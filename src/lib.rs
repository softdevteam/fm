#![doc = include_str!("../README.md")]
#![allow(clippy::upper_case_acronyms)]

use std::{
    collections::hash_map::{Entry, HashMap},
    default::Default,
    error::Error,
    fmt,
};

use regex::Regex;

const ERROR_CONTEXT: usize = 3;
const LINE_ANCHOR_WILDCARD: &str = "...";
const GROUP_ANCHOR_WILDCARD: &str = "..~";
const INTRALINE_WILDCARD: &str = "...";
const ERROR_MARKER: &str = ">>";

#[derive(Debug)]
struct FMOptions {
    output_formatter: OutputFormatter,
    name_matchers: Vec<(Regex, Regex, bool)>,
    distinct_name_matching: bool,
    trim_whitespace: bool,
}

impl Default for FMOptions {
    fn default() -> Self {
        FMOptions {
            output_formatter: OutputFormatter::InputThenSummary,
            name_matchers: Vec::new(),
            distinct_name_matching: false,
            trim_whitespace: true,
        }
    }
}

/// How should an [FMatchError] format itself? Where:
///
///   * `Input` means the literal text passed to fmt.
///   * `Summary` is the subset of pattern and text where an error was detected.
///
/// For example a summary may look as follows (where `...` means "text above/below was elided"):
///
/// ```text
/// Pattern (error at line 5):
///    ...
///    |2
///    |3
///    |4
/// >> |5
///    |6
///    |7
///    |8
///    ...
///
/// Literal text (error at line 5):
///    ...
///    |2
///    |3
///    |4
/// >> |6
///    |7
///    |8
///    |9
///    ...
/// ```
#[derive(Copy, Clone, Debug)]
pub enum OutputFormatter {
    /// Input text followed by a summary.
    InputThenSummary,
    /// Input text only.
    InputOnly,
    /// Summary only.
    SummaryOnly,
}

/// Build up a `FMatcher` allowing the setting of options.
///
/// ```rust
/// use {fm::FMBuilder, regex::Regex};
///
/// let ptn_re = Regex::new(r"\$.+?\b").unwrap();
/// let text_re = Regex::new(r".+?\b").unwrap();
/// let matcher = FMBuilder::new("$1 $1")
///                         .unwrap()
///                         .name_matcher(ptn_re, text_re)
///                         .build()
///                         .unwrap();
/// assert!(matcher.matches("a a").is_ok());
/// assert!(matcher.matches("a b").is_err());
/// ```
#[derive(Debug)]
pub struct FMBuilder<'a> {
    ptn: &'a str,
    options: FMOptions,
}

impl<'a> FMBuilder<'a> {
    /// Create a new `FMBuilder` with default options.
    pub fn new(ptn: &'a str) -> Result<Self, Box<dyn Error>> {
        Ok(FMBuilder {
            ptn,
            options: FMOptions::default(),
        })
    }

    pub fn output_formatter(mut self, output_formatter: OutputFormatter) -> Self {
        self.options.output_formatter = output_formatter;
        self
    }

    /// Add a name matcher `(ptn_re, text_re)`. Name matchers allow you to ensure that different
    /// parts of the text match without specifying precisely what they match. For example, if you
    /// have output where you want to ensure that two locations always match the same name, but the
    /// name is non-deterministic you can allow the use of `$` wildcards in your pattern:
    ///
    /// ```rust
    /// use {fm::FMBuilder, regex::Regex};
    ///
    /// let ptn_re = Regex::new(r"\$[1]+?\b").unwrap();
    /// let text_re = Regex::new(r"[a-b]+?\b").unwrap();
    /// let matcher = FMBuilder::new("$1 b $1")
    ///                         .unwrap()
    ///                         .name_matcher(ptn_re, text_re)
    ///                         .build()
    ///                         .unwrap();
    /// assert!(matcher.matches("a b a").is_ok());
    /// assert!(matcher.matches("a b b").is_err());
    /// ```
    ///
    /// Note that if a line in the pattern uses name matching, it can *only* use the wildcard
    /// operator at the end of the line (so, for the above name matcher, `$1...` is allowed but
    /// `...$1` or `...$1...` is not allowed). Invalid combinations of wildcards and name matching
    /// are caught when a pattern is built.
    ///
    /// Multiple name matchers are allowed: they are matched in the order they were added to
    /// `FMBuilder`.
    pub fn name_matcher(mut self, ptn_re: Regex, text_re: Regex) -> Self {
        self.options.name_matchers.push((ptn_re, text_re, false));
        self
    }

    /// Add a name matcher that has the same semantics as a name matcher added with
    /// [Self::name_matcher] *but* which ignores the contents of the matched text. This can be
    /// used to ensure that the text follows a certain "shape" but without worrying about either a)
    /// the concrete value b) having to generate fresh names for each such instance. This can be
    /// combined with "normal" name matching, as in the following example:
    ///
    /// ```rust
    /// use {fm::FMBuilder, regex::Regex};
    ///
    /// let ptn_re = Regex::new(r"\$[1]+?\b").unwrap();
    /// let ptn_ignore_re = Regex::new(r"\$_\b").unwrap();
    /// let text_re = Regex::new(r"[a-b]+?\b").unwrap();
    /// let matcher = FMBuilder::new("$1 $_ $1 $_")
    ///                         .unwrap()
    ///                         .name_matcher(ptn_re, text_re.clone())
    ///                         .name_matcher_ignore(ptn_ignore_re, text_re)
    ///                         .build()
    ///                         .unwrap();
    /// assert!(matcher.matches("a b a a").is_ok());
    /// assert!(matcher.matches("a b b a").is_err());
    /// ```
    ///
    /// As this shows, once `$1` has matched "a", all further instances of `$1` must also match
    /// "a", but `_` can match different values at different points. This is true even if distinct
    /// name matching (see [Self::distinct_name_matching] is enabled.
    pub fn name_matcher_ignore(mut self, ptn_re: Regex, text_re: Regex) -> Self {
        self.options.name_matchers.push((ptn_re, text_re, true));
        self
    }

    /// If `yes`, then different names cannot match the same text value. For example if `$1` binds
    /// to `a` then `$2` will refuse to match against `a` (though `$1` will continue to match
    /// against only `a`). Note that ignorable name matches (see [Self::name_matcher_ignore]) are
    /// never subject to distinct name matching. Defaults to `false`.
    pub fn distinct_name_matching(mut self, yes: bool) -> Self {
        self.options.distinct_name_matching = yes;
        self
    }

    /// If `yes`, then:
    ///   1. Blank lines at the start/end of the pattern and text are ignored.
    ///   2. Leading/trailing whitespace is ignored on each line of the pattern and text.
    /// Defaults to "yes".
    pub fn trim_whitespace(mut self, yes: bool) -> Self {
        self.options.trim_whitespace = yes;
        self
    }

    /// Turn this `FMBuilder` into a `FMatcher`.
    pub fn build(self) -> Result<FMatcher<'a>, Box<dyn Error>> {
        self.validate()?;
        let (ptn_lines, ptn_lines_off) = line_trimmer(self.options.trim_whitespace, self.ptn);
        Ok(FMatcher {
            orig_ptn: self.ptn,
            ptn_lines,
            ptn_lines_off,
            options: self.options,
        })
    }

    fn validate(&self) -> Result<(), Box<dyn Error>> {
        let lines = self.ptn.lines().map(|x| x.trim()).collect::<Vec<_>>();

        for i in 0..lines.len() {
            if i < lines.len() - 1
                && (lines[i] == LINE_ANCHOR_WILDCARD || lines[i] == GROUP_ANCHOR_WILDCARD)
                && (lines[i + 1] == LINE_ANCHOR_WILDCARD || lines[i + 1] == GROUP_ANCHOR_WILDCARD)
            {
                return Err(Box::<dyn Error>::from(format!(
                    "Can't have two consecutive interline wildcards lines at lines {} and {}.",
                    i + 1,
                    i + 2
                )));
            }
        }

        for (ref ptn_re, _, _) in &self.options.name_matchers {
            for (i, l) in lines.iter().enumerate() {
                if l.starts_with(INTRALINE_WILDCARD) && ptn_re.is_match(l) {
                    return Err(Box::<dyn Error>::from(format!(
                        "Can't mix name matching with start-of-line wildcards at line {}.",
                        i + 1
                    )));
                }
            }
        }
        Ok(())
    }
}

/// The fuzzy matcher.
#[derive(Debug)]
pub struct FMatcher<'a> {
    orig_ptn: &'a str,
    ptn_lines: Vec<&'a str>,
    ptn_lines_off: usize,
    options: FMOptions,
}

impl<'a> FMatcher<'a> {
    /// A convenience method that automatically builds a pattern using `FMBuilder` defaults.
    pub fn new(ptn: &'a str) -> Result<FMatcher, Box<dyn Error>> {
        FMBuilder::new(ptn)?.build()
    }

    /// Does this fuzzy matcher match `text`?
    pub fn matches(&self, text: &str) -> Result<(), FMatchError> {
        let mut names = HashMap::new();
        let mut ptn_i = 0;
        let (text_lines, text_lines_off) = line_trimmer(self.options.trim_whitespace, text);
        let mut text_i = 0;
        loop {
            match (self.ptn_lines.get(ptn_i), text_lines.get(text_i)) {
                (Some(x), Some(y)) => {
                    if x.trim() == LINE_ANCHOR_WILDCARD {
                        let text_i_orig = text_i;
                        ptn_i += 1;
                        match self.ptn_lines.get(ptn_i) {
                            Some(x) => {
                                let mut succ = false;
                                while let Some(y) = text_lines.get(text_i) {
                                    if self.match_line(&mut names, x, y) {
                                        succ = true;
                                        break;
                                    }
                                    text_i += 1;
                                }
                                if !succ {
                                    return Err(self.fmatch_err(
                                        ptn_i,
                                        text,
                                        text_lines_off,
                                        text_i_orig,
                                        names,
                                    ));
                                }
                            }
                            None => return Ok(()),
                        }
                    } else if x.trim() == GROUP_ANCHOR_WILDCARD {
                        ptn_i += 1;
                        // If the interline wildcard is the last part of the pattern, then we
                        // implicitly match any remaining text: i.e. we're done!
                        if ptn_i == self.ptn_lines.len() {
                            return Ok(());
                        }
                        // We now have to perform (bounded) backtracking
                        let ptn_i_orig = ptn_i;
                        let text_i_orig = text_i;
                        let mut text_i_st = text_i;
                        let names_orig = names;
                        names = names_orig.clone();
                        loop {
                            match (self.ptn_lines.get(ptn_i), text_lines.get(text_i)) {
                                (None, None) => return Ok(()),
                                (None, Some(_)) => {
                                    return Err(self.fmatch_err(
                                        ptn_i_orig,
                                        text,
                                        text_lines_off,
                                        text_i_orig,
                                        names,
                                    ));
                                }
                                (Some(x), _)
                                    if *x == GROUP_ANCHOR_WILDCARD
                                        || *x == LINE_ANCHOR_WILDCARD =>
                                {
                                    // We've matched everything successfully
                                    break;
                                }
                                (Some(_), None) => {
                                    return Err(self.fmatch_err(
                                        ptn_i_orig,
                                        text,
                                        text_lines_off,
                                        text_i_orig,
                                        names,
                                    ));
                                }
                                (Some(x), Some(y)) => {
                                    if self.match_line(&mut names, x, y) {
                                        ptn_i += 1;
                                        text_i += 1;
                                    } else {
                                        // We failed to match, so we need to reset the
                                        // pattern, but advance the text.
                                        ptn_i = ptn_i_orig;
                                        text_i_st += 1;
                                        text_i = text_i_st;
                                        names = names_orig.clone();
                                    }
                                }
                            }
                        }
                    } else if self.match_line(&mut names, x, y) {
                        ptn_i += 1;
                        text_i += 1;
                    } else {
                        return Err(self.fmatch_err(ptn_i, text, text_lines_off, text_i, names));
                    }
                }
                (None, None) => return Ok(()),
                (Some(x), None) => {
                    if let LINE_ANCHOR_WILDCARD | GROUP_ANCHOR_WILDCARD = x.trim() {
                        ptn_i += 1;
                        // If the interline wildcard is the last line in the pattern, we're done.
                        // If it isn't, then the pattern hasn't matched: rather than explicitly
                        // throw an error in this clause, we let the next iteration of the outer
                        // while loop catch this case.
                        if ptn_i == self.ptn_lines.len() {
                            return Ok(());
                        }
                    } else {
                        return Err(self.fmatch_err(ptn_i, text, text_lines_off, text_i, names));
                    }
                }
                (None, Some(_)) => {
                    return Err(self.fmatch_err(ptn_i, text, text_lines_off, text_i, names));
                }
            }
        }
    }

    /// Try matching `ptn` against `text`. If, and only if, the match is successful, `names` will
    /// be updated with matched names.
    fn match_line<'b>(
        &self,
        names: &mut HashMap<&'a str, &'b str>,
        ptn: &'a str,
        text: &'b str,
    ) -> bool {
        let sww = ptn.starts_with(INTRALINE_WILDCARD);
        let eww = ptn.ends_with(INTRALINE_WILDCARD);
        if sww && eww {
            text.contains(&ptn[INTRALINE_WILDCARD.len()..ptn.len() - INTRALINE_WILDCARD.len()])
        } else if sww {
            text.ends_with(&ptn[INTRALINE_WILDCARD.len()..])
        } else if self.options.name_matchers.is_empty() {
            if eww {
                text.starts_with(&ptn[..ptn.len() - INTRALINE_WILDCARD.len()])
            } else {
                ptn == text
            }
        } else {
            let mut new_names = HashMap::new();
            let mut ptn_i = 0;
            let mut text_i = 0;
            'a: while ptn_i < ptn.len()
                && text_i < text.len()
                && &ptn[ptn_i..] != INTRALINE_WILDCARD
            {
                for (ref ptn_re, ref text_re, ignore) in &self.options.name_matchers {
                    if let Some(ptnm) = ptn_re.find(&ptn[ptn_i..]) {
                        if ptnm.start() != 0 {
                            continue;
                        }
                        match text_re.find(&text[text_i..]) {
                            Some(textm) if textm.start() == 0 => {
                                let key = ptnm.as_str();
                                let val = textm.as_str();
                                if val.is_empty() {
                                    panic!("Text pattern matched the empty string.");
                                }
                                if !ignore {
                                    if self.options.distinct_name_matching {
                                        for (x, y) in names.iter().chain(new_names.iter()) {
                                            if *x != key && *y == val {
                                                return false;
                                            }
                                        }
                                    }
                                    match names.entry(key) {
                                        Entry::Occupied(e) => {
                                            if *e.get() != val {
                                                return false;
                                            }
                                        }
                                        Entry::Vacant(_) => match new_names.entry(key) {
                                            Entry::Occupied(e) => {
                                                if *e.get() != val {
                                                    return false;
                                                }
                                            }
                                            Entry::Vacant(e) => {
                                                e.insert(val);
                                            }
                                        },
                                    }
                                }
                                ptn_i += ptnm.len();
                                text_i += textm.len();
                                continue 'a;
                            }
                            Some(_) | None => return false,
                        }
                    }
                }
                if ptn[ptn_i..ptn_i + 1] != text[text_i..text_i + 1] {
                    return false;
                }
                ptn_i += 1;
                text_i += 1;
            }
            if (ptn_i == ptn.len() && text_i == text.len()) || &ptn[ptn_i..] == INTRALINE_WILDCARD {
                names.extend(new_names);
                true
            } else {
                false
            }
        }
    }

    fn fmatch_err(
        &self,
        ptn_i: usize,
        text: &str,
        text_lines_off: usize,
        text_i: usize,
        names: HashMap<&'a str, &'a str>,
    ) -> FMatchError {
        FMatchError {
            output_formatter: self.options.output_formatter,
            ptn: self.orig_ptn.to_owned(),
            text: text.to_owned(),
            ptn_line_off: self.ptn_lines_off + ptn_i,
            text_line_off: text_lines_off + text_i,
            names: names
                .iter()
                .map(|(x, y)| (x.to_string(), y.to_string()))
                .collect::<HashMap<_, _>>(),
        }
    }
}

/// An error indicating a failed match.
/// The pattern and text are copied in so that the error isn't tied to their lifetimes.
pub struct FMatchError {
    output_formatter: OutputFormatter,
    ptn: String,
    text: String,
    ptn_line_off: usize,
    text_line_off: usize,
    names: HashMap<String, String>,
}

impl FMatchError {
    pub fn ptn_line_off(&self) -> usize {
        self.ptn_line_off
    }

    pub fn text_line_off(&self) -> usize {
        self.text_line_off
    }
}

impl fmt::Display for FMatchError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.output_formatter {
            OutputFormatter::SummaryOnly => fmt_summary(
                f,
                &self.ptn,
                self.ptn_line_off,
                &self.text,
                self.text_line_off,
                &self.names,
            ),
            OutputFormatter::InputThenSummary => {
                fmt_raw(f, &self.text)?;
                writeln!(f)?;
                fmt_summary(
                    f,
                    &self.ptn,
                    self.ptn_line_off,
                    &self.text,
                    self.text_line_off,
                    &self.names,
                )
            }
            OutputFormatter::InputOnly => fmt_raw(f, &self.text),
        }
    }
}

fn fmt_raw(f: &mut fmt::Formatter, text: &str) -> fmt::Result {
    let err_mk_chars = ERROR_MARKER.chars().count() + ' '.len_utf8();
    let lhs = &format!("\n{}|", " ".repeat(err_mk_chars));
    writeln!(
        f,
        "Literal text:{}{}",
        lhs,
        text.split('\n').collect::<Vec<_>>().join(lhs)
    )
}

fn fmt_summary(
    f: &mut fmt::Formatter,
    ptn: &str,
    ptn_line_off: usize,
    text: &str,
    text_line_off: usize,
    names: &HashMap<String, String>,
) -> fmt::Result {
    // Figure out how many characters are required for the LHS margin.
    let err_mk_chars = ERROR_MARKER.chars().count() + ' '.len_utf8();

    let display_lines = |f: &mut fmt::Formatter, s: &str, mark_line: usize| -> fmt::Result {
        let mut i = 1;
        if mark_line.checked_sub(ERROR_CONTEXT + 2).is_some() {
            writeln!(f, "{}...", " ".repeat(err_mk_chars))?;
        }
        for line in s.lines() {
            if let Some(j) = mark_line.checked_sub(ERROR_CONTEXT) {
                if i < j {
                    i += 1;
                    continue;
                }
            }
            if mark_line == i {
                write!(f, "{} ", ERROR_MARKER)?;
            } else {
                write!(f, "{}", " ".repeat(err_mk_chars))?;
            }
            if line.is_empty() {
                writeln!(f, "|")?;
            } else {
                writeln!(f, "|{}", line)?;
            }
            i += 1;
            if let Some(j) = mark_line.checked_add(ERROR_CONTEXT) {
                if i > j {
                    break;
                }
            }
        }
        if mark_line == i {
            writeln!(f, "{}", ERROR_MARKER)?;
        } else if let Some(j) = mark_line.checked_add(ERROR_CONTEXT) {
            if i > j {
                writeln!(f, "{}...", " ".repeat(err_mk_chars))?;
            }
        }
        Ok(())
    };

    writeln!(f, "Pattern (error at line {}):", ptn_line_off)?;
    display_lines(f, ptn, ptn_line_off)?;
    if !names.is_empty() {
        let mut names = names.iter().collect::<Vec<(_, _)>>();
        names.sort();
        let names = names
            .iter()
            .map(|(k, v)| format!("{k}: {v}"))
            .collect::<Vec<_>>()
            .join("\n  ");
        writeln!(f, "\nNames at point of failure:\n  {names}")?;
    }
    writeln!(f, "\nText (error at line {}):", text_line_off)?;
    display_lines(f, text, text_line_off)
}

/// A short error message. We don't reuse the longer message from `Display` as a Rust panic
/// uses `Debug` and doesn't interpret formatting characters when printing the panic message.
impl fmt::Debug for FMatchError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Failed to match at line {}", self.text_line_off)
    }
}

impl Error for FMatchError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// Return `s` split into lines and the number of leading lines (+1 to allow for human-readable
/// errors!) skipped.
///
/// If `trim` is set to true:
///   1. Leading/trailing blank space within lines is trimmed.
///   2. Leading/trailing blank lines (including blank space) are trimmed.
fn line_trimmer<'a>(trim: bool, s: &'a str) -> (Vec<&'a str>, usize) {
    let mut lines = s.lines().collect::<Vec<_>>();
    if !trim {
        return (lines, 1);
    }
    let mut st = 0;
    while st < lines.len() && lines[st].trim().is_empty() {
        st += 1;
    }
    let mut en = lines.len();
    while en > 0 && lines[en - 1].trim().is_empty() {
        en -= 1;
    }
    if en < st {
        en = st;
    }
    (
        lines.drain(st..en).map(|x| x.trim()).collect::<Vec<_>>(),
        st + 1,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::proptest;

    #[test]
    fn line_trimming() {
        assert_eq!(line_trimmer(true, ""), (vec![], 1));
        assert_eq!(line_trimmer(true, "\n"), (vec![], 2));
        assert_eq!(line_trimmer(true, "\na"), (vec!["a"], 2));
        assert_eq!(line_trimmer(true, "\na\n"), (vec!["a"], 2));
        assert_eq!(line_trimmer(true, "\na\nb\n"), (vec!["a", "b"], 2));
        assert_eq!(line_trimmer(true, "\n a\nb \n"), (vec!["a", "b"], 2));
        assert_eq!(line_trimmer(true, "\n a\n\nb \n"), (vec!["a", "", "b"], 2));
    }

    #[test]
    fn defaults() {
        fn helper(ptn: &str, text: &str) -> bool {
            FMatcher::new(ptn).unwrap().matches(text).is_ok()
        }
        assert!(helper("", ""));
        assert!(helper("\n", ""));
        assert!(helper("", "\n"));
        assert!(helper("a", "a"));
        assert!(!helper("a", "ab"));
        assert!(helper("...", ""));
        assert!(helper("...", "a"));
        assert!(helper("...", "a\nb"));
        assert!(helper("...\na", "a"));
        assert!(helper("...\na\n...", "a"));
        assert!(helper("a\n...", "a"));
        assert!(helper("a\n...\nd", "a\nd"));
        assert!(helper("a\n...\nd", "a\nb\nc\nd"));
        assert!(!helper("a\n...\nd", "a\nb\nc"));
        assert!(helper("a\n...\nc\n...\ne", "a\nb\nc\nd\ne"));
        assert!(helper("a\n...\n...b", "a\nb"));
        assert!(helper("a\n...\nb...", "a\nb"));
        assert!(helper("a\n...\nb...", "a\nbc"));
        assert!(helper("a\nb...", "a\nbc"));
        assert!(!helper("a\nb...", "a\nb\nc"));
        assert!(helper("a\n...b...", "a\nb"));
        assert!(helper("a\n...b...", "a\nxbz"));
        assert!(helper("a\n...b...", "a\nbz"));
        assert!(helper("a\n...b...", "a\nxb"));
        assert!(!helper("a\n...b...", "a\nxb\nc"));
        assert!(!helper("a", "a\nb"));
        assert!(!helper("a\nb", "a"));
        assert!(!helper("a\n...\nb", "a"));
        assert!(helper("a\n", "a\n"));
        assert!(helper("a\n", "a"));
        assert!(helper("a", "a\n"));
        assert!(helper("a\n\n", "a\n\n"));
        assert!(helper("a\n\n", "a"));
        assert!(helper("a", "a\n\n"));
        assert!(!helper("a\n\nb", "a\n"));
        assert!(!helper("a\n", "a\n\nb"));
    }

    #[test]
    fn groupings() {
        fn helper(ptn: &str, text: &str) -> bool {
            FMatcher::new(ptn).unwrap().matches(text).is_ok()
        }
        assert!(helper("a\n..~\nc\n", "a\nb\nc"));
        assert!(helper("a\n..~\nc\n", "a\nc"));
        assert!(helper("a\n..~\nc\nd\n", "a\nc\nd"));
        assert!(helper("a\n..~\nc\nd\n", "a\nb\nc\nd"));
        assert!(!helper("a\n..~\nc\nd\ne", "a\nb\nc\nd"));
        assert!(!helper("a\n..~\nc\nd\n", "a\nb\nc\ne"));
        assert!(!helper("a\n..~\nc\nd\n", "a\nc\ne\nc\ne"));
        assert!(!helper("..~\nc", ""));
        assert!(!helper("..~\nc", "c\nd"));
        assert!(helper("a\n..~\nc\nd\n", "a\nc\ne\nc\nd"));
        assert!(helper("a\n..~\nc\nd\ne", "a\nc\ne\nc\nd\ne"));
        assert!(helper("a\n..~\nc\n..~", "a\nb\nc"));
        assert!(helper("a\n..~\nc\n...", "a\nb\nc"));
        assert!(helper("a\n..~\nc\n..~\nd", "a\nb\nc\nd"));
        assert!(!helper("a\n..~\nc\n..~\nd", "a\nb\nc\ne"));
        assert!(helper("a\n..~\nc\n...\nd", "a\nb\nc\nd"));
        assert!(helper("a\n..~\nc\n..~\nd", "a\nb\nc\ne\nf\nd"));
        assert!(helper("a\n..~\nc\nd\n..~\nd", "a\nb\nc\nd\nd"));
        assert!(!helper("a\n..~\nc\nd\n..~\nd", "a\nb\nc\nd"));
        assert!(!helper("a\n..~\nc\nd\n..~\nd", "a\nb\nc\nd\nd\nd"));
        assert!(helper("..~\na\n..~\nb", "a\nb"));
        assert!(!helper("..~\na\n..~\nb", "a"));
        assert!(!helper("..~\na\n..~\nb", "a\nb\nc"));
        assert!(helper("..~\na\n..~", "a\nb"));
    }

    #[test]
    fn dont_trim_whitespace() {
        fn helper(ptn: &str, text: &str) -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .trim_whitespace(false)
                .build()
                .unwrap()
                .matches(text)
                .is_ok()
        }
        assert!(helper("", ""));
        assert!(!helper("\n", ""));
        assert!(!helper("", "\n"));
        assert!(helper("a\n", "a\n"));
        assert!(helper("a\n", "a"));
        assert!(helper("a", "a\n"));
        assert!(helper("a\n\n", "a\n\n"));
        assert!(!helper("a\n\n", "a"));
        assert!(!helper("a", "a\n\n"));
        assert!(!helper("a\n\nb", "a\n"));
        assert!(!helper("a\n", "a\n\nb"));

        assert!(helper("a\na", "a\na"));

        assert!(helper("a\n a", "a\n a"));
        assert!(!helper("a\n a", "a\na"));
        assert!(!helper("a\na", "a\n a"));

        assert!(helper("a\na ", "a\na "));
        assert!(!helper("a\na", "a\na "));
        assert!(!helper("a\na ", "a\na"));
    }

    #[test]
    fn name_matcher() {
        let nameptn_re = Regex::new(r"\$.+?\b").unwrap();
        let name_re = Regex::new(r".+?\b").unwrap();
        let helper = |ptn: &str, text: &str| -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .name_matcher(nameptn_re.clone(), name_re.clone())
                .build()
                .unwrap()
                .matches(text)
                .is_ok()
        };
        assert!(helper("", ""));
        assert!(helper("a", "a"));
        assert!(!helper("a", "ab"));
        assert!(helper("...", ""));
        assert!(helper("...", "a"));
        assert!(helper("......", "a"));
        assert!(!helper("......", ""));
        assert!(helper("...", "a\nb"));
        assert!(!helper("......", "a\nb"));
        assert!(helper("...\na", "a"));
        assert!(helper("...\na\n...", "a"));
        assert!(helper("a\n...", "a"));
        assert!(helper("a\n...\nd", "a\nd"));
        assert!(helper("a\n...\nd", "a\nb\nc\nd"));
        assert!(!helper("a\n...\nd", "a\nb\nc"));
        assert!(helper("a\n...\nc\n...\ne", "a\nb\nc\nd\ne"));
        assert!(helper("a\n...\n...b", "a\nb"));
        assert!(helper("a\n...\nb...", "a\nb"));
        assert!(helper("a\n...\nb...", "a\nbc"));
        assert!(helper("a\nb...", "a\nbc"));
        assert!(!helper("a\nb...", "a\nb\nc"));
        assert!(helper("a\n...b...", "a\nb"));
        assert!(helper("a\n...b...", "a\nxbz"));
        assert!(helper("a\n...b...", "a\nbz"));
        assert!(helper("a\n...b...", "a\nxb"));
        assert!(!helper("a\n...b...", "a\nxb\nc"));

        assert!(!helper("$1", ""));
        assert!(helper("$1", "a"));
        assert!(helper("$1, $1", "a, a"));
        assert!(!helper("$1, $1", "a, b"));
        assert!(helper("$1, a, $1", "a, a, a"));
        assert!(!helper("$1, a, $1", "a, b, a"));
        assert!(!helper("$1, a, $1", "a, a, b"));
        assert!(helper("$1, $1, a", "a, a, a"));
        assert!(!helper("$1, $1, a", "a, a, b"));
        assert!(!helper("$1, $1, a", "a, b, a"));
        assert!(helper("$1 $2\n...\n$3 $2", "a X\nb Y\nc X"));
        assert!(!helper("ab$a", "a"));
        assert!(helper("$1\n$1...", "a\na b c"));
        assert!(!helper("$1\n$1...", "a\nb b c"));
        assert!(helper("$1\n$1...", "a\na b c"));
        assert!(helper("$1\n$1 b...", "a\na b c"));
        assert!(helper("$1\n$1 b c...", "a\na b c"));
        assert!(!helper("$1\n$1 b c...\n$1", "a\na b c"));
        assert!(!helper("$1\n$1 b c...\n$1", "a\na b c\na\nb"));
    }

    #[test]
    fn multiple_name_matchers() {
        let nameptn1_re = Regex::new(r"\$.+?\b").unwrap();
        let nameptn2_re = Regex::new(r"\&.+?\b").unwrap();
        let name_re = Regex::new(r".+?\b").unwrap();
        let helper = |ptn: &str, text: &str| -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .name_matcher(nameptn1_re.clone(), name_re.clone())
                .name_matcher(nameptn2_re.clone(), name_re.clone())
                .build()
                .unwrap()
                .matches(text)
                .is_ok()
        };

        assert!(!helper("$1", ""));
        assert!(helper("$1", "a"));
        assert!(helper("$1, $1", "a, a"));
        assert!(!helper("$1, $1", "a, b"));
        assert!(helper("$1, a, $1", "a, a, a"));
        assert!(!helper("$1, a, $1", "a, b, a"));
        assert!(!helper("$1, a, $1", "a, a, b"));
        assert!(helper("$1, $1, a", "a, a, a"));
        assert!(!helper("$1, $1, a", "a, a, b"));
        assert!(!helper("$1, $1, a", "a, b, a"));
        assert!(helper("$1 $2\n...\n$3 $2", "a X\nb Y\nc X"));
        assert!(!helper("ab$a", "a"));
        assert!(helper("$1\n$1...", "a\na b c"));
        assert!(!helper("$1\n$1...", "a\nb b c"));
        assert!(helper("$1\n$1...", "a\na b c"));
        assert!(helper("$1\n$1 b...", "a\na b c"));
        assert!(helper("$1\n$1 b c...", "a\na b c"));
        assert!(!helper("$1\n$1 b c...\n$1", "a\na b c"));
        assert!(!helper("$1\n$1 b c...\n$1", "a\na b c\na\nb"));

        assert!(!helper("&1", ""));
        assert!(helper("&1", "a"));
        assert!(helper("&1, &1", "a, a"));
        assert!(!helper("&1, &1", "a, b"));
        assert!(helper("&1, a, &1", "a, a, a"));
        assert!(!helper("&1, a, &1", "a, b, a"));
        assert!(!helper("&1, a, &1", "a, a, b"));
        assert!(helper("&1, &1, a", "a, a, a"));
        assert!(!helper("&1, &1, a", "a, a, b"));
        assert!(!helper("&1, &1, a", "a, b, a"));
        assert!(helper("&1 &2\n...\n&3 &2", "a X\nb Y\nc X"));
        assert!(!helper("ab&a", "a"));
        assert!(helper("&1\n&1...", "a\na b c"));
        assert!(!helper("&1\n&1...", "a\nb b c"));
        assert!(helper("&1\n&1...", "a\na b c"));
        assert!(helper("&1\n&1 b...", "a\na b c"));
        assert!(helper("&1\n&1 b c...", "a\na b c"));
        assert!(!helper("&1\n&1 b c...\n&1", "a\na b c"));
        assert!(!helper("&1\n&1 b c...\n&1", "a\na b c\na\nb"));

        assert!(helper("$1 &1", "a a"));
        assert!(helper("$1 &1", "a b"));
        assert!(helper("&1 $1 &1", "a b a"));
        assert!(!helper("&1 $1 &1", "a b b"));
        assert!(helper("&1 $1 &1", "a a a"));
        assert!(helper("$1 &1 $1", "a b a"));
        assert!(helper("$1 &1 &1", "a b b"));
        assert!(!helper("$1 &1 &1", "a b a"));
        assert!(helper("$1 &2\n...\n$3 &2", "a X\nb Y\nc X"));
        assert!(helper("$1 &1\n$1 &1...", "a b\na b c d"));
        assert!(helper("$1 &1\n$1 &1...", "a b\na b"));
        assert!(!helper("$1 &1\n$1 &1...", "a b\na a c d"));
        assert!(!helper("$1 &1\n$1 &1 c...\n$1", "a b\na b c"));
        assert!(!helper("$1 &1\n$1 &1 c...\n$1", "a b\na b c\na\nb"));

        assert!(helper("..~\n$1, $1\n..~", "a, a"));
        assert!(helper("..~\n$1\n$1\n..~", "a\na"));
        assert!(helper("..~\n$1\n$1\n..~", "a\nb\nb"));
        assert!(helper("..~\n$1\n$1\n..~", "a\nb\na\na"));
        assert!(helper("..~\n$1\n$1\n..~", "a\nb\na\nc\nc"));
        assert!(!helper("..~\n$1\n$1\n..~", "a\nb\na\nb"));
    }

    #[test]
    fn name_matcher_ignore() {
        let nameptn_ignore_re = Regex::new(r"\$_\b").unwrap();
        let nameptn_normal_re = Regex::new(r"\$[^_]+?\b").unwrap();
        let name_re = Regex::new(r"[a-z]+?\b").unwrap();
        let helper = |ptn: &str, text: &str| -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .name_matcher_ignore(nameptn_ignore_re.clone(), name_re.clone())
                .name_matcher(nameptn_normal_re.clone(), name_re.clone())
                .build()
                .unwrap()
                .matches(text)
                .is_ok()
        };

        assert!(helper("$1, $1", "a, a"));
        assert!(!helper("$1, $1", "a, b"));
        assert!(helper("$_, $_", "a, b"));
        assert!(!helper("$_, $_", "1, 2"));
        assert!(helper("$1, $_, $1", "a, b, a"));
        assert!(helper("$1, $_, $1", "a, a, a"));
    }

    #[test]
    fn name_matcher_ignore_distinct_matching() {
        let nameptn_ignore_re = Regex::new(r"\$_\b").unwrap();
        let nameptn_normal_re = Regex::new(r"\$[^_]+?\b").unwrap();
        let name_re = Regex::new(r"[a-z]+?\b").unwrap();
        let helper = |ptn: &str, text: &str| -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .distinct_name_matching(true)
                .name_matcher_ignore(nameptn_ignore_re.clone(), name_re.clone())
                .name_matcher(nameptn_normal_re.clone(), name_re.clone())
                .build()
                .unwrap()
                .matches(text)
                .is_ok()
        };

        assert!(helper("$1 $1 $2 $2", "a a b b"));
        assert!(!helper("$1 $1 $2 $2", "a a a a"));
        assert!(helper("$1 $1 $_ $_", "a a b b"));
        assert!(helper("$1 $1 $_ $_", "a a a a"));
    }

    #[test]
    fn error_lines() {
        let ptn_re = Regex::new("\\$.+?\\b").unwrap();
        let text_re = Regex::new(".+?\\b").unwrap();
        let helper = |ptn: &str, text: &str| -> (usize, usize) {
            let err = FMBuilder::new(ptn)
                .unwrap()
                .name_matcher(ptn_re.clone(), text_re.clone())
                .build()
                .unwrap()
                .matches(text)
                .unwrap_err();
            (err.ptn_line_off(), err.text_line_off())
        };

        assert_eq!(helper("a\n...\nd", "a\nb\nc"), (3, 2));
        assert_eq!(helper("a\nb...", "a\nb\nc"), (3, 3));
        assert_eq!(helper("a\n...b...", "a\nxb\nc"), (3, 3));

        assert_eq!(helper("a\n\nb", "a\n"), (2, 2));
        assert_eq!(helper("a\n", "a\n\nb"), (2, 2));

        assert_eq!(helper("$1", ""), (1, 1));
        assert_eq!(helper("$1, $1", "a, b"), (1, 1));
        assert_eq!(helper("$1, a, $1", "a, b, a"), (1, 1));
        assert_eq!(helper("$1, a, $1", "a, a, b"), (1, 1));
        assert_eq!(helper("$1, $1, a", "a, a, b"), (1, 1));
        assert_eq!(helper("$1, $1, a", "a, b, a"), (1, 1));

        assert_eq!(helper("$1", ""), (1, 1));
        assert_eq!(helper("$1\n$1", "a\nb"), (2, 2));
        assert_eq!(helper("$1\na\n$1", "a\nb\na"), (2, 2));
        assert_eq!(helper("$1\na\n$1", "a\na\nb"), (3, 3));
        assert_eq!(helper("$1\n$1\na", "a\na\nb"), (3, 3));
        assert_eq!(helper("$1\n$1\na", "a\nb\na"), (2, 2));

        assert_eq!(helper("...\nb\nc\nd\n", "a\nb\nc\n0\ne"), (4, 4));
        assert_eq!(helper("...\nc\nd\n", "a\nb\nc\n0\ne"), (3, 4));
        assert_eq!(helper("...\nd\n", "a\nb\nc\n0\ne"), (2, 1));

        assert_eq!(helper("a\n..~\nc\nd\ne", "a\nb\nc\nd"), (3, 2));
        assert_eq!(helper("a\n..~\nc\nd", "a\nb\nc\ne"), (3, 2));
        assert_eq!(helper("a\n..~\nc\nd", "a\nc\ne\nc\ne"), (3, 2));
        assert_eq!(helper("a\n..~\nc\nd\n...\nf", "a\ne\nf\nc\nd\ne"), (6, 6));
    }

    #[test]
    #[should_panic]
    fn empty_name_pattern() {
        let ptn_re = Regex::new("").unwrap();
        let text_re = Regex::new(".+?\\b").unwrap();
        FMBuilder::new("$1")
            .unwrap()
            .name_matcher(ptn_re, text_re)
            .build()
            .unwrap()
            .matches("x")
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn empty_text_pattern() {
        let ptn_re = Regex::new("\\$.+?\\b").unwrap();
        let text_re = Regex::new("").unwrap();
        FMBuilder::new("$1")
            .unwrap()
            .name_matcher(ptn_re, text_re)
            .build()
            .unwrap()
            .matches("x")
            .unwrap();
    }

    #[test]
    fn consecutive_wildcards_disallowed() {
        match FMatcher::new("...\n...") {
            Err(e)
                if e.to_string()
                    == "Can't have two consecutive interline wildcards lines at lines 1 and 2." =>
            {
                ()
            }
            x => panic!("{x:?}"),
        }

        match FMatcher::new("..~\n...") {
            Err(e)
                if e.to_string()
                    == "Can't have two consecutive interline wildcards lines at lines 1 and 2." =>
            {
                ()
            }
            x => panic!("{x:?}"),
        }

        match FMatcher::new("a\nb\n...\n..~") {
            Err(e)
                if e.to_string()
                    == "Can't have two consecutive interline wildcards lines at lines 3 and 4." =>
            {
                ()
            }
            x => panic!("{x:?}"),
        }
    }

    #[test]
    fn wildcards_and_names() {
        let ptn_re = Regex::new("\\$.+?\\b").unwrap();
        let text_re = Regex::new("").unwrap();
        let builder = FMBuilder::new("$1\n...$1abc")
            .unwrap()
            .name_matcher(ptn_re, text_re);
        assert_eq!(
            &(*(builder.build().unwrap_err())).to_string(),
            "Can't mix name matching with start-of-line wildcards at line 2."
        );
    }

    #[test]
    fn distinct_names() {
        let nameptn_re = Regex::new(r"\$.+?\b").unwrap();
        let name_re = Regex::new(r".+?\b").unwrap();
        let helper = |ptn: &str, text: &str| -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .name_matcher(nameptn_re.clone(), name_re.clone())
                .distinct_name_matching(true)
                .build()
                .unwrap()
                .matches(text)
                .is_ok()
        };

        assert!(helper("$1 $1", "a a"));
        assert!(!helper("$1 $1", "a b"));
        assert!(!helper("$1 $2", "a a"));
    }

    #[test]
    fn error_display() {
        let ptn_re = Regex::new("\\$.+?\\b").unwrap();
        let text_re = Regex::new(".+?\\b").unwrap();
        let helper = |output_formatter: OutputFormatter, ptn: &str, text: &str| -> String {
            let err = FMBuilder::new(ptn)
                .unwrap()
                .output_formatter(output_formatter)
                .name_matcher(ptn_re.clone(), text_re.clone())
                .build()
                .unwrap()
                .matches(text)
                .unwrap_err();
            format!("{}", err)
        };

        assert_eq!(
            helper(
                OutputFormatter::SummaryOnly,
                "a\nb\nc\nd\n",
                "a\nb\nc\nz\nd\n"
            ),
            "Pattern (error at line 4):
   |a
   |b
   |c
>> |d

Text (error at line 4):
   |a
   |b
   |c
>> |z
   |d
"
        );

        assert_eq!(
            helper(OutputFormatter::SummaryOnly, "a\n", "a\n\nb"),
            "Pattern (error at line 2):
   |a
>>

Text (error at line 2):
   |a
>> |
   |b
"
        );

        assert_eq!(
            helper(OutputFormatter::SummaryOnly, "a\n$1\n$1", "a\nb\nc"),
            "Pattern (error at line 3):
   |a
   |$1
>> |$1

Names at point of failure:
  $1: b

Text (error at line 3):
   |a
   |b
>> |c
"
        );

        let ptn = (1..10)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        let text = (1..11)
            .filter(|x| *x != 5)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(
            helper(OutputFormatter::SummaryOnly, &ptn, &text),
            "Pattern (error at line 5):
   ...
   |2
   |3
   |4
>> |5
   |6
   |7
   |8
   ...

Text (error at line 5):
   ...
   |2
   |3
   |4
>> |6
   |7
   |8
   |9
   ...
"
        );

        assert_eq!(
            helper(OutputFormatter::InputThenSummary, &ptn, &text),
            "Literal text:
   |1
   |2
   |3
   |4
   |6
   |7
   |8
   |9
   |10

Pattern (error at line 5):
   ...
   |2
   |3
   |4
>> |5
   |6
   |7
   |8
   ...

Text (error at line 5):
   ...
   |2
   |3
   |4
>> |6
   |7
   |8
   |9
   ...
"
        );

        assert_eq!(
            helper(OutputFormatter::InputOnly, &ptn, &text),
            "Literal text:
   |1
   |2
   |3
   |4
   |6
   |7
   |8
   |9
   |10
"
        );
    }

    proptest! {
        #[test]
        fn proptest_basic(ptn in "[a-z ]{0,3}", text in "[a-z ]{0,3}") {
            let helper = |ptn: &str, text: &str| -> bool {
                FMBuilder::new(ptn)
                    .unwrap()
                    .build()
                    .unwrap()
                    .matches(text)
                    .is_ok()
            };

            helper(&ptn, &text);
        }
    }

    #[test]
    fn proptest_name_matcher() {
        let ptn_re = Regex::new("\\$[0-9]+?\\b").unwrap();
        let text_re = Regex::new("[a-z]+?\\b").unwrap();
        proptest!(|(ptn in "([a-z ]|\\$[0-9]){0,10}", text in "[a-z ]{0,10}")| {
            let helper = |ptn: &str, text: &str| -> bool {
                FMBuilder::new(ptn)
                    .unwrap()
                    .name_matcher(ptn_re.clone(), text_re.clone())
                    .build()
                    .unwrap()
                    .matches(text)
                    .is_ok()
            };

            helper(&ptn, &text);
        });
    }

    #[test]
    fn proptest_name_matcher_ignore() {
        let ptn_re = Regex::new("\\$[0-9]+?\\b").unwrap();
        let ptn_ignore_re = Regex::new("\\$_\\b").unwrap();
        let text_re = Regex::new("[a-z]+?\\b").unwrap();
        proptest!(|(ptn in "([a-z ]|\\$[0-9_]){0,10}", text in "[a-z ]{0,10}")| {
            let helper = |ptn: &str, text: &str| -> bool {
                FMBuilder::new(ptn)
                    .unwrap()
                    .name_matcher(ptn_re.clone(), text_re.clone())
                    .name_matcher_ignore(ptn_ignore_re.clone(), text_re.clone())
                    .build()
                    .unwrap()
                    .matches(text)
                    .is_ok()
            };

            helper(&ptn, &text);
        });
    }
}
