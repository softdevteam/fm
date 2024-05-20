#![doc = include_str!("../README.md")]
#![allow(clippy::upper_case_acronyms)]

use std::{
    collections::hash_map::{Entry, HashMap},
    default::Default,
    error::Error,
    fmt,
    str::Lines,
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
    name_matchers: Vec<(Regex, Regex)>,
    distinct_name_matching: bool,
    ignore_leading_whitespace: bool,
    ignore_trailing_whitespace: bool,
    ignore_surrounding_blank_lines: bool,
}

impl Default for FMOptions {
    fn default() -> Self {
        FMOptions {
            output_formatter: OutputFormatter::InputThenSummary,
            name_matchers: Vec::new(),
            distinct_name_matching: false,
            ignore_leading_whitespace: true,
            ignore_trailing_whitespace: true,
            ignore_surrounding_blank_lines: true,
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
    /// let ptn_re = Regex::new(r"\$.+?\b").unwrap();
    /// let text_re = Regex::new(r".+?\b").unwrap();
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
        self.options.name_matchers.push((ptn_re, text_re));
        self
    }

    /// If `yes`, then different names cannot match the same text value. For example if `$1` binds
    /// to `a` then `$2` will refuse to match against `a` (though `$1` will continue to match
    /// against only `a`). Defaults to `false`.
    pub fn distinct_name_matching(mut self, yes: bool) -> Self {
        self.options.distinct_name_matching = yes;
        self
    }

    /// If `yes`, then each line's leading whitespace will be ignored in both pattern and text;
    /// otherwise leading whitespace must match. Defaults to `true`.
    pub fn ignore_leading_whitespace(mut self, yes: bool) -> Self {
        self.options.ignore_leading_whitespace = yes;
        self
    }

    /// If `yes`, then each line's trailing whitespace will be ignored in both pattern and text;
    /// otherwise trailing whitespace must match. Defaults to `true`.
    pub fn ignore_trailing_whitespace(mut self, yes: bool) -> Self {
        self.options.ignore_trailing_whitespace = yes;
        self
    }

    /// If `yes`, blank lines at the start and end of both the pattern and text are ignored for
    /// matching purposes. Defaults to `true`.
    pub fn ignore_surrounding_blank_lines(mut self, yes: bool) -> Self {
        self.options.ignore_surrounding_blank_lines = yes;
        self
    }

    /// Turn this `FMBuilder` into a `FMatcher`.
    pub fn build(self) -> Result<FMatcher<'a>, Box<dyn Error>> {
        self.validate()?;
        Ok(FMatcher {
            ptn: self.ptn,
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

        for (ref ptn_re, _) in &self.options.name_matchers {
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
    ptn: &'a str,
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
        let mut ptn_lines = self.ptn.lines();
        let (mut ptnl, mut ptn_lines_off) = self.skip_blank_lines(&mut ptn_lines, None);
        ptn_lines_off += 1;
        let mut text_lines = text.lines();
        let (mut textl, mut text_lines_off) = self.skip_blank_lines(&mut text_lines, None);
        text_lines_off += 1;
        loop {
            match (ptnl, textl) {
                (Some(x), Some(y)) => {
                    if x.trim() == LINE_ANCHOR_WILDCARD {
                        ptnl = ptn_lines.next();
                        ptn_lines_off += 1;
                        match ptnl {
                            Some(x) => {
                                while let Some(y) = textl {
                                    text_lines_off += 1;
                                    if self.match_line(&mut names, x, y) {
                                        break;
                                    }
                                    textl = text_lines.next();
                                }
                                text_lines_off -= 1;
                            }
                            None => return Ok(()),
                        }
                    } else if x.trim() == GROUP_ANCHOR_WILDCARD {
                        let ptn_lines_off_orig = ptn_lines_off;
                        let text_lines_off_orig = text_lines_off;
                        ptnl = ptn_lines.next();
                        // If the interline wildcard is the last part of the pattern, then we
                        // implicitly match any remaining text: i.e. we're done!
                        if ptnl.is_none() {
                            return Ok(());
                        }
                        // We now have to perform (bounded) backtracking
                        ptn_lines_off += 1;
                        let mut ptn_lines_sub = ptn_lines.clone();
                        let mut ptnl_sub = ptnl;
                        let mut ptn_lines_off_sub = ptn_lines_off;
                        let mut text_lines_sub = text_lines.clone();
                        let mut text_lines_off_sub = text_lines_off;
                        let mut textl_sub = textl;
                        let mut names_sub = names.clone();
                        loop {
                            match (ptnl_sub, textl_sub) {
                                (None, None) => return Ok(()),
                                (Some(x), _)
                                    if x.trim() == GROUP_ANCHOR_WILDCARD
                                        || x.trim() == LINE_ANCHOR_WILDCARD =>
                                {
                                    // We've matched everything successfully
                                    ptn_lines = ptn_lines_sub;
                                    ptnl = ptnl_sub;
                                    ptn_lines_off = ptn_lines_off_sub;
                                    text_lines = text_lines_sub;
                                    textl = textl_sub;
                                    text_lines_off = text_lines_off_sub;
                                    names = names_sub;
                                    break;
                                }
                                (None, Some(_)) => {
                                    match self.skip_blank_lines(&mut text_lines_sub, textl_sub) {
                                        (Some(_), _) => {
                                            return Err(FMatchError {
                                                output_formatter: self.options.output_formatter,
                                                ptn: self.ptn.to_owned(),
                                                text: text.to_owned(),
                                                ptn_line_off: ptn_lines_off_orig,
                                                text_line_off: text_lines_off_orig,
                                            })
                                        }
                                        (None, _) => return Ok(()),
                                    }
                                }
                                (Some(_), None) => {
                                    return Err(FMatchError {
                                        output_formatter: self.options.output_formatter,
                                        ptn: self.ptn.to_owned(),
                                        text: text.to_owned(),
                                        ptn_line_off: ptn_lines_off_orig,
                                        text_line_off: text_lines_off_orig,
                                    });
                                }
                                (Some(x), Some(y)) => {
                                    if self.match_line(&mut names_sub, x, y) {
                                        ptnl_sub = ptn_lines_sub.next();
                                        ptn_lines_off_sub += 1;
                                        textl_sub = text_lines_sub.next();
                                        text_lines_off_sub += 1;
                                    } else {
                                        // We failed to match, so we need to reset the
                                        // pattern, but advance the text.
                                        ptn_lines_sub = ptn_lines.clone();
                                        ptnl_sub = ptnl;
                                        ptn_lines_off_sub += 1;
                                        textl_sub = text_lines.next();
                                        text_lines_off += 1;
                                        text_lines_sub = text_lines.clone();
                                        text_lines_off_sub = text_lines_off;
                                        names_sub = names.clone();
                                    }
                                }
                            }
                        }
                    } else if self.match_line(&mut names, x, y) {
                        ptnl = ptn_lines.next();
                        ptn_lines_off += 1;
                        textl = text_lines.next();
                        text_lines_off += 1;
                    } else {
                        return Err(FMatchError {
                            output_formatter: self.options.output_formatter,
                            ptn: self.ptn.to_owned(),
                            text: text.to_owned(),
                            ptn_line_off: ptn_lines_off,
                            text_line_off: text_lines_off,
                        });
                    }
                }
                (None, None) => return Ok(()),
                (Some(x), None) => {
                    if let LINE_ANCHOR_WILDCARD | GROUP_ANCHOR_WILDCARD = x.trim() {
                        ptnl = ptn_lines.next();
                        ptn_lines_off += 1;
                        // If the interline wildcard is the last line in the pattern, we're done.
                        // If it isn't, then the pattern hasn't matched: rather than explicitly
                        // throw an error in this clause, we let the next iteration of the outer
                        // while loop catch this case.
                        if ptnl.is_none() {
                            return Ok(());
                        }
                    } else {
                        match self.skip_blank_lines(&mut ptn_lines, Some(x)) {
                            (Some(_), skipped) => {
                                return Err(FMatchError {
                                    output_formatter: self.options.output_formatter,
                                    ptn: self.ptn.to_owned(),
                                    text: text.to_owned(),
                                    ptn_line_off: ptn_lines_off + skipped,
                                    text_line_off: text_lines_off,
                                });
                            }
                            (None, _) => return Ok(()),
                        }
                    }
                }
                (None, Some(x)) => {
                    let (x, skipped) = self.skip_blank_lines(&mut text_lines, Some(x));
                    if x.is_none() {
                        return Ok(());
                    }
                    return Err(FMatchError {
                        output_formatter: self.options.output_formatter,
                        ptn: self.ptn.to_owned(),
                        text: text.to_owned(),
                        ptn_line_off: ptn_lines_off,
                        text_line_off: text_lines_off + skipped,
                    });
                }
            }
        }
    }

    /// Skip blank lines in the input if `options.ignore_surrounding_blank_lines` is set. If `line`
    /// is `Some(...)` that is taken as the first line of the input and after that is processesd
    /// the `lines` iterator is used. The contents of the first non-blank line are returned as well
    /// as the number of lines skipped. Notice that this is intended *only* to skip blank lines at
    /// the start and end of a string, as it is predicated on the `ignore_surrounding_blank_lines`
    /// option (i.e. don't use this to skip blank lines in the middle of the input, because that
    /// will fail if the user sets `ignore_surrounding_blank_lines` to `false`!).
    #[allow(clippy::while_let_on_iterator)]
    fn skip_blank_lines(
        &self,
        lines: &mut Lines<'a>,
        line: Option<&'a str>,
    ) -> (Option<&'a str>, usize) {
        if !self.options.ignore_surrounding_blank_lines {
            if line.is_some() {
                return (line, 0);
            }
            return (lines.next(), 0);
        }
        let mut trimmed = 0;
        if let Some(l) = line {
            if !l.trim().is_empty() {
                return (Some(l), 0);
            }
            trimmed += 1;
        }
        while let Some(l) = lines.next() {
            if !l.trim().is_empty() {
                return (Some(l), trimmed);
            }
            trimmed += 1;
        }
        (None, trimmed)
    }

    /// Try matching `ptn` against `text`. If, and only if, the match is successful, `names` will
    /// be updated with matched names.
    fn match_line<'b>(
        &self,
        names: &mut HashMap<&'a str, &'b str>,
        mut ptn: &'a str,
        mut text: &'b str,
    ) -> bool {
        if self.options.ignore_leading_whitespace {
            ptn = ptn.trim_start();
            text = text.trim_start();
        }

        if self.options.ignore_trailing_whitespace {
            ptn = ptn.trim_end();
            text = text.trim_end();
        }

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
                for (ref ptn_re, ref text_re) in &self.options.name_matchers {
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
}

/// An error indicating a failed match.
/// The pattern and text are copied in so that the error isn't tied to their lifetimes.
pub struct FMatchError {
    output_formatter: OutputFormatter,
    ptn: String,
    text: String,
    ptn_line_off: usize,
    text_line_off: usize,
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

#[cfg(test)]
mod tests {
    use super::*;

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
    fn dont_ignore_surrounding_blank_lines() {
        fn helper(ptn: &str, text: &str) -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .ignore_surrounding_blank_lines(false)
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

        assert_eq!(helper("a\n...\nd", "a\nb\nc"), (3, 3));
        assert_eq!(helper("a\nb...", "a\nb\nc"), (3, 3));
        assert_eq!(helper("a\n...b...", "a\nxb\nc"), (3, 3));

        assert_eq!(helper("a\n\nb", "a\n"), (3, 2));
        assert_eq!(helper("a\n", "a\n\nb"), (2, 3));

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
        assert_eq!(helper("...\nd\n", "a\nb\nc\n0\ne"), (2, 5));

        assert_eq!(helper("a\n..~\nc\nd\ne", "a\nb\nc\nd"), (2, 2));
        assert_eq!(helper("a\n..~\nc\nd", "a\nb\nc\ne"), (2, 2));
        assert_eq!(helper("a\n..~\nc\nd", "a\nc\ne\nc\ne"), (2, 2));
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

Text (error at line 3):
   |a
   |
>> |b
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

    #[test]
    fn test_allow_whitespace() {
        let helper = |ptn: &str, text: &str| -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .ignore_leading_whitespace(false)
                .ignore_trailing_whitespace(false)
                .build()
                .unwrap()
                .matches(text)
                .is_ok()
        };

        assert!(helper("a\na", "a\na"));

        assert!(helper("a\n a", "a\n a"));
        assert!(!helper("a\n a", "a\na"));
        assert!(!helper("a\na", "a\n a"));

        assert!(helper("a\na ", "a\na "));
        assert!(!helper("a\na", "a\na "));
        assert!(!helper("a\na ", "a\na"));
    }
}
