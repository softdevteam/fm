//! `fm` is a simple non-backtracking fuzzy text matcher useful for matching multi-line patterns
//! and text. At its most basic the wildcard operator (`...` by default) can be used in the
//! following ways:
//!
//!   * If a line consists solely of `...` it means "match zero or more lines of text".
//!   * If a line starts with `...`, the search is not anchored to the start of the line.
//!   * If a line ends with `...`, the search is not anchored to the end of the line.
//!
//! Note that `...` can appear both at the start and end of a line and if a line consists of
//! `......` (i.e. starts and ends with the wildcard with nothing inbetween), it will match exactly
//! one line. If the wildcard operator appears in any other locations, it is matched literally.
//! Wildcard matching does not backtrack, so if a line consists solely of `...` then the next
//! matching line anchors the remainder of the search.
//!
//! The following examples show `fm` in action using its defaults (i.e. `...` as the wildcard
//! operator, and leading/trailing whitespace ignored):
//!
//! ```rust
//! use fm::FMatcher;
//!
//! assert!(FMatcher::new("a").unwrap().matches("a").is_ok());
//! assert!(FMatcher::new(" a ").unwrap().matches("a").is_ok());
//! assert!(FMatcher::new("a").unwrap().matches("b").is_err());
//! assert!(FMatcher::new("a\n...\nb").unwrap().matches("a\na\nb").is_ok());
//! assert!(FMatcher::new("a\n...\nb").unwrap().matches("a\na\nb\nb").is_err());
//! ```
//!
//! If you want to use non-default options, you will first need to use `FMBuilder` before having
//! access to an `FMatcher`. For example, to use "name matching" (where you specify that the same
//! chunk of text must appear at multiple points in the text, but without specifying exactly what
//! the chunk must contain) you can set options as follows:
//!
/// ```rust
/// use {fm::FMBuilder, regex::Regex};
///
/// let ptn_re = Regex::new("\\$.+?\\b").unwrap();
/// let text_re = Regex::new(".+?\\b").unwrap();
/// let matcher = FMBuilder::new("$1 $1")
///                         .unwrap()
///                         .name_matcher(Some((ptn_re, text_re)))
///                         .build()
///                         .unwrap();
/// assert!(matcher.matches("a a").is_ok());
/// assert!(matcher.matches("a b").is_err());
/// ```
use std::{
    collections::hash_map::{Entry, HashMap},
    default::Default,
    error::Error,
};

use regex::Regex;

const WILDCARD: &str = "...";

#[derive(Debug)]
struct FMOptions {
    name_matcher: Option<(Regex, Regex)>,
    ignore_leading_whitespace: bool,
    ignore_trailing_whitespace: bool,
}

impl Default for FMOptions {
    fn default() -> Self {
        FMOptions {
            name_matcher: None,
            ignore_leading_whitespace: true,
            ignore_trailing_whitespace: true,
        }
    }
}

/// Build up a `FMatcher` allowing the setting of options.
///
/// ```rust
/// use {fm::FMBuilder, regex::Regex};
///
/// let ptn_re = Regex::new("\\$.+?\\b").unwrap();
/// let text_re = Regex::new(".+?\\b").unwrap();
/// let matcher = FMBuilder::new("$1 $1")
///                         .unwrap()
///                         .name_matcher(Some((ptn_re, text_re)))
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

    /// Add a name matcher `Some((ptn_re, text_re))` (or unset it with `None`). Defaults to `None`.
    ///
    /// Name matchers allow you to ensure that different parts of the text match without specifying
    /// precisely what they match. For example, if you have output where you want to ensure that
    /// two locations always match the same name, but the name is non-deterministic you can allow
    /// the use of `$` wildcards in your pattern:
    ///
    /// ```rust
    /// use {fm::FMBuilder, regex::Regex};
    ///
    /// let ptn_re = Regex::new("\\$.+?\\b").unwrap();
    /// let text_re = Regex::new(".+?\\b").unwrap();
    /// let matcher = FMBuilder::new("$1 b $1")
    ///                         .unwrap()
    ///                         .name_matcher(Some((ptn_re, text_re)))
    ///                         .build()
    ///                         .unwrap();
    /// assert!(matcher.matches("a b a").is_ok());
    /// assert!(matcher.matches("a b b").is_err());
    /// ```
    ///
    /// Note that name matching and wildcards cannot be used together in a single line (e.g. for
    /// the above example, `...$1` would lead to a pattern validation error).
    pub fn name_matcher(mut self, matcher: Option<(Regex, Regex)>) -> Self {
        self.options.name_matcher = matcher;
        self
    }

    #[doc(hidden)]
    pub fn ignore_leading_whitespace(mut self, yes: bool) -> Self {
        self.options.ignore_leading_whitespace = yes;
        self
    }

    #[doc(hidden)]
    pub fn ignore_trailing_whitespace(mut self, yes: bool) -> Self {
        self.options.ignore_trailing_whitespace = yes;
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
        if let Some((ref ptn_re, _)) = self.options.name_matcher {
            for (i, l) in self.ptn.lines().enumerate() {
                let l = l.trim();
                if (l.starts_with("...") || l.ends_with("...")) && ptn_re.is_match(l) {
                    return Err(Box::<dyn Error>::from(format!(
                        "Can't mix name matching with wildcards on line {}.",
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
    /// A convenience method that automatically builds a pattern for you using `FMBuilder`'s
    /// default options.
    pub fn new(ptn: &'a str) -> Result<FMatcher, Box<dyn Error>> {
        FMBuilder::new(ptn)?.build()
    }

    /// Does this fuzzy matcher match `text`? Returns `Ok(())` on success or `Err(usize)` on error
    /// where the `usize` is the line number of the first line in `text` where the match failed.
    pub fn matches(&self, text: &str) -> Result<(), usize> {
        let mut names = HashMap::new();
        let mut ptn_lines = self.ptn.lines();
        let mut ptnl = ptn_lines.next();
        let mut text_lines = text.lines();
        let mut textl = text_lines.next();
        let mut text_lines_off = 1;
        loop {
            match (ptnl, textl) {
                (Some(x), Some(y)) => {
                    if x.trim() == WILDCARD {
                        ptnl = ptn_lines.next();
                        match ptnl {
                            Some(x) => {
                                while let Some(y) = textl {
                                    if self.match_line(&mut names, x, y) {
                                        break;
                                    }
                                    textl = text_lines.next();
                                    text_lines_off += 1;
                                }
                                text_lines_off -= 1;
                            }
                            None => return Ok(()),
                        }
                    } else if self.match_line(&mut names, x, y) {
                        ptnl = ptn_lines.next();
                        textl = text_lines.next();
                        text_lines_off += 1;
                    } else {
                        return Err(text_lines_off);
                    }
                }
                (None, None) => return Ok(()),
                (Some(x), None) if x.trim() == WILDCARD => return Ok(()),
                (Some(_), None) | (None, Some(_)) => return Err(text_lines_off),
            }
        }
    }

    fn match_line<'b>(
        &self,
        names: &mut HashMap<&'a str, &'b str>,
        mut ptn: &'a str,
        mut text: &'b str,
    ) -> bool {
        if self.options.ignore_leading_whitespace {
            ptn = ptn.trim_start();
            text = text.trim_start();
        } else {
            todo!();
        }

        if self.options.ignore_trailing_whitespace {
            ptn = ptn.trim_end();
            text = text.trim_end();
        } else {
            todo!();
        }

        let sww = ptn.starts_with(WILDCARD);
        let eww = ptn.ends_with(WILDCARD);
        if sww && eww {
            text.find(&ptn[WILDCARD.len()..ptn.len() - WILDCARD.len()])
                .is_some()
        } else if sww {
            text.ends_with(&ptn[WILDCARD.len()..])
        } else if eww {
            text.starts_with(&ptn[..ptn.len() - WILDCARD.len()])
        } else {
            match self.options.name_matcher {
                Some((ref ptn_re, ref text_re)) => {
                    while let Some(ptnm) = ptn_re.find(ptn) {
                        if ptnm.start() == ptnm.end() {
                            panic!("Name pattern matched the empty string.");
                        }
                        if ptn[..ptnm.start()] != text[..ptnm.start()] {
                            return false;
                        }
                        ptn = &ptn[ptnm.end()..];
                        text = &text[ptnm.start()..];
                        if let Some(textm) = text_re.find(text) {
                            if textm.start() == textm.end() {
                                panic!("Text pattern matched the empty string.");
                            }
                            match names.entry(ptnm.as_str()) {
                                Entry::Occupied(e) => {
                                    if e.get() != &textm.as_str() {
                                        return false;
                                    }
                                }
                                Entry::Vacant(e) => {
                                    e.insert(textm.as_str());
                                }
                            }
                            text = &text[textm.end()..];
                        } else {
                            return false;
                        }
                    }
                    ptn == text
                }
                None => ptn == text,
            }
        }
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
    }

    #[test]
    fn name_matcher() {
        let nameptn_re = Regex::new("\\$.+?\\b").unwrap();
        let name_re = Regex::new(".+?\\b").unwrap();
        let helper = |ptn: &str, text: &str| -> bool {
            FMBuilder::new(ptn)
                .unwrap()
                .name_matcher(Some((nameptn_re.clone(), name_re.clone())))
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
    }

    #[test]
    fn error_line() {
        let ptn_re = Regex::new("\\$.+?\\b").unwrap();
        let text_re = Regex::new(".+?\\b").unwrap();
        let helper = |ptn: &str, text: &str| -> usize {
            FMBuilder::new(ptn)
                .unwrap()
                .name_matcher(Some((ptn_re.clone(), text_re.clone())))
                .build()
                .unwrap()
                .matches(text)
                .unwrap_err()
        };

        assert_eq!(helper("a\n...\nd", "a\nb\nc"), 3);
        assert_eq!(helper("a\nb...", "a\nb\nc"), 3);
        assert_eq!(helper("a\n...b...", "a\nxb\nc"), 3);

        assert_eq!(helper("$1", ""), 1);
        assert_eq!(helper("$1, $1", "a, b"), 1);
        assert_eq!(helper("$1, a, $1", "a, b, a"), 1);
        assert_eq!(helper("$1, a, $1", "a, a, b"), 1);
        assert_eq!(helper("$1, $1, a", "a, a, b"), 1);
        assert_eq!(helper("$1, $1, a", "a, b, a"), 1);

        assert_eq!(helper("$1", ""), 1);
        assert_eq!(helper("$1\n$1", "a\nb"), 2);
        assert_eq!(helper("$1\na\n$1", "a\nb\na"), 2);
        assert_eq!(helper("$1\na\n$1", "a\na\nb"), 3);
        assert_eq!(helper("$1\n$1\na", "a\na\nb"), 3);
        assert_eq!(helper("$1\n$1\na", "a\nb\na"), 2);
    }

    #[test]
    #[should_panic]
    fn empty_name_pattern() {
        let ptn_re = Regex::new("").unwrap();
        let text_re = Regex::new(".+?\\b").unwrap();
        FMBuilder::new("$1")
            .unwrap()
            .name_matcher(Some((ptn_re, text_re)))
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
            .name_matcher(Some((ptn_re, text_re)))
            .build()
            .unwrap()
            .matches("x")
            .unwrap();
    }

    #[test]
    fn wildcards_and_names() {
        let ptn_re = Regex::new("\\$.+?\\b").unwrap();
        let text_re = Regex::new("").unwrap();
        let builder = FMBuilder::new("$1\n...$1abc")
            .unwrap()
            .name_matcher(Some((ptn_re, text_re)));
        assert_eq!(
            &(*(builder.build().unwrap_err())).to_string(),
            "Can't mix name matching with wildcards on line 2."
        );
    }
}
