# fm 0.2.2 (2023-05-23)

* `...\n...` is an illegal pattern, but previously caused an error when
  matching: it is now reported at build time as an invalid pattern.


# fm 0.2.1 (2021-03-05)

* Fix Clippy warnings.


# fm 0.2.0 (2020-11-26)

* Multiple name matchers can now be supplied. The API in `FMBuilder` has changed from:
    ```
    pub fn name_matcher(mut self, matcher: (Regex, Regex)) -> Self {
    ```
  to:
    ```
    pub fn name_matcher(mut self, ptn_re: Regex, text_re: Regex) -> Self {
    ```
  Calling `name_matcher` multiple times adds additional name matchers; name
  matchers are matched against text in the order they were added.


# fm 0.1.4 (2020-07-22)

* Add ability to use wildcards at the end of lines when name matching is used
  (so `$1...` is allowed but `...$1` and `...$1...` are still unallowed).

* Fix crash caused when the remaining pattern exceeds the remaining text.


# fm 0.1.3 (2020-07-21)

* Fix bug where, if name matching is turned on, lines which failed to match
  could incorrectly add to the name dictionary.


# fm 0.1.2 (2020-07-13)

* Show at most 3 lines of context either side of an error line. This means that
  even large patterns and/or text do not cause the user to have to scroll
  endlessly through the console.


# fm 0.1.1 (2020-07-08)

* Add `ignore_leading_whitespace` and `ignore_trailing_whitespace` options.
  Both default to `true`, meaning that per-line leading/trailing whitespace is
  ignored. Setting them to false makes `fm` sensitive to per-line
  leading/trailing whitespace.


# fm 0.1.0 (2020-07-02)

First public release.
