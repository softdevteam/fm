# fm 0.4.0 (2024-08-30)

* Add the `..~` "group match" wildcard, which searches until it finds a match
  for a group of lines. This means that fm now backtracks! The behaviour of the
  `...` interline wildcard is unchanged, and is preferred, because it has more
  predictable performance and leads to stronger tests.

* Report names matched when matching fails. When matching fails, it can be hard
  to work out what went wrong, particularly when name matching is used. fm now
  reports the set of names and their values at the point of failure, which
  helps debug matching problems.

* Add support for "ignorable" name matchers. Sometimes one needs to match a
  particular pattern, but the specific text matched is irrelevant. As a one-off
  this was easily handled, but if you had multiple places where you wanted to
  do this, you had to use a fresh name for each such instance, which is at best
  obfuscatory and at worst error prone. Ignorable name matchers allow you to
  use the same name (e.g. `_`) multiple times, each matching the same pattern,
  but not comparing the text matched with other instances of the ignorable
  name.

* Report the text line where pattern failed to match from. Previously when
  `...` failed, it told you how-far-it-got before realising it had failed,
  rather than the more useful where-it-started.

* Remove "distinct name matching" in favour of the more powerful "name
  matching validator". Distinct name matching can now be expressed as:

  ```
  .name_matching_validator(|names| {
    names.values().collect::<HashSet<_>>().len() == names.len()
  })
  ```


# fm 0.3.0 (2024-03-20)

* Add `OutputFormatter`s. The default output formatting has now changed from a
  summary of the pattern and text to: the raw text followed by the
  (same-as-before) summary.

* `FMatchError` no longer implements `PartialEq`.


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
