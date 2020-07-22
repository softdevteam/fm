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
