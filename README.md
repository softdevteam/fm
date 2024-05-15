# fm

`fm` is a simple fuzzy text matcher useful for matching multi-line patterns.

Its core feature is the wildcard operator `...`, which can be used in the
following ways:

  * If a line consists solely of `...` it means "match zero or more lines of
    text".
  * If a line starts with `...`, the search is not anchored to the start of the
    line.
  * If a line ends with `...`, the search is not anchored to the end of the
    line.

Note that `...` can appear both at the start and end of a line and if a line
consists of `......` (i.e. starts and ends with the wildcard with nothing
inbetween), it will match exactly one line. If the wildcard operator appears in
any other locations, it is matched literally.

A line consisting solely of `...` searches until the next line/group in the
pattern matches, which then anchors the remainder of the search: in other
words, searching never backtracks beyond a line consisting solely of `...`.
Each individual line constitutes a group *unless* the `(((` ... `)))` markers
(where each marker must be on its own line) group together multiple lines into
a single group. Within a group, line(s) can start/end with a wildcard but
cannot solely consist of a wildcard.

The following examples show `fm` in action using its defaults:

```rust
use fm::FMatcher;

assert!(FMatcher::new("a").unwrap().matches("a").is_ok());
assert!(FMatcher::new(" a ").unwrap().matches("a").is_ok());
assert!(FMatcher::new("a").unwrap().matches("b").is_err());
assert!(FMatcher::new("a\n...\nb").unwrap().matches("a\na\nb").is_ok());
assert!(FMatcher::new("a\n...\nb").unwrap().matches("a\na\nb\nb").is_err());
```

When a match fails, the matcher returns an error indicating the line number at
which the match failed. The error can be formatted for human comprehension
using the provided `Display` implementation.

If you want to use non-default options, you will first need to use `FMBuilder`
before having access to an `FMatcher`. For example, to use "name matching"
(where you specify that the same chunk of text must appear at multiple points
in the text, but without specifying exactly what the chunk must contain) you
can set options as follows:

```rust
use {fm::FMBuilder, regex::Regex};

let ptn_re = Regex::new(r"\$.+?\b").unwrap();
let text_re = Regex::new(r".+?\b").unwrap();
let matcher = FMBuilder::new("$1 $1")
                        .unwrap()
                        .name_matcher(ptn_re, text_re)
                        .build()
                        .unwrap();
assert!(matcher.matches("a a").is_ok());
assert!(matcher.matches("a b").is_err());
```
