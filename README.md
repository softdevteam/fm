# fm

`fm` is a simple limited backtracking fuzzy text matcher useful for matching
multi-line *patterns* and *literal* text. Wildcard operators can be used to
match parts of a line and to skip multiple lines of text. For example this
*pattern*:

```text
...A
...
D...
```

will successfully match against literals such as:

```text
xyzA
B
C
Dxyz
```


## Intraline matching

The intraline wildcard operator `...` can appear at the start and/or end of a
line. `...X...` matches any literal line that contains "X"; `...X` matches any
literal line that ends with "X"; and `X...` matches any literal line that
starts with "X". `......` matches exactly one literal line (i.e. the contents
of the literal line are irrelevant but this will not match against the end
of the literal text).


## Interline matching

There are two interline wildcard operators that match zero or more literal
lines until a match for the next *item* is found, at which point the search is
*anchored* (i.e. backtracking will not occur before the anchor). An item is
either:

  * A single pattern line.
  * A group of pattern lines. A group is the sequence of pattern lines between
    two interline wildcard operators or, if no wildcard operator is found, the
    end of the pattern.

The interline wildcards are:

  * The *prefix match* wildcard `...` searches until it finds a match for the
    line immediately after the interline operator ("the prefix"), at which
    point the search is anchored. This wildcard does not backtrack.
  * The *group match* wildcard `..~` searches until it finds a match for the
    next group, at which point the search is anchored. This wildcard
    backtracks, though never further than one group.

Interline wildcards cannot directly follow each other i.e. `...\n...?` is an
invalid pattern. Interline wildcards can appear at the beginning or end of
a pattern: at the end of a pattern, both interline wildcards have identical
semantics to each other.

Consider this pattern:

```text
A
...
B
C
...
```

This will match successfully against the literal:

```text
A
D
B
C
E
```

but fail to match against the literal:

```text
A
D
B
B
C
E
```

because the `...` matches against the first "B", which anchors the search, then
immediately fails to match against the second "B".

In contrast the pattern:

```text
A
..~
B
C
...
```

does match the literal because `..~` backtracks on the second "B".

There are two reasons why you should default to using `...` rather than `..~`.
Most obviously `...` does not backtrack and has linear performance. Less
obviously `...` is a more rigorous test, since it cannot skip prefix matches
(i.e. the next line after the `...` in the pattern) in the literal.


## API

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

let ptn_re = Regex::new(r"\$[0-9]+?\b").unwrap();
let text_re = Regex::new(r"[a-z]+?\b").unwrap();
let matcher = FMBuilder::new("$1 $1")
                        .unwrap()
                        .name_matcher(ptn_re, text_re)
                        .build()
                        .unwrap();
assert!(matcher.matches("a a").is_ok());
assert!(matcher.matches("a b").is_err());
```
