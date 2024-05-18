# Lean 4 Regex

A [regular expression](https://en.wikipedia.org/wiki/Regular_expression) engine written in
[Lean 4](https://github.com/leanprover/lean4).

This library is heavily based on the [Rust regex crate](https://docs.rs/regex/latest/regex/).

Main restrictions:

- focus on unicode data,
- simple api and few configurations,
- [BoundedBacktracker](https://bergmannjg.github.io/regex/Regex/Backtrack.html) as the single regex engine,
- no optimizations.

## Installation

Add the following dependency to lakefile.lean:

```lean
require Regex from git
  "https://github.com/bergmannjg/regex" @ "main"
```

## Documentation

The main documentation is in [Regex.lean](https://bergmannjg.github.io/regex/Regex.html)

## Example

```lean
-- build `re` at compile time
def re := regex% "a?b"
-- searches for the first match in `re`
#eval Regex.captures "b" re

--Output is
--fullMatch: 'b', 0, 1
--groups: #[]
```

## Test

The library is tested with the [testdata](./testdata) of Rust Regex crate.

The tests are run with

```sh
./.lake/build/bin/test --all ./testdata/
```

The tests passed successfully except those with not yet supported features:

- non unicode data.

## License

This project is licensed under the MIT [license](./LICENSE).

The data in `Regex/Unicode/data/` is licensed under the Unicode
License Agreement
([LICENSE-UNICODE](https://www.unicode.org/copyright.html#License)).

The .toml files in `testdata/rust` are licensed under the
([LICENSE-RUST-REGEX](https://github.com/rust-lang/regex/blob/master/LICENSE-MIT)).
