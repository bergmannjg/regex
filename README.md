# Lean 4 Regex

A [regular expression](https://en.wikipedia.org/wiki/Regular_expression) engine written in
[Lean 4](https://github.com/leanprover/lean4).

This library is based on the [Rust regex crate](https://docs.rs/regex/latest/regex/)
and extended for compatibility with [PCRE2](https://www.pcre.org/)
(see [Syntax](https://bergmannjg.github.io/regex/Regex.html#Syntax)).

Main restrictions:

- focus on unicode data,
- simple api and few configurations,
- [BoundedBacktracker](https://bergmannjg.github.io/regex/Regex/Backtrack.html) as the single regex engine,
- no optimizations.

## Installation

Add the following dependency to lakefile.toml:

```toml
[[require]]
name = "Regex"
git = "https://github.com/bergmannjg/regex"
```

## Documentation

The main documentation is in [Regex.lean](https://bergmannjg.github.io/regex/Regex.html)

## Verification

Some parts of the regex compilation and execution are verified.

* The [compilation](https://bergmannjg.github.io/regex/Regex/Compiler.html#Compiler.compile)
throws [no exceptions](https://bergmannjg.github.io/regex/Regex/Compiler/Lemmas/Compile.html#Compiler.Lemmas.compile_eq_ok).
* All transitions in the resulting [NFA](https://bergmannjg.github.io/regex/Regex/NFA/Basic.html#NFA.Checked.NFA) are valid (i.e. every transition maps to a valid state).
* Executing the NFA with the [bounded backtracker](https://bergmannjg.github.io/regex/Regex/Backtrack.html#BoundedBacktracker.backtrack.loop) always terminates.
* The matches of the regex are [slices](https://bergmannjg.github.io/regex/Regex/Backtrack.html#BoundedBacktracker.matches) of the original string.

## Example

Get captures of "∀ (n : Nat), 0 ≤ n" :

```lean
def Main : IO Unit := do
  let re := regex% r"^\p{Math}\s*.(?<=\()([a-z])[^,]+,\s*(\p{Nd})\s*(\p{Math})\s*\1$"
  let captures := Regex.captures "∀ (n : Nat), 0 ≤ n" re
  IO.println s!"{captures}"
```

Output is

```lean
fullMatch: '∀ (n : Nat), 0 ≤ n', 0, 22
groups: #[(some ('n', 5, 6)), (some ('0', 15, 16)), (some ('≤', 17, 20))]
```

Api

- *regex%* : notation to build the regular expression at compile time
- *captures* : searches for the first match of the  regular expression

Components of regular expression:

- *\p{Math}* : match all characters with the Math property
- *(?<=\\()* : lookbehind of char '('
- *(\p{Nd})* : capturing group of numeric characters
- *\1* : backreference to first capturing group

## Test

The library is tested
with the [testdata](./testdata/pcre) of the PCRE2 library
and the [testdata](./testdata/rust) of the Rust Regex crate.

The tests are run with

```sh
lake test
```

## License

This project is licensed under the MIT [license](./LICENSE).

The data in `Regex/Unicode/data/` is licensed under the Unicode
License Agreement
([LICENSE-UNICODE](https://www.unicode.org/copyright.html#License)).

The .toml files in `testdata/rust` are licensed under the
([LICENSE-RUST-REGEX](https://github.com/rust-lang/regex/blob/master/LICENSE-MIT)).
