import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Unicode
import Regex.Regex
import Regex.Notation

/-!
# Regex

A [regular expression](https://en.wikipedia.org/wiki/Regular_expression) engine written in
[Lean 4](https://github.com/leanprover/lean4).

This library is based on the [Rust regex crate](https://docs.rs/regex/latest/regex/)
and extended for compatibility with [PCRE2](https://www.pcre.org/).

Contents:

1. [Syntax](#Syntax)
2. [Unicode support](#Unicode)
3. [Api](#Api)
4. [Examples](#Examples)
5. [Performance](#Performance)
6. [Inspect tool](#Inspect-tool)

## Syntax

There are to syntax flavors:

- Pcre : compatibility with [PCRE2](https://www.pcre.org/) (default),
- Rust : compatibility with [Rust](https://docs.rs/regex/latest/regex/#syntax).

The following features are not yet implemented in the Pcre flavor:

* [subroutines](https://pcre2project.github.io/pcre2/doc/html/pcre2syntax.html#SEC26),
* [conditional patterns](https://pcre2project.github.io/pcre2/doc/html/pcre2syntax.html#TOC1),
* [backtracking control](https://pcre2project.github.io/pcre2/doc/html/pcre2syntax.html#SEC28),
* [variable length look behind](https://pcre2project.github.io/pcre2/doc/html/pcre2syntax.html#SEC22).

## Unicode

This library implements part of “Basic Unicode Support” (Level 1) as specified by the
[Unicode Technical Standard #18](https://www.unicode.org/reports/tr18/#Basic_Unicode_Support).

### RL1.1 Hex Notation

[RL1.1](https://www.unicode.org/reports/tr18/#RL1.1)

Hex Notation refers to the ability to specify a Unicode code point in a regular expression
via its hexadecimal code point representation. These forms of hexadecimal notation are supported:

<pre>
\x7F            hex character code (exactly two digits)
\x{10FFFF}      any hex character code corresponding to a Unicode code point
\u007F          hex character code (exactly four digits)
\u{7F}          any hex character code corresponding to a Unicode code point
\U0000007F      hex character code (exactly eight digits)
\U{7F}          any hex character code corresponding to a Unicode code point
</pre>

### RL1.2 Properties

[RL1.2](https://www.unicode.org/reports/tr18/#Categories)

A unicode character may have properties. A property has a name
and a type (`Unicode.PropertyType`) and may have values.

These forms of property notation are supported:

<pre>
\pX               Unicode character class identified by a one-letter name
\p{Greek}         Unicode character class given by property value
\p{Script=Greek}  Unicode character class given by property name and value
\PX               Negated Unicode character class identified by a one-letter name
\P{Greek}         negated Unicode character class (general category or script)
</pre>

The type `Unicode.PropertyName` contains all supported property names.

### RL1.3 Subtraction and Intersection

[RL1.3](https://www.unicode.org/reports/tr18/#RL1.3)

This library implements union, intersection and subtraction of sets of characters.

## Api

Main api for Regex library

- `Regex.build`: build a Regex from the given pattern
- `Regex.captures`: searches for the first match of the regex
- `Regex.all_captures`: searches all successive non-overlapping matches of the regex
- `regex%`: build the regular expression at compile time

## Examples

Get captures of "∀ (n : Nat), 0 ≤ n" :

<pre>
def Main : IO Unit := do
  let re := regex% r"^\p{Math}\s*(.(?<=\()([a-z])[^,]+),\s*(\p{Nd})\s*(\p{Math})\s*\2$"
  let captures := Regex.captures "∀ (n : Nat), 0 ≤ n" re
  IO.println s!"{captures}"
</pre>

Output is

<pre>
fullMatch: '∀ (n : Nat), 0 ≤ n', 0, 22
groups: #[(some ('(n : Nat)', 4, 13)), (some ('n', 5, 6)),
          (some ('0', 15, 16)), (some ('≤', 17, 20))]
</pre>

Components of regular expression:

- *\p{Math}* : match all characters with the Math property
- *(?<=\\()* : lookbehind of char '('
- *(\p{Nd})* : capturing group of numeric characters
- *\2* : backreference to second capturing group

## Performance

The performance is tested for 2 different kinds of regular expressions and haystacks.

The performance data is generated with the [benchmark tool](https://github.com/bergmannjg/regex/tree/main/benchmark) .

### Test 1

The performance is tested for the regular expression **a?<sup>n</sup>a<sup>n</sup>** and
the haystack a<sup>n</sup> where n means repetition i.e. a?a?aa for n = 2.
To find a match for this expression the BoundedBacktracker has to traverse the entire search space.

<table border="1" align="center">
<tr><th>n</th><th>seconds</th><th>visited values</th><th>backtracks</></tr>
<tr align="right"><td>100</td><td>0.005</td><td>20404</td><td>5050</td></tr>
<tr align="right"><td>500</td><td>0.150</td><td>502004</td><td>125250</td></tr>
<tr align="right"><td>1000</td><td>0.600</td><td>2004004</td><td>500500</td></tr>
<tr align="right"><td>2000</td><td>2.200</td><td>8008004</td><td>2001000</td></tr>
</table>

The visited values are the encoded (StateID, HaystackOffset) pairs that have been visited
by the backtracker within a single search (`BoundedBacktracker.SearchState`).

### Test 2

The performance is tested for the regular expression **(?i)Xyz** and
a haystack which contains **xyz** as last element.

<table border="1" align="center">
<tr align="right"><th>size of haystack</th><th>seconds</th><th>visited values</th></tr>
<tr align="right"><td>1 kb</td><td>0.170</td><td>5010</td></tr>
<tr align="right"><td>100 kb</td><td>0.340</td><td>500010</td></tr>
<tr align="right"><td>1000 kb</td><td>1.720</td><td>5000010</td></tr>
</table>

## Inspect tool

The inspect tool command line options:

- *ast* *re* : display the abstract syntax tree of the regex *re*,
- *hir* *re* : display the high-level intermediate representation of the regex *re*,
- *compile* *re* : display the non-deterministic finite automaton of the regex *re*,
- *captures* *re* *s : display the captures of the regex *re* in the string *s*.
- *benchmark* *n* : display the captures of the regex * a?<sup>n</sup>a<sup>n</sup>* in the string *a<sup>n</sup>*.

Output of *inspect ast 'a|b*

<pre>
Alternation
  0: Literal (a|b,0,1) Verbatim 'a'
  1: Literal (a|b,2,3) Verbatim 'b'
</pre>

Output of *inspect hir 'a|b*

<pre>
Alternation
  0: Literal 'a'
  1: Literal 'b'
</pre>

Output of *inspect compile 'a|b*

<pre>
0: UnionReverse [ 2 3 ]
1: Empty => 0
2: SparseTransitions [ 0x00-0xd7ff => 1 0xe000-0x10ffff => 1 ]
3: capture(pid=0, group=0, slot=0) => 6
4: byte-range a-a => 7
5: byte-range b-b => 7
6: Union [ 4 5 ]
7: Empty => 8
8: capture(pid=0, group=0, slot=1) => 9
9: Match(0)
</pre>

Output of *inspect captures 'a|b' a*

<pre>
fullMatch: 'a', 0, 1
groups: #[]
</pre>

-/
