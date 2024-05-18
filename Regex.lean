import Regex.Syntax.Hir
import Regex.Nfa
import Regex.Unicode
import Regex.Regex
import Regex.Notation

/-!
# Regex

A [regular expression](https://en.wikipedia.org/wiki/Regular_expression) engine written in
[Lean 4](https://github.com/leanprover/lean4).

This library is heavily based on the [Rust regex crate](https://docs.rs/regex/latest/regex/).

Contents:

1. [Syntax](#Syntax)
2. [Unicode support](#Unicode)
3. [Api](#Api)
4. [Examples](#Examples)
5. [Performance](#Performance)
6. [Inspect tool](#Inspect-tool)

## Syntax

The [syntax](https://docs.rs/regex/latest/regex/#syntax) of the Rust regex crate is documented below.
The syntax is similar to Perl-style regular expressions, but lacks a few features like

* [back references](https://pcre2project.github.io/pcre2/doc/html/pcre2syntax.html#SEC25),
* [look around assertions](https://pcre2project.github.io/pcre2/doc/html/pcre2syntax.html#SEC22).

This library supports the Rust regex syntax except
* non unicode mode,
* verbose mode.

### Matching one character

<pre>
.             any character except new line (includes new line with s flag)
[0-9]         any ASCII digit
\d            digit (\p{Nd})
\D            not digit
\pX           Unicode character class identified by a one-letter name
\p{Greek}     Unicode character class (general category or script)
\PX           Negated Unicode character class identified by a one-letter name
\P{Greek}     negated Unicode character class (general category or script)
</pre>

### Character classes

<pre>
[xyz]           A character class matching either x, y or z (union).
[^xyz]          A character class matching any character except x, y and z.
[a-z]           A character class matching any character in range a-z.
[[:alpha:]]     ASCII character class ([A-Za-z])
[[:^alpha:]]    Negated ASCII character class ([^A-Za-z])
[x[^xyz]]       Nested character class (matching any character except y and z)
[a-y&&xyz]      Intersection (matching x or y)
[0-9&&[^4]]     Subtraction using intersection and negation (matching 0-9 except 4)
[0-9--4]        Direct subtraction (matching 0-9 except 4)
[a-g~~b-h]      Symmetric difference (matching `a` and `h` only)
[\\[\\]]          Escaping in character classes (matching [ or ])
[a&&b]          An empty character class matching nothing
</pre>

### Composites

<pre>
xy    concatenation (x followed by y)
x|y   alternation (x or y, prefer x)
</pre>

### Repetitions

<pre>
x*        zero or more of x (greedy)
x+        one or more of x (greedy)
x?        zero or one of x (greedy)
x*?       zero or more of x (ungreedy/lazy)
x+?       one or more of x (ungreedy/lazy)
x??       zero or one of x (ungreedy/lazy)
x{n,m}    at least n x and at most m x (greedy)
x{n,}     at least n x (greedy)
x{n}      exactly n x
x{n,m}?   at least n x and at most m x (ungreedy/lazy)
x{n,}?    at least n x (ungreedy/lazy)
x{n}?     exactly n x
</pre>

### Empty matches

<pre>
^               the beginning of a haystack (or start-of-line with multi-line mode)
$               the end of a haystack (or end-of-line with multi-line mode)
\A              only the beginning of a haystack (even with multi-line mode enabled)
\z              only the end of a haystack (even with multi-line mode enabled)
\b              a Unicode word boundary (\w on one side and \W, \A, or \z on other)
\B              not a Unicode word boundary
\b{start}       a Unicode start-of-word boundary (\W|\A on the left, \w on the right)
\b{end}         a Unicode end-of-word boundary (\w on the left, \W|\z on the right))
\b{start-half}  half of a Unicode start-of-word boundary (\W|\A on the left)
\b{end-half}    half of a Unicode end-of-word boundary (\W|\z on the right)
</pre>

The empty regex is valid and matches the empty string. For example, the
empty regex matches `abc` at positions `0`, `1`, `2` and `3`.

### Grouping and flags

<pre>
(exp)          numbered capture group (indexed by opening parenthesis)
(?P&lt;name&gt;exp)  named (also numbered) capture group (names must be alpha-numeric)
(?&lt;name&gt;exp)   named (also numbered) capture group (names must be alpha-numeric)
(?:exp)        non-capturing group
(?flags)       set flags within current group
(?flags:exp)   set flags for exp (non-capturing)
</pre>

Capture group names must be any sequence of alpha-numeric Unicode codepoints,
in addition to `.`, `_`, `[` and `]`. Names must start with either an `_` or
an alphabetic codepoint. Alphabetic codepoints correspond to the `Alphabetic`
Unicode property, while numeric codepoints correspond to the union of the
`Decimal_Number`, `Letter_Number` and `Other_Number` general categories.

Flags are each a single character. For example, `(?x)` sets the flag `x`
and `(?-x)` clears the flag `x`. Multiple flags can be set or cleared at
the same time: `(?xy)` sets both the `x` and `y` flags and `(?x-y)` sets
the `x` flag and clears the `y` flag.

All flags are by default disabled unless stated otherwise. They are:

<pre>
i     case-insensitive: letters match both upper and lower case
m     multi-line mode: ^ and $ match begin/end of line
s     allow . to match \n
R     enables CRLF mode: when multi-line mode is enabled, \r\n is used
U     swap the meaning of x* and x*?
u     Unicode support (always enabled, *-u* is ignored)
-u    non unicode support (*-u* is ignored)
x     verbose mode, allow line comments (not implemented)
</pre>

Multi-line mode means `^` and `$` no longer match just at the beginning/end of
the input, but also at the beginning/end of lines:

### Escape sequences

Note that this includes all possible escape sequences, even ones that are
documented elsewhere.

<pre>
\*              literal *, applies to all ASCII except [0-9A-Za-z<>]
\a              bell (\x07)
\f              form feed (\x0C)
\t              horizontal tab
\n              new line
\r              carriage return
\v              vertical tab (\x0B)
\A              matches at the beginning of a haystack
\z              matches at the end of a haystack
\b              word boundary assertion
\B              negated word boundary assertion
\b{start}, \<   start-of-word boundary assertion
\b{end}, \>     end-of-word boundary assertion
\b{start-half}  half of a start-of-word boundary assertion
\b{end-half}    half of a end-of-word boundary assertion
\123            octal character code, up to three digits (when enabled)
\x7F            hex character code (exactly two digits)
\x{10FFFF}      any hex character code corresponding to a Unicode code point
\u007F          hex character code (exactly four digits)
\u{7F}          any hex character code corresponding to a Unicode code point
\U0000007F      hex character code (exactly eight digits)
\U{7F}          any hex character code corresponding to a Unicode code point
\p{Letter}      Unicode character class
\P{Letter}      negated Unicode character class
\d, \s, \w      Perl character class
\D, \S, \W      negated Perl character class
</pre>

### Perl character classes (Unicode friendly)

These classes are based on the definitions provided in
[UTS#18](https://www.unicode.org/reports/tr18/#Compatibility_Properties):

<pre>
\d     digit (\p{Nd})
\D     not digit
\s     whitespace (\p{White_Space})
\S     not whitespace
\w     word character (\p{Alphabetic} + \p{M} + \d + \p{Pc} + \p{Join_Control})
\W     not word character
</pre>

### ASCII character classes

These classes are based on the definitions provided in
[UTS#18](https://www.unicode.org/reports/tr18/#Compatibility_Properties):

<pre>
[[:alnum:]]    alphanumeric ([0-9A-Za-z])
[[:alpha:]]    alphabetic ([A-Za-z])
[[:ascii:]]    ASCII ([\x00-\x7F])
[[:blank:]]    blank ([\t ])
[[:cntrl:]]    control ([\x00-\x1F\x7F])
[[:digit:]]    digits ([0-9])
[[:graph:]]    graphical ([!-~])
[[:lower:]]    lower case ([a-z])
[[:print:]]    printable ([ -~])
[[:punct:]]    punctuation ([!-\/:-@\[-`{-~])
[[:space:]]    whitespace ([\t\n\v\f\r ])
[[:upper:]]    upper case ([A-Z])
[[:word:]]     word characters ([0-9A-Za-z_])
[[:xdigit:]]   hex digit ([0-9A-Fa-f])
</pre>

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
  let re ← Regex.build r"^\p{Math}\s*([^,]+),\s*(\p{Nd})\s*(\p{Math})\s*(\w)$"
  let captures := Regex.captures "∀ (n : Nat), 0 ≤ n" re
  IO.println s!"{captures}"
</pre>

Output is

<pre>
fullMatch: '∀ (n : Nat), 0 ≤ n', 0, 22
groups: #[(some ('(n : Nat)', 4, 13)), (some ('0', 15, 16)), (some ('≤', 17, 20)), (some ('n', 21, 22))]
</pre>

Components of regular expression:

- *^* : Assertion Start of line
- *\p{Math}* : match all characters with the Math property
- *\s\** : match white space
- *(\w)* : capturing group of word characters
- *(\p{Nd})* : capturing group of numeric characters

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
