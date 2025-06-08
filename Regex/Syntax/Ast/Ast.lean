import Batteries.Data.Array.Basic
import Regex.Utils

/-!
## Abstract syntax tree for a single regular expression.

The abstract syntax tree `Syntax.AstItems.Ast`.
-/

namespace Syntax.AstItems

/-- The type of an error that occurred while building an AST. -/
inductive ErrorKind
  /-- Backrefence invalid. -/
  | BackRefenceInvalid
  /-- The capturing group limit was exceeded. -/
  | CaptureLimitExceeded
  /-- An invalid escape sequence was found in a character class set. -/
  | ClassEscapeInvalid
  /-- An invalid character class range was found. -/
  | ClassRangeInvalid
  /-- An invalid range boundary was found in a character class. -/
  | ClassRangeLiteral
  /-- An opening `[` was found with no corresponding closing `]`. -/
  | ClassUnclosed
  /-- An invalid decimal number was given where one was expected. -/
  | DecimalInvalid
  /-- End quote without a corresponding open quote. -/
  | EndQuoteWithoutOpenQuote
  /-- A bracketed hex literal was empty. -/
  | EscapeHexEmpty
  /-- A bracketed hex literal did not correspond to a Unicode scalar value. -/
  | EscapeHexInvalid
  /-- An invalid hexadecimal digit was found. -/
  | EscapeHexInvalidDigit
  /-- EOF was found before an escape sequence was completed. -/
  | EscapeUnexpectedEof
  /-- An unrecognized escape sequence. -/
  | EscapeUnrecognized
  /-- Fixed width in look behind -/
  | FixedWidtExcpected
  /-- A dangling negation was used when setting flags, e.g., `i-`. -/
  | FlagDanglingNegation
  /-- A flag was used twice, e.g., `i-i`. -/
  | FlagDuplicate
  /-- The negation operator was used twice, e.g., `-i-s`. -/
  | FlagRepeatedNegation
  /-- Expected a flag but got EOF, e.g., `(?`. -/
  | FlagUnexpectedEof
  /-- Unrecognized flag, e.g., `a`. -/
  | FlagUnrecognized
  /-- A duplicate capture name was found. -/
  | GroupNameDuplicate
  /-- A capture group name is empty, e.g., `(?P<>abc)`. -/
  | GroupNameEmpty
  /-- An invalid character was seen for a capture group name. -/
  | GroupNameInvalid
  /-- A capture group name is not found of a backreference. -/
  | GroupNameNotFound
  /-- A closing `>` could not be found for a capture group name. -/
  | GroupNameUnexpectedEof
  /-- An unclosed group, e.g., `(ab`. -/
  | GroupUnclosed
  /-- An unopened group, e.g., `ab)`. -/
  | GroupUnopened
  /-- The nest limit was exceeded. -/
  | NestLimitExceeded
  /-- The range provided in a counted repetition operator is invalid. -/
  | RepetitionCountInvalid
  /-- An opening `{` was not followed by a valid decimal value. -/
  | RepetitionCountDecimalEmpty
  /-- An opening `{` was found with no corresponding closing `}`. -/
  | RepetitionCountUnclosed
  /-- A repetition operator was applied to a missing sub-expression. -/
  | RepetitionMissing
  /-- A repetition operator was ungreedy and possessive. -/
  | RepetitionUngreedyAndPossessive
  /-- The special word boundary syntax, `\b{something}`, was used, but
      either EOF without `}` was seen, or an invalid character in the
      braces was seen. -/
  | SpecialWordBoundaryUnclosed
  /-- The special word boundary syntax, `\b{something}`, was used, but
      `something` was not recognized as a valid word boundary kind. -/
  | SpecialWordBoundaryUnrecognized
  /-- The syntax `\b{` was observed, but afterwards the end of the pattern
      was observed without being able to tell whether it was meant to be a
      bounded repetition on the `\b` or the beginning of a special word
      boundary assertion. -/
  | SpecialWordOrRepetitionUnexpectedEof
  /-- The Unicode class is not valid. -/
  | UnicodeClassInvalid
  /-- When octal support is disabled, this error is produced when an octal escape is used. -/
  | UnsupportedBackreference
  /-- When syntax similar to PCRE's look-around is used, this error is returned. -/
  | UnsupportedLookAround
  /-- ClassAsci not found. -/
  | UnkownAsciiClass
  /-- A octal literal did not correspond to a Unicode scalar value. -/
  | EscapeOctalInvalid
  /-- Feature not implemented. -/
  | FeatureNotImplementedSubroutines
  /-- Feature not implemented. -/
  | FeatureNotImplementedFlagShorthand
  /-- Feature not implemented. -/
  | FeatureNotImplementedAtomicGroup
  /-- Feature not implemented. -/
  | FeatureNotImplementedConditionalExpression
  /-- Feature not implemented. -/
  | FeatureNotImplementedBranchResetGroup
  /-- Feature not implemented. -/
  | FeatureNotImplementedControlVerbs
  /-- Feature not implemented. -/
  | FeatureNotImplementedFlagExtended

namespace ErrorKind

def toString : ErrorKind -> String
  | .BackRefenceInvalid => "no capturing group found for backrefence"
  | .CaptureLimitExceeded => "exceeded the maximum number of capturing groups"
  | .ClassEscapeInvalid => "invalid escape sequence found in character class"
  | .ClassRangeInvalid => "invalid character class range, the start must be <= the end"
  | .ClassRangeLiteral => "invalid range boundary, must be a literal"
  | .ClassUnclosed => "unclosed character class"
  | .DecimalInvalid => "decimal literal invalid"
  | .EndQuoteWithoutOpenQuote => "end quote without a corresponding open quote"
  | .EscapeHexEmpty => "hexadecimal literal empty"
  | .EscapeHexInvalid => "hexadecimal literal is not a Unicode scalar value"
  | .EscapeHexInvalidDigit => "invalid hexadecimal digit"
  | .EscapeUnexpectedEof => "incomplete escape sequence, reached end of pattern prematurely"
  | .EscapeUnrecognized => "unrecognized escape sequence"
  | .FixedWidtExcpected => "fixed width expr in look around expected"
  | .FlagDanglingNegation => "dangling flag negation operator"
  | .FlagDuplicate => "duplicate flag"
  | .FlagRepeatedNegation => "flag negation operator repeated"
  | .FlagUnexpectedEof => "expected flag but got end of regex"
  | .FlagUnrecognized => "unrecognized flag"
  | .GroupNameDuplicate => "duplicate capture group name"
  | .GroupNameEmpty => "empty capture group name"
  | .GroupNameInvalid => "invalid capture group character"
  | .GroupNameNotFound => "capture group of backreference not found."
  | .GroupNameUnexpectedEof => "unclosed capture group name"
  | .GroupUnclosed => "unclosed group"
  | .GroupUnopened => "unopened group"
  | .NestLimitExceeded => "exceed the maximum number of nested parentheses/brackets ({})"
  | .RepetitionCountInvalid => "invalid repetition count range, the start must be <= the end"
  | .RepetitionCountDecimalEmpty => "repetition quantifier expects a valid decimal"
  | .RepetitionCountUnclosed => "unclosed counted repetition"
  | .RepetitionMissing => "repetition operator missing expression"
  | .RepetitionUngreedyAndPossessive => "ungreedy and possessive repetition not possible"
  | .SpecialWordBoundaryUnclosed =>
        "special word boundary assertion is either unclosed or contains an invalid character"
  | .SpecialWordBoundaryUnrecognized =>
        "unrecognized special word boundary assertion, "
        ++ "valid choices are: start, end, start-half or end-half"
  | .SpecialWordOrRepetitionUnexpectedEof =>
        "found either the beginning of a special word "
        ++ "boundary or a bounded repetition on a \\b with "
        ++ "an opening brace, but no closing brace"
  | .UnicodeClassInvalid => "invalid Unicode character class"
  | .UnsupportedBackreference => "backreferences are not supported"
  | .UnsupportedLookAround => "look-around, including look-ahead and look-behind, is not supported"
  | .UnkownAsciiClass => "ascii class unkown"
  | .FeatureNotImplementedSubroutines => "feature not implemented: Subroutines"
  | .FeatureNotImplementedFlagShorthand => "feature not implemented: Flag ^"
  | .FeatureNotImplementedAtomicGroup => "feature not implemented: AtomicGroup"
  | .FeatureNotImplementedConditionalExpression => "feature not implemented: ConditionalExpression"
  | .FeatureNotImplementedBranchResetGroup => "feature not implemented: BranchResetGroup"
  | .FeatureNotImplementedControlVerbs => "feature not implemented: ControlVerb"
  | .FeatureNotImplementedFlagExtended => "feature not implemented: Flag x"
  | .EscapeOctalInvalid => "octal value is not a Unicode scalar value"
end ErrorKind

instance : ToString ErrorKind where
  toString := ErrorKind.toString

def toError (s : String) (kind : ErrorKind) (msg : String := "") : String :=
  let msg := if msg.length > 0 then msg ++ " " else msg
  s!"{msg}failed to parse pattern {s}, error: {kind}"

def toErrorAt (s : String) (i : Nat) (kind : ErrorKind) (msg : String := "") : String :=
  let msg := if msg.length > 0 then msg ++ " " else msg
  s!"{msg}failed to parse pattern {s} at {i}, error: {kind}"

/-- The type of a Unicode hex literal. -/
inductive HexLiteralKind where
  /-- A `\x` prefix. When used without brackets, this form is limited to one digit (Pcre flavor). -/
  | x : HexLiteralKind
  /-- A `\x` prefix. When used without brackets, this form is limited to two digits. -/
  | X : HexLiteralKind
  /-- A `\u` prefix. When used without brackets, this form is limited to four digits. -/
  | UnicodeShort : HexLiteralKind

namespace HexLiteralKind

def digits : HexLiteralKind -> Nat
  | .x => 1
  | .X => 2
  | .UnicodeShort => 4

end HexLiteralKind

/-- The kind of a single literal expression. -/
inductive LiteralKind where
  /-- The literal is written verbatim, e.g., `a` or `☃`. -/
  | Verbatim : LiteralKind
  /-- The literal is written as a hex code with a fixed number of digits like '\u0061' -/
  | Hex : HexLiteralKind -> LiteralKind
  /-- The literal is written as a hex code with a bracketed number of digits.
      The only restriction is that the bracketed hex code must refer
      to a valid Unicode scalar value. -/
  | HexBrace : HexLiteralKind -> LiteralKind

namespace LiteralKind

def toString : LiteralKind -> String
  | .Verbatim => "Verbatim"
  | .Hex .x => "Hex x"
  | .Hex .X => "Hex X"
  | .Hex .UnicodeShort => "Hex UnicodeShort"
  | .HexBrace .x => "HexBrace x"
  | .HexBrace .X => "HexBrace X"
  | .HexBrace .UnicodeShort => "HexBrace UnicodeShort"

end LiteralKind

instance : ToString LiteralKind where
  toString := LiteralKind.toString

/-- A single character literal, which includes escape sequences. -/
structure Literal where
  /-- The span of this literal. -/
  span: Substring
  /-- The kind of this literal. -/
  kind: LiteralKind
  /-- The Unicode scalar value corresponding to this literal. -/
  c: Char

def spanToString (span : Substring) : String :=
  s!"({span.str},{span.startPos},{span.stopPos})"

namespace Literal

def toString (lit : Literal) : String :=
  s!"Literal {spanToString lit.span} {lit.kind} '{UInt32.intAsString lit.c.val}'"

def toLiteral (c : Char) (p : String) (f t : String.Pos): Literal :=
  ⟨⟨p, f, t⟩, .Verbatim, c⟩

end Literal

instance : ToString Literal where
  toString := Literal.toString

/-- A backrefence to a capturung group. -/
structure BackRef where
  /-- The span of this backrefence. -/
  span: Substring
  /-- number of the capturung group. -/
  n: Nat

namespace BackRef

def toString (br : BackRef) : String :=
  s!"Backrefence {spanToString br.span} '{br.n}'"

end BackRef

instance : ToString BackRef where
  toString := BackRef.toString

/-- A range repetition operator.-/
inductive RepetitionRange where
  /-- `{m}` -/
  | Exactly : Nat -> RepetitionRange
  /-- `{m,}` -/
  | AtLeast : Nat -> RepetitionRange
  /-- `{m,n}` -/
  | Bounded : Nat -> Nat -> RepetitionRange

namespace RepetitionRange

def toString : RepetitionRange -> String
  | .Exactly n => s!"Exactly {n}"
  | .AtLeast n => s!"AtLeast {n}"
  | .Bounded m n => s!"Bounded {m},{n}"

end RepetitionRange

instance : ToString RepetitionRange where
  toString := RepetitionRange.toString

/-- The kind of a repetition operator.-/
inductive RepetitionKind where
  /-- `?` -/
  | ZeroOrOne
  /-- `*` -/
  | ZeroOrMore
  /-- `+` -/
  | OneOrMore
  | Range : RepetitionRange -> RepetitionKind

namespace RepetitionKind

def toString : RepetitionKind -> String
  | ZeroOrOne => "?"
  | ZeroOrMore => "*"
  | OneOrMore => "+"
  | Range r => s!"Range {r}"

end RepetitionKind

instance : ToString RepetitionKind where
  toString := RepetitionKind.toString

/-- The repetition operator itself. -/
structure RepetitionOp where
  /-- The span of this Repetition . -/
  span: Substring
  /-- The kind of this Repetition . -/
  kind: RepetitionKind

namespace RepetitionOp

def toString (r : RepetitionOp) : String :=
  s!"RepetitionOp {spanToString r.span} {r.kind}"

end RepetitionOp

instance : ToString RepetitionOp where
  toString := RepetitionOp.toString

/-- A single character class range in a set. -/
structure ClassSetRange where
    /-- The span of this range. -/
    span: Substring
    /-- The start of this range. -/
    start: Literal
    /-- The end of this range. -/
    «end»: Literal
    /-- assertion -/
    isLe : start.c ≤ «end».c

namespace ClassSetRange

def toString (r : ClassSetRange) : String :=
  s!"ClassSetRange {spanToString r.span} {r.start} {r.end}"

end ClassSetRange

instance : ToString ClassSetRange where
  toString := ClassSetRange.toString

/-- A single flag. -/
inductive Flag where
    /-- `i` -/
    | CaseInsensitive
    /-- `m` -/
    | MultiLine
    /-- `s` -/
    | DotMatchesNewLine
    /-- `U` -/
    | SwapGreed
    /-- `u` -/
    | Unicode
    /-- `R` -/
    | CRLF
    /-- `x` -/
    | Extended

instance : ToString Flag where
  toString s := match s with
    | .CaseInsensitive => "CaseInsensitive"
    | .MultiLine => "MultiLine"
    | .DotMatchesNewLine => "DotMatchesNewLine"
    | .SwapGreed => "SwapGreed"
    | .Unicode => "Unicode"
    | .CRLF => "CRLF"
    | .Extended => "Extended"

/-- The kind of an item in a group of flags. -/
inductive FlagsItemKind where
    /-- A negation operator applied to all subsequent flags in the enclosing group. -/
    | Negation
    /-- A single flag in a group. -/
    | Flag : Flag -> FlagsItemKind

instance : ToString FlagsItemKind where
  toString s := match s with
    | .Negation => "Negation"
    | .Flag f => s!"{f}"

/-- A single item in a group of flags. -/
structure FlagsItem where
    /-- The span of this item. -/
    span: Substring
    /-- The kind of this item. -/
    kind: FlagsItemKind

instance : ToString FlagsItem where
  toString s :=
    let  ⟨_, kind⟩ := s
    s!"{kind}"

/-- A group of flags.-/
structure Flags where
    /-- The span of this item. -/
    span: Substring
    /-- The kind of this item. -/
    items: Array FlagsItem

instance : ToString Flags where
  toString flags := s!"Flags {flags.items}"

/-- The kind of a Lookaround. -/
inductive LookaroundKind where
  | PositiveLookahead : LookaroundKind
  | NegativeLookahead : LookaroundKind
  | PositiveLookbehind : Nat -> LookaroundKind
  | NegativeLookbehind : Nat -> LookaroundKind

instance : ToString LookaroundKind where
  toString look :=
    match look with
    |.PositiveLookahead => "PositiveLookahead"
    |.NegativeLookahead => "NegativeLookahead"
    |.PositiveLookbehind i => s!"PositiveLookbehind Length {i}"
    |.NegativeLookbehind i => s!"NegativeLookbehind Length {i}"

/-- The kind of a group. -/
inductive GroupKind where
  | CaptureIndex : Nat -> Option String -> GroupKind
  | NonCapturing : Flags -> GroupKind
  | Lookaround : LookaroundKind -> GroupKind

namespace GroupKind

def toString : GroupKind -> String
  | .CaptureIndex i s => s!"CaptureIndex {i} name {s}"
  | .NonCapturing flags => s!"NonCapturing {flags}"
  | .Lookaround kind => s!"Lookaround {kind}"

end GroupKind

instance : ToString GroupKind where
  toString := GroupKind.toString

/-- The type of op used in a Unicode character class. -/
inductive ClassUnicodeOpKind where
  | Equal : ClassUnicodeOpKind

instance : ToString ClassUnicodeOpKind where
  toString v :=
    match v with
    | .Equal => "Equal"

/-- The available forms of Unicode character classes. -/
inductive ClassUnicodeKind where
    /-- A one letter abbreviated class, e.g., `\pN`. -/
    | OneLetter : Char -> ClassUnicodeKind
    /-- A binary property, general category or script. The string may be empty. -/
    | Named : String -> ClassUnicodeKind
    /--  A property name and an associated value.-/
    | NamedValue : (op : ClassUnicodeOpKind) -> (n : String) -> (v : String) -> ClassUnicodeKind
namespace ClassUnicodeKind

def toString : ClassUnicodeKind -> String
  | .OneLetter c => s!"OneLetter '{c}'"
  | .Named s => s!"Named '{s}'"
  | .NamedValue op n v => s!"NamedValue {op} {n} {v}"

end ClassUnicodeKind

instance : ToString ClassUnicodeKind where
  toString := ClassUnicodeKind.toString

/-- A Unicode character class. -/
structure ClassUnicode where
  /-- The span of this class. -/
  span : Substring
  /-- is class negated. -/
  negated : Bool
  /-- The kind of Unicode class. -/
  kind : ClassUnicodeKind

instance : ToString ClassUnicode where
  toString cls := s!"{spanToString cls.span} {cls.negated} {cls.kind}"

/-- An assertion kind. -/
inductive AssertionKind where
  /-- `^` -/
  | StartLine : AssertionKind
  /-- `$` -/
  | EndLine : AssertionKind
  /-- `$` pcre flavor -/
  | EndLineWithOptionalLF : AssertionKind
  /-- `\A` -/
  | StartText : AssertionKind
  /-- `\z` -/
  | EndText : AssertionKind
  /-- `\Z` pcre flavor -/
  | EndTextWithOptionalLF : AssertionKind
  /-- \b -/
  | WordBoundary : AssertionKind
  /-- \B -/
  | NotWordBoundary : AssertionKind
  /-- `\b{start}` -/
  | WordBoundaryStart : AssertionKind
  /-- `\b{end}` -/
  |  WordBoundaryEnd : AssertionKind
  /-- `\b{start-half}` -/
  | WordBoundaryStartHalf : AssertionKind
  /-- `\b{end-half}` -/
  |  WordBoundaryEndHalf : AssertionKind
  /-- \G -/
  | PreviousMatch : AssertionKind
  /-- \K -/
  | ClearMatches : AssertionKind

namespace AssertionKind

def toString : AssertionKind -> String
  | .StartLine => s!"StartLine"
  | .EndLine => s!"EndLine"
  | .EndLineWithOptionalLF => s!"EndLineWithOptionalLF"
  | .StartText => s!"StartText"
  | .EndText => s!"EndText"
  | .EndTextWithOptionalLF => s!"EndTextWithOptionalLF"
  | .WordBoundary => s!"WordBoundary"
  | .NotWordBoundary => s!"NotWordBoundary"
  | .WordBoundaryStart => s!"WordBoundaryStart"
  | .WordBoundaryEnd => s!"WordBoundaryEnd"
  | .WordBoundaryStartHalf => s!"WordBoundaryStartHalf"
  | .WordBoundaryEndHalf => s!"WordBoundaryEndHalf"
  | .PreviousMatch => s!"PreviousMatch"
  | .ClearMatches => s!"ClearMatches"

end AssertionKind

instance : ToString AssertionKind where
  toString := AssertionKind.toString

/-- A single zero-width assertion. -/
structure Assertion where
  /-- The span of this assertion. -/
  span : Substring
  /-- The assertion kind. -/
  kind : AssertionKind

instance : ToString Assertion where
  toString a := s!"{spanToString a.span} {a.kind}"

/-- The available ASCII character classes. -/
inductive ClassAsciiKind where
    /-- `[0-9A-Za-z]` -/
    | Alnum
    /-- `[A-Za-z]` -/
    | Alpha
    /-- `[\x00-\x7F]` -/
    | Ascii
    /-- `[ \t]` -/
    | Blank
    /-- `[\x00-\x1F\x7F]` -/
    | Cntrl
    /-- `[0-9]` -/
    | Digit
    /-- `[!-~]` -/
    | Graph
    /-- `[a-z]` -/
    | Lower
    /-- `[ -~]` -/
    | Print
    /-- ...  -/
    | Punct
    /-- `[\t\n\v\f\r ]` -/
    | Space
    /-- `[A-Z]` -/
    | Upper
    /-- `[0-9A-Za-z_]` -/
    | Word
    /-- `[0-9A-Fa-f]` -/
    | Xdigit

instance : ToString ClassAsciiKind where
  toString k :=
  match k with
  | .Alnum => "Alnum"
  | .Alpha => "Alpha"
  | .Ascii => "Ascii"
  | .Blank => "Blank"
  | .Cntrl => "Cntrl"
  | .Digit => "Digit"
  | .Graph => "Graph"
  | .Lower => "Lower"
  | .Print => "Print"
  | .Punct => "Punct"
  | .Space => "Space"
  | .Upper => "Upper"
  | .Word => "Word"
  | .Xdigit => "Xdigit"

namespace ClassAsciiKind

def from_name (name: String) : Option ClassAsciiKind :=
  match name.toLower with
  | "alnum" => some ClassAsciiKind.Alnum
  | "alpha" => some ClassAsciiKind.Alpha
  | "ascii" => some ClassAsciiKind.Ascii
  | "blank" => some ClassAsciiKind.Blank
  | "cntrl" => some ClassAsciiKind.Cntrl
  | "digit" => some ClassAsciiKind.Digit
  | "graph" => some ClassAsciiKind.Graph
  | "lower" => some ClassAsciiKind.Lower
  | "print" => some ClassAsciiKind.Print
  | "punct" => some ClassAsciiKind.Punct
  | "space" => some ClassAsciiKind.Space
  | "upper" => some ClassAsciiKind.Upper
  | "word" => some ClassAsciiKind.Word
  | "xdigit" => some ClassAsciiKind.Xdigit
  | _ => none

end ClassAsciiKind

/-- An ASCII character class. -/
structure ClassAscii where
  /-- The span of this assertion. -/
  span : Substring
  /-- The kind of ASCII class. -/
  kind : ClassAsciiKind
  /-- Whether the class is negated or not -/
  negated : Bool

instance : ToString ClassAscii where
  toString cls :=
    let ⟨_, k, n⟩ := cls
    s!"ClassAscii {k} negated {n}"

/-- The available Perl character classes. -/
inductive ClassPerlKind where
  /-- Decimal numbers. -/
  | Digit
  /-- Whitespace. -/
  | Space
  /-- Word characters. -/
  | Word
  /-- Newline. -/
  | Newline
  /-- Whitespace. -/
  | VerticalSpace
  /-- Whitespace. -/
  | HorizontalSpace

instance : ToString ClassPerlKind where
  toString k :=
  match k with
  | .Digit => "Digit"
  | .Space => "Space"
  | .Word => "Word"
  | .Newline => "Newline"
  | .VerticalSpace => "VerticalSpace"
  | .HorizontalSpace => "HorizontalSpace"

/--A Perl character class.-/
structure ClassPerl where
  /-- The span of this assertion. -/
  span : Substring
  /-- The kind of Perl class. -/
  kind : ClassPerlKind
  /-- Whether the class is negated or not -/
  negated : Bool

instance : ToString ClassPerl where
  toString cls :=
    let ⟨_, k, n⟩ := cls
    s!"ClassPerl {k} negated {n}"

mutual

/-- A repetition operation applied to a regular expression. -/
inductive Repetition where
  | mk (span: Substring) (op: RepetitionOp) (greedy : Bool) (possessive : Bool) (ast: Ast) : Repetition

/-- A grouped regular expression. -/
inductive Group where
  | mk (span: Substring) (kind: GroupKind) (ast: Ast) : Group

/-- A group of flags that is not applied to a particular regular expression. -/
inductive SetFlags where
  | mk (span: Substring) (flags: Flags) : SetFlags

/-- A primitive is an expression with no sub-expressions. -/
inductive Primitive where
  | Literal : AstItems.Literal -> Primitive
  | BackRef : AstItems.BackRef -> Primitive
  | Dot : Substring -> Primitive
  | Assertion : Assertion -> Primitive
  | Unicode : ClassUnicode -> Primitive
  | Perl : ClassPerl -> Primitive

/-- A union of items inside a character class set. -/
inductive ClassSetUnion where
  | mk (span : Substring) (items : Array ClassSetItem) : ClassSetUnion

/-- A single component of a character class set. -/
inductive ClassSetItem where
  /-- An empty item. -/
  | Empty : Substring -> ClassSetItem
  /-- A single literal. -/
  | Literal : Literal -> ClassSetItem
  /-- A range between two literals. -/
  | Range : ClassSetRange -> ClassSetItem
  /--  An ASCII character class, e.g., `[:alnum:]` or `[:punct:]`. -/
  | Ascii : ClassAscii -> ClassSetItem
  /-- A Unicode character class, e.g., `\pL` or `\p{Greek}`. -/
  | Unicode: ClassUnicode -> ClassSetItem
  /-- A perl character class, e.g., `\d` or `\W`. -/
  | Perl : ClassPerl -> ClassSetItem
  /-- A bracketed character class set, which may contain zero or more character ranges
      and/or zero or more nested classes. e.g., `[a-zA-Z\pL]`.-/
  | Bracketed : ClassBracketed -> ClassSetItem
  /-- A union of items. -/
  | Union : ClassSetUnion -> ClassSetItem

/-- The type of a Unicode character class set operation. -/
inductive ClassSetBinaryOpKind where
  /-- The intersection of two sets, e.g., `\pN&&[a-z]`. -/
  | Intersection : ClassSetBinaryOpKind
  /-- The difference of two sets, e.g., `\pN--[0-9]`. -/
  | Difference : ClassSetBinaryOpKind
  /-- The symmetric difference of two sets. The symmetric difference is the
      set of elements belonging to one but not both sets.-/
  | SymmetricDifference : ClassSetBinaryOpKind

/-- A Unicode character class set operation. -/
inductive ClassSetBinaryOp where
  | mk (span : Substring) (kind: ClassSetBinaryOpKind) (lhs: ClassSet) (rhs: ClassSet)
    : ClassSetBinaryOp

/-- A character class set. -/
inductive ClassSet where
  /-- An item, which can be a single literal, range, nested character class or a union of items.-/
  | Item : ClassSetItem -> ClassSet
  /-- A single binary operation (i.e., &&, -- or ~~). -/
  | BinaryOp : ClassSetBinaryOp -> ClassSet

/-- A bracketed character class, e.g., `[a-z0-9]`.-/
inductive ClassBracketed where
  | mk : (span: Substring) -> (negated : Bool) -> (kind: ClassSet) -> ClassBracketed

/-- An alternation of regular expressions. -/
inductive Alternation where
  | mk (span: Substring) (asts: Array Ast) : Alternation

/-- A concatenation of regular expressions. -/
inductive Concat where
  | mk (span: Substring) (asts: Array Ast) : Concat

/-- An abstract syntax tree for a single regular expression. -/
inductive Ast where
  /-- An empty regex that matches everything. -/
  | Empty : Ast
  /-- A set of flags, e.g., `(?is)`. -/
  | Flags : SetFlags -> Ast
  /-- A single character literal, which includes escape sequences. -/
  | Literal : Literal -> Ast
  /-- A backrefence to a capturung group. -/
  | BackRef : BackRef -> Ast
  /-- The "any character" class. -/
  | Dot : Substring -> Ast
  /-- A single zero-width assertion. -/
  | Assertion : Assertion -> Ast
  /-- A single Unicode character class, e.g., `\pL` or `\p{Greek}`. -/
  | ClassUnicode : ClassUnicode -> Ast
  /-- A single perl character class, e.g., `\d` or `\W`. -/
  | ClassPerl : ClassPerl -> Ast
  /-- A single bracketed character class set, which may contain zero or more character range. -/
  | ClassBracketed : ClassBracketed -> Ast
  /-- A repetition operator applied to an arbitrary regular expression. -/
  | Repetition : Repetition -> Ast
  /-- An alternation of regular expressions. -/
  | Alternation : Alternation -> Ast
  /-- A grouped regular expression. -/
  | Group : Group -> Ast
  /-- A concatenation of regular expressions. -/
  | Concat : Concat -> Ast

end

instance : Inhabited Ast  := ⟨.Empty⟩

namespace ClassSetUnion

def items (union : ClassSetUnion) : Array ClassSetItem :=
  let ⟨_, items⟩ := union
  items

/-- Return this union as a character class set item. -/
def into_item (union : ClassSetUnion) : ClassSetItem :=
  let ⟨span, items⟩ := union
  match items.size with
  | 0 => ClassSetItem.Empty span
  | 1 => if h: 0 < items.size then items[0]'h else ClassSetItem.Empty span
  | _ => ClassSetItem.Union union

end ClassSetUnion

namespace ClassBracketed

def span (cls : ClassBracketed) : Substring := match cls with | .mk span _ _ => span

def negate (cls : ClassBracketed) : Bool := match cls with | .mk _ negate _ => negate

end ClassBracketed

namespace Concat

def span (concat : Concat) : Substring := match concat with | .mk span _ => span

def asts (concat : Concat) : Array Ast := match concat with | .mk _ asts => asts

theorem sizeOfAstsOfConcat (concat : Concat) : sizeOf concat.asts < sizeOf concat := by
  unfold Syntax.AstItems.Concat.asts
  split <;> simp_all; omega

def into_ast (concat : Concat) : Ast :=
  match concat.asts.size with
  | 0 => Ast.Empty
  | 1 => concat.asts[0]!
  | _ => Ast.Concat concat

end Concat

namespace Alternation

def asts (concat : Alternation) : Array Ast := match concat with | .mk _ asts => asts

theorem sizeOfAstsOfAlternation (alt : Alternation) : sizeOf alt.asts < sizeOf alt := by
  unfold Syntax.AstItems.Alternation.asts
  split <;> simp_all; omega

def into_ast (alt : Alternation) : Ast :=
  let ⟨_, asts⟩ := alt
  match asts.size with
  | 0 => Ast.Empty
  | 1 => asts[0]!
  | _ => Ast.Alternation alt

end Alternation

namespace Primitive

def into_ast (p : Primitive) : Ast :=
  match p with
  | .Literal lit => Ast.Literal lit
  | .BackRef n => Ast.BackRef n
  | .Dot span => Ast.Dot span
  | .Assertion a => Ast.Assertion a
  | .Unicode cls => Ast.ClassUnicode cls
  | .Perl cls => Ast.ClassPerl cls

def into_class_set_item (p : Primitive) : Except String ClassSetItem :=
  match p with
  | .Literal lit => Except.ok (ClassSetItem.Literal lit)
  | .Perl cls => Except.ok (ClassSetItem.Perl cls)
  | .Unicode cls => Except.ok (ClassSetItem.Unicode cls)
  | _ => Except.error "into_class_set_item, unexpected entry"

def into_class_literal (p : Primitive) : Except String Syntax.AstItems.Literal :=
  match p with
  | .Literal lit => Except.ok lit
  | .Perl _ => Except.error "escape sequence unexpected in range"
  | _ => Except.error "into_class_literal, unexpected entry"

end Primitive

namespace Group

def kind (g : Group) : GroupKind := match g with | .mk _ kind _ => kind

def ast (g : Group) : Ast := match g with | .mk _ _ ast => ast

theorem sizeOfAstOfGroup (g : Group) : sizeOf g.ast < sizeOf g := by
  unfold Syntax.AstItems.Group.ast
  split <;> simp_all; omega

end Group

namespace ClassSetBinaryOp

def kind (cls : ClassSetBinaryOp) : ClassSetBinaryOpKind := match cls with | .mk _ kind _ _ => kind

end ClassSetBinaryOp

instance : ToString SetFlags where
  toString s :=
    let ⟨_, flags⟩ := s
    s!"{flags}"

namespace ClassSetItem

mutual

def toStringClassSetUnion (r : ClassSetUnion) (col : Nat) : String :=
  let col := col + 2
  let pre := "\n" ++ (Char.multiple ' ' col "")

  let ⟨_, items⟩ := r
  let lines :=
      let asts := Array.mapFinIdx items.attach (fun i s _ => (i, s))
      let asts := String.join (asts.toList |> List.map (fun (i, ast) =>
          let iv := String.mk (Nat.toDigits 0 i)
          have : sizeOf ast.val < sizeOf items := Array.sizeOf_lt_of_mem ast.property
          pre ++ iv ++ ": " ++ (toStringClassSetItem ast col)))
      s!"ClassSetUnion {asts}"

  s!"{pre}{lines}"
termination_by sizeOf r

def toStringClassSetItem (r : ClassSetItem) (col : Nat) : String :=
  match r with
  | .Empty _ => s!"ItemEmpty"
  | .Literal lit => s!"Item {lit}"
  | .Range range => s!"Item {range}"
  | .Ascii cls => s!"Item {cls}"
  | .Perl cls => s!"Item {cls}"
  | .Unicode cls => s!"Item {cls}"
  | .Bracketed ⟨_, neg, cls⟩ =>
      match cls with
      | .Item item => s!"Bracketed Item {neg} {ClassSetItem.toStringClassSetItem item col}"
      | .BinaryOp ⟨_, kind, lhs, rhs⟩ =>
        let kind :=
            match kind with
            | .Intersection => s!"Intersection"
            | .Difference => s!"Difference"
            | .SymmetricDifference => s!"SymmetricDifference"
        s!"Item Bracketed BinaryOp {neg} {kind}"
  | .Union union => s!"Item Union {toStringClassSetUnion union col}"
termination_by sizeOf r

end

end ClassSetItem

instance : ToString ClassSetUnion where
  toString union := ClassSetItem.toStringClassSetUnion union 0

instance : ToString ClassSetItem where
  toString item := ClassSetItem.toStringClassSetItem item 0

namespace ClassSetBinaryOpKind

def toString (r : ClassSetBinaryOpKind) : String :=
  match r with
  | .Intersection => s!"Intersection"
  | .Difference => s!"Difference"
  | .SymmetricDifference => s!"SymmetricDifference"

end ClassSetBinaryOpKind

namespace ClassSet

def toString (r : ClassSet) (col : Nat) : String :=
  let col := col + 2
  let pre := "\n" ++ (Char.multiple ' ' col "")

  match r with
  | .Item item => s!"ClassSet {ClassSetItem.toStringClassSetItem item col}"
  | .BinaryOp ⟨_, kind, lhs, rhs⟩ =>
      let op := s!"BinaryOp {ClassSetBinaryOpKind.toString kind}"
      let lhs := s!"lhs {ClassSet.toString lhs col}"
      let rhs := s!"rhs {ClassSet.toString rhs col}"
      s!"ClassSet {op}{pre}{lhs}{pre}{rhs}"

end ClassSet

instance : ToString ClassSet where
  toString s := ClassSet.toString s 0

namespace Repetition

def op (rep : Repetition) : RepetitionOp := match rep with | .mk _ op _ _ _ => op

def greedy (rep : Repetition) : Bool := match rep with | .mk _ _ greedy _ _ => greedy

def possessive (rep : Repetition) : Bool := match rep with | .mk _ _ _ possessive _ => possessive

def ast (rep : Repetition) : Ast := match rep with | .mk _ _ _ _ ast => ast

theorem sizeOfAstOfRepetition (rep : Repetition) : sizeOf rep.ast < sizeOf rep := by
  unfold Syntax.AstItems.Repetition.ast
  split <;> simp_all

end Repetition

def span (ast : Ast) : Substring :=
  match ast with
  | .Empty => default
  | .Flags ⟨span, _⟩  => span
  | .Literal lit => lit.span
  | .BackRef br => br.span
  | .Dot span => span
  | .Assertion ⟨span, _⟩ => span
  | .ClassUnicode cls => cls.span
  | .ClassPerl cls => cls.span
  | .ClassBracketed ⟨span, _, _⟩ => span
  | .Repetition ⟨span, _, _, _, _⟩ => span
  | .Alternation ⟨span, _⟩ => span
  | .Group ⟨span, _, _⟩ => span
  | .Concat concat => concat.span

def toString (ast : Ast) (col : Nat) : String :=
  let col := col + 2
  let pre := "\n" ++ (Char.multiple ' ' col "")
  match ast with
  | .Empty => s!"Empty"
  | .Flags ⟨_, flags⟩  => s!"Flags {flags}"
  | .Literal lit => s!"{lit}"
  | .BackRef br => s!"{br}"
  | .Dot span => s!"Dot {spanToString span}"
  | .Assertion a => s!"Assertion {a}"
  | .ClassUnicode cls => s!"ClassUnicode {cls}"
  | .ClassPerl cls => s!"ClassPerl {cls}"
  | .ClassBracketed ⟨_, negated, cls⟩  =>
      s!"ClassBracketed negated {negated}{pre}{ClassSet.toString cls col}"
  | .Repetition rep =>
    match rep with
    | .mk _ op greedy possessive ast => s!"Repetition{pre}{op} possessive {possessive} greedy {greedy}{pre}{toString ast col}"
  | .Alternation alt =>
    match alt with
    | .mk _ items =>
      let asts : Array (Fin items.attach.size ×  { x // x ∈ items }) :=
        Array.mapFinIdx items.attach (fun i s h => (⟨i, h⟩, s))
      let asts := String.join (asts.toList |> List.map (fun (i, ast) =>
          let iv := String.mk (Nat.toDigits 0 i.val)
          have : sizeOf ast.val < sizeOf items := Array.sizeOf_lt_of_mem ast.property
          pre ++ iv ++ ": " ++ (toString ast col)))
      s!"Alternation {asts}"
  | .Group g =>
    match g with
    | .mk _ kind ast => s!"Group{pre}{kind}{pre}{toString ast col}"
  | .Concat concat =>
      let asts : Array (Fin concat.asts.attach.size ×  { x // x ∈ concat.asts })
        := Array.mapFinIdx concat.asts.attach (fun i s h => (⟨i, h⟩, s))
      let asts := String.join (asts.toList |> List.map (fun (i, ast) =>
          let iv := String.mk (Nat.toDigits 0 i.val)
          have : sizeOf ast.val < sizeOf concat :=
            Nat.lt_trans (Array.sizeOf_lt_of_mem ast.property) (Concat.sizeOfAstsOfConcat concat)
          pre ++ iv ++ ": " ++ (toString ast col)))
      s!"Concat {asts}"
termination_by sizeOf ast

instance : ToString Ast where
  toString ast := AstItems.toString ast 0

def find (ast : Ast) (p : Ast -> Bool) : Option Ast :=
  if p ast then some ast else
    match ast with
    | .Repetition rep => match rep with | .mk _ _ _ _ item => find item p
    | .Alternation alt =>
      match alt with | .mk _ items => (items |> Array.filterMap  (fun item => find item p))[0]?
    | .Group grp => match grp with | .mk _ _ item => find item p
    | .Concat concat =>
      match concat with | .mk _ items => (items |> Array.filterMap  (fun item => find item p))[0]?
    | _ => none
termination_by sizeOf ast

def get_fixed_width (pattern : String) (ast : Ast) : Except String Nat := do
  match ast with
  | .Literal _ => pure 1
  | .Dot _ => pure 1
  | .ClassBracketed _ => pure 1
  | .ClassUnicode _ => pure 1
  | .ClassPerl _ => pure 1
  | .Assertion _ => pure 0
  | .Flags _ => pure 0
  | .Concat concat =>
      match concat with
      | ⟨_, asts⟩ =>
        let width ← asts.attach.foldlM (init := 0) (fun s (ast : { x // x ∈ asts}) => do
            have : sizeOf ast.val < sizeOf asts := Array.sizeOf_lt_of_mem ast.property
            let width ← get_fixed_width pattern ast.val
            pure (s + width))
        pure width
  | .Alternation alt =>
      match alt with
      | ⟨_, asts⟩ =>
        let widths ← asts.attach.mapM (fun (ast : { x // x ∈ asts}) => do
            have : sizeOf ast.val < sizeOf asts := Array.sizeOf_lt_of_mem ast.property
            let width ← get_fixed_width pattern ast.val
            pure width)
        if h : 0 < widths.size
        then
          let width := widths[0]'h
          if Array.all widths (fun w => w = width)
          then pure width
          else throw (toError pattern .FixedWidtExcpected)
        else throw (toError pattern .FixedWidtExcpected)
  | .Repetition rep  =>
      match rep with
      | AstItems.Repetition.mk _ (RepetitionOp.mk _ (.Range (.Exactly n))) _ _ _ => pure n
      | _ => throw (toError pattern .FixedWidtExcpected)
  | .Group ⟨_, GroupKind.CaptureIndex _ _, ast⟩  =>
        let width ← get_fixed_width pattern ast
        pure width
  | .Group ⟨_, GroupKind.Lookaround _, _⟩  =>
        pure 0
  | _ => throw (toError pattern .FixedWidtExcpected)
termination_by sizeOf ast

def checkBackRefence (b : Nat) (ast: Ast) : Except String Bool := do
  let check (ast : Ast) :=
    match ast with
    | .Group ⟨_, AstItems.GroupKind.CaptureIndex b' _, _⟩ => b = b'
    | _ => false

  match AstItems.find ast check with
  | some ast =>
      match get_fixed_width "" ast with
      | Except.ok _ => pure true
      | Except.error _ => Except.error s!"fixed width capture group of backreference {b} expected"
  | none => Except.error s!"capture group {b} not found"

/-- capture groups with a backreference should have fixed width -/
def checkBackRefences (b : Nat) (ast: Ast) : Except String Bool := do
  if b = 0 then pure true
  else
    if ← checkBackRefence b ast then checkBackRefences (b - 1) ast else pure false
