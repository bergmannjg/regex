import Regex.Syntax.Ast.Ast
import Regex.Syntax.Ast.Parse
import Regex.Syntax.Ast.Visitor
import Regex.Syntax.Hir
import Regex.Utils
import Regex.Unicode
import Regex.Data.Char.Basic

import UnicodeBasic

/-!
## Translate

Translate (`Syntax.translate`) an abstract syntax tree `Syntax.Ast.Ast`
into a high level intermediate representation `Syntax.Hir`.
-/

namespace Syntax

open AstItems

/-- Translator state -/
structure Translator where
  /--  Our call stack, but on the heap. -/
  stack : Array HirFrame
  /-- The current flag settings. -/
  flags : Flags

namespace Flags

def is_case_insensitive (f : Flags) : Bool :=
  f.case_insensitive.getD false

def is_dot_matches_new_line (f : Flags) : Bool :=
  f.dot_matches_new_line.getD false

def is_multi_line (f : Flags) : Bool :=
  f.multi_line.getD false

def is_crlf (f : Flags) : Bool :=
  f.crlf.getD false

def is_swap_greed (f : Flags) : Bool :=
  f.swap_greed.getD false

private def from_ast (ast: Syntax.AstItems.Flags) : Syntax.Flags :=
  let init : Bool × Syntax.Flags := (true, default)
  let (_, flags) := ast.items |> Array.foldl (init := init)
    (fun (enabled, acc) f =>
    match f.kind with
    | .Negation => (false, acc)
    | .Flag Flag.IgnoreWhitespace => (enabled, acc)
    | .Flag  Flag.CRLF => (enabled, {acc with crlf := enabled})
    | .Flag Flag.Unicode => (enabled, acc)
    | .Flag Flag.SwapGreed => (enabled, {acc with swap_greed := enabled})
    | .Flag Flag.DotMatchesNewLine => (enabled, {acc with dot_matches_new_line := enabled})
    | .Flag Flag.MultiLine => (enabled, {acc with multi_line := enabled})
    | .Flag Flag.CaseInsensitive => (enabled, {acc with case_insensitive := enabled}))
  flags

private def merge (flags previous : Syntax.Flags) : Syntax.Flags :=
  let setIfNone (o : Option Bool) (v : Option Bool) : Option Bool := if o.isNone then v else o
  let flags := { flags with
        case_insensitive := setIfNone flags.case_insensitive previous.case_insensitive}
  let flags := { flags with
        multi_line := setIfNone flags.multi_line previous.multi_line}
  let flags := { flags with
        dot_matches_new_line := setIfNone flags.dot_matches_new_line previous.dot_matches_new_line}
  let flags := { flags with
        swap_greed := setIfNone flags.swap_greed previous.swap_greed}
  let flags := { flags with
        crlf := setIfNone flags.crlf previous.crlf}

  flags

end Flags

/-- Set the flags of this translator from the flags set in the given AST.-/
private def set_flags (ast_flags : Syntax.AstItems.Flags) (t : Translator) : Translator :=
  {t with flags := Flags.merge (Flags.from_ast ast_flags) t.flags}

/-- Convert an Ast literal to its scalar representation. -/
private def ast_literal_to_scalar (lit: AstItems.Literal) : Except String Char :=
  Except.ok lit.c

private def push_char (c : Char) (stack : Array HirFrame) : Array HirFrame :=
  stack.push (HirFrame.Literal c)

private def unicode_fold_and_negate (ranges : Array ClassUnicodeRange) (flags : Flags) (negate : Bool)
    : ClassUnicode :=
  let cls : ClassUnicode := ⟨IntervalSet.canonicalize ranges⟩
  let cls := if flags.is_case_insensitive then ClassUnicode.case_fold cls else cls
  if negate then ClassUnicode.negate cls else cls

private def hir_repetition (r : AstItems.Repetition) (expr: Hir) (flags : Flags): Hir :=
  let (min, max) :=
    match r.op.kind with
    | .ZeroOrOne => (0, some 1)
    | .ZeroOrMore => (0, none)
    | .OneOrMore => (1, none)
    | .Range (.Exactly n) => (n, some n)
    | .Range (.AtLeast n) => (n, none)
    | .Range (.Bounded m n) => (m, some n)

  if min = 0 && match max with | some 0 => true | _ => false
  then Hir.mk HirKind.Empty default
  else
    let greedy := if flags.is_swap_greed then !r.greedy else r.greedy
    let rep : Syntax.Repetition := Syntax.Repetition.mk min max greedy r.possessive expr
    Hir.mk (HirKind.Repetition rep) default

private def hir_dot (flags : Flags) : Hir :=
  if flags.is_dot_matches_new_line then Syntax.dot (Dot.AnyChar)
  else if flags.is_crlf then Syntax.dot (Dot.AnyCharExceptCRLF)
  else Syntax.dot (Dot.AnyCharExceptLF)

private def range_of_category (category : String) : Except String $ Array ClassUnicodeRange := do
  let pairs ← Unicode.rangesOfProperty category
  Except.ok pairs

private def range_of_general_category (category : Unicode.GeneralCategory)
    : Except String $ Array ClassUnicodeRange := do
  let pairs ← Unicode.rangesOfGeneralCategory category
  Except.ok pairs

private def range_of_property (property : String) : Except String $ Array ClassUnicodeRange := do
  let pairs ← Unicode.rangesOfProperty property
  Except.ok pairs

private def range_of_named_property (name property : String)
    : Except String $ Array ClassUnicodeRange := do
  let pairs ← Unicode.rangesOfNamedProperty name property
  Except.ok pairs

private def hir_unicode_class (cls : AstItems.ClassUnicode) (flags : Flags)
    : Except String ClassUnicode := do
  let range ←
    match cls.kind with
    | .OneLetter c =>
        let range ← range_of_category c.toString
        Except.ok (unicode_fold_and_negate range flags cls.negated)
    | .Named s =>
      let range ← range_of_category s
      Except.ok (unicode_fold_and_negate range flags cls.negated)
    | .NamedValue _ n s =>
      let range ← range_of_named_property n s
      Except.ok (unicode_fold_and_negate range flags cls.negated)

private def hir_perl_unicode_class (cls : AstItems.ClassPerl) (flags : Flags)
    : Except String ClassUnicode := do
  match cls.kind with
  | .Digit =>
    let range : Array ClassUnicodeRange ← range_of_general_category Unicode.GeneralCategory.Nd
    Except.ok (unicode_fold_and_negate range flags cls.negated)
  | .Space =>
    let range : Array ClassUnicodeRange ← range_of_property "White_Space"
    Except.ok (unicode_fold_and_negate range flags cls.negated)
  | .VerticalSpace =>
    let range1 : Array ClassUnicodeRange ← range_of_property "White_Space"
    let range2 : Array ClassUnicodeRange :=
      #[⟨⟨'\u0009', '\u0009'⟩, by simp_arith⟩, ⟨⟨'\u0020', '\u0020'⟩, by simp_arith⟩, ⟨⟨'\u00a0', '\u00a0'⟩, by simp_arith⟩]
    let is1 : IntervalSet Char := IntervalSet.canonicalize range1
    let is2 : IntervalSet Char := IntervalSet.canonicalize range2
    let diff := IntervalSet.difference is1 is2
    Except.ok (if cls.negated then ⟨IntervalSet.negate diff⟩ else ⟨diff⟩)
  | .HorizontalSpace =>
    let rangea : Array ClassUnicodeRange ← range_of_property "White_Space"
    let rangeb : Array ClassUnicodeRange := #[⟨⟨'\u00a0', '\u00a0'⟩, by simp_arith⟩]
    let range1 : Array ClassUnicodeRange := rangea ++ rangeb
    let range2 : Array ClassUnicodeRange := #[⟨⟨'\u000a', '\u000a'⟩, by simp_arith⟩]
    let is1 : IntervalSet Char := IntervalSet.canonicalize range1
    let is2 : IntervalSet Char := IntervalSet.canonicalize range2
    let diff := IntervalSet.difference is1 is2
    Except.ok (if cls.negated then ⟨IntervalSet.negate diff⟩ else ⟨diff⟩)
  | .Word =>
    let range : Array ClassUnicodeRange := ← range_of_property "Word"
    Except.ok (unicode_fold_and_negate range flags cls.negated)
  | .Newline =>
    if cls.negated then
      let range1 : ClassUnicodeRange := ⟨⟨'\u0000', '\u0009'⟩, by simp_arith⟩
      let range2 : ClassUnicodeRange := ⟨⟨'\u000B', ⟨0xD7FF, by simp_arith⟩⟩, by simp_arith⟩
      let range3 : ClassUnicodeRange := ⟨⟨⟨0xE000, by simp_arith⟩, ⟨0x10FFFF, by simp_arith⟩⟩, by simp_arith⟩
      Except.ok ⟨IntervalSet.canonicalize #[range1, range2, range3]⟩
    else
      let range1 : ClassUnicodeRange := ⟨⟨'\u000a', '\u000b'⟩, by simp_arith⟩
      Except.ok ⟨IntervalSet.canonicalize #[range1]⟩

private def hir_ascii_unicode_class (cls: AstItems.ClassAscii) (flags : Flags)
    : Except String ClassUnicode := do
  let range : Array ClassUnicodeRange :=
    match cls.kind with
    | .Alnum => #[⟨⟨'0','9'⟩, by simp_arith⟩, ⟨⟨'A','Z'⟩, by simp_arith⟩, ⟨⟨'a','z'⟩, by simp_arith⟩]
    | .Alpha => #[⟨⟨'A','Z'⟩, by simp_arith⟩, ⟨⟨'a','z'⟩, by simp_arith⟩]
    | .Ascii => #[⟨⟨'\x00', '\x7F'⟩, by simp_arith⟩]
    | .Blank => #[⟨⟨'\t','\t'⟩, by simp_arith⟩, ⟨⟨' ',' '⟩, by simp_arith⟩]
    | .Cntrl => #[⟨⟨'\x00', '\x1F'⟩, by simp_arith⟩, ⟨⟨'\x7F', '\x7F'⟩, by simp_arith⟩]
    | .Digit => #[⟨⟨'0','9'⟩, by simp_arith⟩]
    | .Graph => #[⟨⟨'!','~'⟩, by simp_arith⟩]
    | .Lower => #[⟨⟨'a','z'⟩, by simp_arith⟩]
    | .Print => #[⟨⟨' ','~'⟩, by simp_arith⟩]
    | .Punct => #[⟨⟨'!','/'⟩, by simp_arith⟩, ⟨⟨':','@'⟩, by simp_arith⟩, ⟨⟨'[','`'⟩, by simp_arith⟩,
        ⟨⟨'{','~'⟩, by simp_arith⟩]
    | .Space => #[⟨⟨'\t','\t'⟩, by simp_arith⟩, ⟨⟨'¬','¬'⟩, by simp_arith⟩,
        ⟨⟨'\x0B', '\x0C'⟩, by simp_arith⟩, ⟨⟨'\n','\n'⟩, by simp_arith⟩, ⟨⟨'\r','\r'⟩, by simp_arith⟩,
        ⟨⟨' ',' '⟩, by simp_arith⟩]
    | .Upper => #[⟨⟨'A','Z'⟩, by simp_arith⟩]
    | .Word => #[⟨⟨'0','9'⟩, by simp_arith⟩, ⟨⟨'A','Z'⟩ , by simp_arith⟩, ⟨⟨'_','_'⟩ , by simp_arith⟩,
        ⟨⟨'a','z'⟩ , by simp_arith⟩]
    | .Xdigit => #[⟨⟨'0','9'⟩, by simp_arith⟩, ⟨⟨'A','F'⟩ , by simp_arith⟩, ⟨⟨'a','f'⟩ , by simp_arith⟩]

  Except.ok (unicode_fold_and_negate range flags cls.negated)

private def hir_assertion (ast : AstItems.Assertion) (flags : Syntax.Flags) : Hir :=
  let multi_line := flags.is_multi_line
  let crlf := flags.is_crlf

  let kind := match ast.kind with
  | .StartLine =>
      if multi_line then if crlf then HirKind.Look (.StartCRLF) else HirKind.Look (.StartLF)
      else HirKind.Look (.Start)
  | .EndLine =>
      if multi_line then if crlf then HirKind.Look (.EndCRLF) else HirKind.Look (.EndLF)
      else HirKind.Look (.End)
  | .EndLineWithOptionalLF =>
      if multi_line then if crlf then HirKind.Look (.EndCRLF) else HirKind.Look (.EndLF)
      else HirKind.Look (Look.EndWithOptionalLF)
  | .StartText =>
      HirKind.Look (Look.Start)
  | .EndText =>
      HirKind.Look (Look.End)
  | .EndTextWithOptionalLF =>
      HirKind.Look (Look.EndWithOptionalLF)
  | .WordBoundary =>
      HirKind.Look (Look.WordUnicode)
  | .NotWordBoundary =>
      HirKind.Look (Look.WordUnicodeNegate)
  | .WordBoundaryStart =>
      HirKind.Look (Look.WordStartUnicode)
  | .WordBoundaryEnd =>
      HirKind.Look (Look.WordEndUnicode)
  | .WordBoundaryStartHalf =>
      HirKind.Look (Look.WordStartHalfUnicode)
  | .WordBoundaryEndHalf =>
      HirKind.Look (Look.WordEndHalfUnicode)
  | .PreviousMatch =>
      HirKind.Look (Look.PreviousMatch)
  | .ClearMatches =>
      HirKind.Look (Look.ClearMatches)

  ⟨kind, Syntax.Hir.toProperties kind⟩

private def hir_capture (g : AstItems.Group) (expr: Hir) : Hir :=
  let (index, name) : Option Nat × Option String :=
    match g.kind with
    | .CaptureIndex captureIndex _ => (some captureIndex, none)
    | .NonCapturing _ => (none, none)
    | .Lookaround _ => (none, none)

  match index with
  | some index =>
    let cap : Syntax.Capture := Syntax.Capture.mk index name expr
    Hir.mk (HirKind.Capture cap) default
  | none =>
      match g.kind with
      | .Lookaround .PositiveLookahead =>
        let look : Syntax.Lookaround := Syntax.Lookaround.PositiveLookahead expr
        Hir.mk (HirKind.Lookaround look) default
      | .Lookaround .NegativeLookahead =>
        let look : Syntax.Lookaround := Syntax.Lookaround.NegativeLookahead expr
        Hir.mk (HirKind.Lookaround look) default
      | .Lookaround (.PositiveLookbehind i) =>
        let look : Syntax.Lookaround := Syntax.Lookaround.PositiveLookbehind i expr
        Hir.mk (HirKind.Lookaround look) default
      | .Lookaround (.NegativeLookbehind i) =>
        let look : Syntax.Lookaround := Syntax.Lookaround.NegativeLookbehind i expr
        Hir.mk (HirKind.Lookaround look) default
      | _ => expr

def pop_concat_expr (stack : Array HirFrame) : Except String (Array HirFrame × Option Hir) :=
  match Array.pop? stack with
  | some (frame, stack) =>
    match frame with
    | .Concat => Except.ok (stack, none)
    | .Expr expr => Except.ok (stack, (some expr))
    | .Literal c => Except.ok (stack, (some (Hir.mk (Syntax.HirKind.Literal c) default)))
    | .BackRef f n => Except.ok (stack, (some (Hir.mk (Syntax.HirKind.BackRef f n) default)))
    | .ClassUnicode _ => Except.error "pop_concat_expr, unexpected frame"
    | .Repetition => Except.error "pop_concat_expr, unexpected frame .ClassUnicode"
    | .Group _ => Except.error "pop_concat_expr, unexpected frame .Group"
    | .Alternation => Except.error "pop_concat_expr, unexpected frame .Alternation"
  | none => Except.ok (stack, none)

theorem sizeOf_pop_concat_expr {stack : Array HirFrame}
  (h : pop_concat_expr  stack = Except.ok (stack', some hir))
    : sizeOf stack' < sizeOf stack := by
  unfold pop_concat_expr at h
  split at h <;> try simp_all
  split at h <;> try simp_all <;> (rename_i heq; exact Array.sizeOf_pop? heq)

def pop_concat_exprs (stack : Array HirFrame) (exprs : Array Hir)
    : Except String (Array HirFrame × Array Hir) :=
  match h : pop_concat_expr stack with
  | Except.ok (stack', some hir) =>
    have : sizeOf stack' < sizeOf stack := sizeOf_pop_concat_expr h
    pop_concat_exprs stack' (exprs.push hir)
  | Except.ok (stack, none) => Except.ok (stack, exprs)
  | Except.error e => Except.error e
termination_by stack

def pop_alt_expr (stack : Array HirFrame) : Except String (Array HirFrame × Option Hir) :=
  match Array.pop? stack with
  | some (frame, stack) =>
    match frame with
    | .Alternation => Except.ok (stack, none)
    | .Expr expr => Except.ok (stack, (some expr))
    | .Literal c => Except.ok (stack, (some (Hir.mk (Syntax.HirKind.Literal c) default)))
    | .BackRef f n => Except.ok (stack, (some (Hir.mk (Syntax.HirKind.BackRef f n) default)))
    | __ => Except.error "pop_alt_expr, unexpected frame"
  | none => Except.ok (stack, none)

theorem sizeOf_pop_alt_expr {stack : Array HirFrame}
  (h : pop_alt_expr stack = Except.ok (stack', some hir))
    : sizeOf stack' < sizeOf stack := by
  unfold pop_alt_expr at h
  split at h <;> try simp_all
  split at h <;> try simp_all <;> (rename_i heq; exact Array.sizeOf_pop? heq)

def pop_alt_exprs (stack : Array HirFrame) (exprs : Array Hir)
    : Except String (Array HirFrame × Array Hir) := do
  match h : pop_alt_expr stack with
  | Except.ok (stack', some hir) =>
    have : sizeOf stack' < sizeOf stack := sizeOf_pop_alt_expr h
    pop_alt_exprs stack' (exprs.push hir)
  | Except.ok (stack, none) => Except.ok (stack, exprs)
  | Except.error e => Except.error e
termination_by stack

private def finish (translator : Translator) : Except String Hir :=
  match Array.pop? translator.stack with
  | some (frame, _) => frame.unwrap_expr
  | none => Except.error "empty stack"

private def start (translator : Translator) : Translator := translator

/-- This method is called on an `Ast` before descending into child `Ast` nodes. -/
def visit_pre (ast : Ast) : StateT Translator (Except String) PUnit := do
  let t ← get
  match ast with
  | .ClassBracketed _ =>
      set {t with stack := t.stack.push (HirFrame.ClassUnicode ClassUnicode.empty)}
  | .Repetition _ =>
      set {t with stack := t.stack.push (HirFrame.Repetition)}
  | .Alternation ⟨_, _⟩  =>
      set {t with stack := t.stack.push (HirFrame.Alternation)}
  | .Group g =>
    let old_flags := t.flags
    let t :=
      match g.kind with
      | .NonCapturing flags => set_flags flags t
      | _ => t
    set {t with stack := t.stack.push (HirFrame.Group old_flags)}
  | .Concat _ => set {t with stack := t.stack.push (HirFrame.Concat)}
  | _ => pure ()

/-- This method is called on an `Ast` after descending all of its child `Ast` nodes. -/
def visit_post (ast: Ast) : StateT Translator (Except String) PUnit := do
  let t ← get
  match ast with
  | .Empty =>
    let expr := Hir.mk HirKind.Empty default
    set {t with stack := t.stack.push (HirFrame.Expr expr)}
  | .Flags ⟨_, flags⟩  =>
    let expr := Hir.mk HirKind.Empty default
    let t := set_flags flags t
    set {t with stack := t.stack.push (HirFrame.Expr expr)}
  | .Literal lit =>
    let c ← ast_literal_to_scalar lit
    if t.flags.is_case_insensitive
    then
      let ranges : IntervalSet Char := IntervalSet.canonicalize (Unicode.case_fold_char c)
      let cls : ClassUnicode := ClassUnicode.canonicalize ⟨ranges⟩
      let kind := (HirKind.Class (Class.Unicode cls))
      let expr := Hir.mk kind (Hir.toProperties kind)
      set {t with stack := t.stack.push (HirFrame.Expr expr)}
    else
      set {t with stack := push_char c t.stack}
  | .BackRef ⟨_, n⟩ =>
    set {t with stack := t.stack.push (HirFrame.BackRef t.flags.is_case_insensitive n)}
  | .Dot _ =>
    let expr := (hir_dot t.flags)
    set {t with stack := t.stack.push (HirFrame.Expr expr)}
  | .ClassBracketed ast =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let cls := unicode_fold_and_negate cls.set.intervals t.flags ast.negate
      let kind := (HirKind.Class (Class.Unicode cls))
      let expr := Hir.mk kind (Hir.toProperties kind)
      set {t with stack := stack.push (HirFrame.Expr expr)}
    | none => Except.error "visit_post .ClassBracketed stack empty"
  | .ClassUnicode cls =>
      let cls ← hir_unicode_class cls t.flags
      let kind := (HirKind.Class (Class.Unicode cls))
      set {t with stack := t.stack.push (HirFrame.Expr (Hir.mk kind (Hir.toProperties kind)))}
  | .Assertion a => set {t with stack := t.stack.push (HirFrame.Expr (hir_assertion a t.flags))}
  | .ClassPerl cls =>
      let cls ← hir_perl_unicode_class cls t.flags
      let kind := (HirKind.Class (Class.Unicode cls))
      set {t with stack := t.stack.push (HirFrame.Expr (Hir.mk kind (Hir.toProperties kind)))}
  | .Repetition rep =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let expr ← frame.unwrap_expr
      match stack.pop? with
      | some (frame, stack) =>
        let _ ← frame.unwrap_repetition
        set {t with stack := stack.push (HirFrame.Expr (hir_repetition rep expr t.flags))}
      | none => Except.error "visit_post .Repetition expr stack empty"
    | _ => Except.error "visit_post .Repetition stack empty"
  | .Group g =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let expr ← frame.unwrap_expr
      match stack.pop? with
      | some (frame, stack) =>
        let flags ← frame.unwrap_group
        let stack := stack.push (HirFrame.Expr (hir_capture g expr))
        set {t with stack := stack, flags := flags}
      | none => Except.error "visit_post .Group expr stack empty"
    | none => Except.error "visit_post .Group stack empty"
  | .Concat _ =>
    match pop_concat_exprs t.stack #[] with
    | Except.ok (stack, exprs) =>
        let exprs := exprs |> Array.filter (match ·.kind with | .Empty => false | _ => true)
        set {t with
          stack := stack.push
            (HirFrame.Expr (Hir.mk (Syntax.HirKind.Concat exprs.reverse) default))}
    | Except.error e => Except.error e
  | .Alternation _ =>
    match pop_alt_exprs t.stack #[] with
    | Except.ok (stack, exprs) =>
        set {t with
          stack := stack.push
            (HirFrame.Expr (Hir.mk (Syntax.HirKind.Alternation exprs.reverse) default))}
    | Except.error e => Except.error e

/-- This method is called on every [`ClassSetItem`] before descending into child nodes. -/
def visit_class_set_item_pre (ast : ClassSetItem)
    : StateT Translator (Except String) PUnit := do
 match ast with
 | .Bracketed _ =>
    let t ← get
    set {t with stack := t.stack.push (HirFrame.ClassUnicode  ClassUnicode.empty)}
 | _ => pure ()

/-- This method is called on every [`ClassSetItem`] after descending into child nodes. -/
def visit_class_set_item_post (ast : ClassSetItem)
    : StateT Translator (Except String) PUnit := do
  let t ← get
  match ast with
  | .Literal lit =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let ranges := cls.set.intervals.push ⟨⟨lit.c, lit.c⟩ , by simp [Char.eq_le _]⟩
      let cls := ⟨ClassUnicode.set ⟨IntervalSet.canonicalize ranges⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Literal in stack expected"
  | .Range range =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let ranges := cls.set.intervals.push ⟨⟨range.start.c, range.end.c⟩, range.isLe⟩
      let cls := ⟨ClassUnicode.set ⟨IntervalSet.canonicalize ranges⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Ascii asciicls =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let xcls ← hir_ascii_unicode_class asciicls t.flags
      let cls := ⟨ClassUnicode.set ⟨IntervalSet.union cls.set xcls.set⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Unicode cls =>
    let xcls ← hir_unicode_class cls t.flags
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let cls := ⟨ClassUnicode.set ⟨IntervalSet.union cls.set xcls.set⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Perl cls =>
    let xcls ← hir_perl_unicode_class cls t.flags
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let cls := ⟨ClassUnicode.set ⟨IntervalSet.union cls.set xcls.set⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Bracketed ast =>
     match t.stack.pop? with
    | some (cls1, stack) =>
      match stack.pop? with
      | some (cls2, stack) =>
        let cls1 ← cls1.unwrap_class_unicode
        let cls1 := unicode_fold_and_negate cls1.set.intervals t.flags ast.negate
        let cls2 ← cls2.unwrap_class_unicode
        set {t with stack :=
          stack.push (HirFrame.ClassUnicode (ClassUnicode.union cls1 cls2))}
      | none => Except.error "visit_class_set_item_post .Range in stack expected"
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Union _ => pure ()
  | .Empty _ => pure ()

/-- This method is called on every [`ClassSetBinaryOp`] before descending into  child nodes. -/
def visit_class_set_binary_op_pre : StateT Translator (Except String) PUnit := do
  let t ← get
  set {t with stack := t.stack.push (HirFrame.ClassUnicode ClassUnicode.empty)}

/-- This method is called between the left hand and right hand child nodes. -/
def visit_class_set_binary_op_in : StateT Translator (Except String) PUnit := do
  let t ← get
  set {t with stack := t.stack.push (HirFrame.ClassUnicode ClassUnicode.empty)}

/-- This method is called on every [`ClassSetBinaryOp`] after descending into  child nodes. -/
def visit_class_set_binary_op_post (op: ClassSetBinaryOp)
    : StateT Translator (Except String) PUnit := do
  let t ← get
  match t.stack.pop? with
  | some (rhs, stack) =>
    match stack.pop? with
    | some (lhs, stack) =>
      match stack.pop? with
      | some (cls, stack) =>
        let lhs ← lhs.unwrap_class_unicode
        let lhs := unicode_fold_and_negate lhs.set.intervals t.flags false
        let rhs ← rhs.unwrap_class_unicode
        let rhs := unicode_fold_and_negate rhs.set.intervals t.flags false
        let cls ← cls.unwrap_class_unicode
        let clsOfKind :=
          match op.kind with
          | .Intersection => ClassUnicode.intersection lhs rhs
          | .Difference => ClassUnicode.difference lhs rhs
          | .SymmetricDifference => ClassUnicode.symmetric_difference lhs rhs
        set {t with stack :=
              stack.push (HirFrame.ClassUnicode (ClassUnicode.union cls clsOfKind))}
      | none => Except.error "visit_class_set_binary_op_post stack empty for cls"
    | none => Except.error "visit_class_set_binary_op_post stack empty for lhs"
  | none => Except.error "visit_class_set_binary_op_post stack empty for rhs"

instance : AstItems.Visitor Hir Translator where
  finish := finish
  start := start
  visit_pre := visit_pre
  visit_post := visit_post
  visit_class_set_item_pre := visit_class_set_item_pre
  visit_class_set_item_post := visit_class_set_item_post
  visit_class_set_binary_op_pre := (fun _ => visit_class_set_binary_op_pre)
  visit_class_set_binary_op_in := (fun _ => visit_class_set_binary_op_in)
  visit_class_set_binary_op_post := visit_class_set_binary_op_post

/-- Translate the given abstract syntax tree into a high level intermediate representation. -/
def translate (flags : Flags := default) (ast : Ast) : Except String Hir :=
  visit instVisitorHirTranslator ⟨#[], flags⟩  ast
