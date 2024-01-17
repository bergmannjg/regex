import Regex.Syntax.Ast.Ast
import Regex.Syntax.Ast.Parse
import Regex.Syntax.Ast.Visitor
import Regex.Syntax.Hir
import Regex.Utils
import Regex.Unicode
import UnicodeBasic

/-!
## Translate

Translate (`Syntax.translate`) an abstract syntax tree `Syntax.Ast.Ast`
into a high level intermediate representation `Syntax.Hir`.
-/

namespace Syntax

open Ast

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

private def from_ast (ast: Syntax.Ast.Flags) : Syntax.Flags :=
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
private def set_flags (ast_flags : Syntax.Ast.Flags) (t : Translator) : Translator :=
  {t with flags := Flags.merge (Flags.from_ast ast_flags) t.flags}

/-- Convert an Ast literal to its scalar representation. -/
private def ast_literal_to_scalar (lit: Ast.Literal) : Except String Char :=
  Except.ok lit.c

private def push_char (c : Char) (stack : Array HirFrame) : Array HirFrame :=
  stack.push (HirFrame.Literal c)

private def unicode_fold_and_negate (cls : ClassUnicode) (flags : Flags) (negate : Bool)
    : ClassUnicode :=
  let cls := ClassUnicode.canonicalize cls
  let cls := if flags.is_case_insensitive then ClassUnicode.case_fold cls else cls
  if negate then ClassUnicode.negate cls else cls

private def hir_repetition (r : Ast.Repetition) (expr: Hir) (flags : Flags): Hir :=
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
    let rep : Syntax.Repetition := Syntax.Repetition.mk min max greedy expr
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

private def hir_unicode_class (cls : Ast.ClassUnicode) (flags : Flags)
    : Except String ClassUnicode := do
  let range ←
    match cls.kind with
    | .OneLetter c =>
        let range ← range_of_category c.toString
        Except.ok (unicode_fold_and_negate ⟨⟨range⟩⟩ flags cls.negated)
    | .Named s =>
      let range ← range_of_category s
      Except.ok (unicode_fold_and_negate ⟨⟨range⟩⟩ flags cls.negated)
    | .NamedValue _ n s =>
      let range ← range_of_named_property n s
      Except.ok (unicode_fold_and_negate ⟨⟨range⟩⟩ flags cls.negated)

private def hir_perl_unicode_class (cls : Ast.ClassPerl) (flags : Flags)
    : Except String ClassUnicode := do
  match cls.kind with
  | .Digit =>
    let range : Array ClassUnicodeRange ← range_of_general_category Unicode.GeneralCategory.Nd
    Except.ok (unicode_fold_and_negate ⟨⟨range⟩⟩ flags cls.negated)
  | .Space =>
    let range : Array ClassUnicodeRange ← range_of_property "White_Space"
    Except.ok (unicode_fold_and_negate ⟨⟨range⟩⟩ flags cls.negated)
  | .Word =>
    let range : Array ClassUnicodeRange ← range_of_property "Word"
    Except.ok (unicode_fold_and_negate ⟨⟨range⟩⟩ flags cls.negated)

private def hir_ascii_unicode_class (cls: Ast.ClassAscii) (flags : Flags)
    : Except String ClassUnicode := do
  let range : Array ClassUnicodeRange :=
    match cls.kind with
    | .Alnum => #[⟨'0','9'⟩, ⟨'A','Z'⟩, ⟨'a','z'⟩]
    | .Alpha => #[⟨'A','Z'⟩, ⟨'a','z'⟩]
    | .Ascii => #[⟨'\x00', '\x7F'⟩]
    | .Blank => #[⟨'\t','\t'⟩, ⟨' ',' '⟩]
    | .Cntrl => #[⟨'\x00', '\x1F'⟩, ⟨'\x7F', '\x7F'⟩]
    | .Digit => #[⟨'0','9'⟩]
    | .Graph => #[⟨'!','~'⟩]
    | .Lower => #[⟨'a','z'⟩]
    | .Print => #[⟨' ','~'⟩]
    | .Punct => #[⟨'!','/'⟩, ⟨':','@'⟩, ⟨'[','`'⟩, ⟨'{','~'⟩]
    | .Space => #[⟨'\t','\t'⟩, ⟨'¬','¬'⟩, ⟨'\x0B', '\x0C'⟩, ⟨'\r','\r'⟩, ⟨' ',' '⟩]
    | .Upper => #[⟨'A','Z'⟩]
    | .Word => #[⟨'0','9'⟩, ⟨'A','Z'⟩, ⟨'_','_'⟩, ⟨'a','z'⟩]
    | .Xdigit => #[⟨'0','9'⟩, ⟨'A','F'⟩, ⟨'a','f'⟩]

  Except.ok (unicode_fold_and_negate ⟨⟨range⟩⟩ flags cls.negated)

private def hir_assertion (ast : Ast.Assertion) (flags : Syntax.Flags) : Hir :=
  let multi_line := flags.is_multi_line
  let crlf := flags.is_crlf

  let kind := match ast.kind with
  | .StartLine =>
      if multi_line then if crlf then HirKind.Look (.StartCRLF) else HirKind.Look (.StartLF)
      else HirKind.Look (.Start)
  | .EndLine =>
      if multi_line then if crlf then HirKind.Look (.EndCRLF) else HirKind.Look (.EndLF)
      else HirKind.Look (.End)
  | .StartText =>
      HirKind.Look (Look.Start)
  | .EndText =>
      HirKind.Look (Look.End)
  | .WordBoundary =>
      HirKind.Look (Look.WordUnicode)
  | .NotWordBoundary =>
      HirKind.Look (Look.WordUnicodeNegate)

  ⟨kind, Syntax.Hir.toProperties kind⟩

private def hir_capture (g : Ast.Group) (expr: Hir) : Hir :=
  let (index, name) : Option Nat × Option String :=
    match g.kind with
    | .CaptureIndex captureIndex => (some captureIndex, none)
    | .NonCapturing _ => (none, none)

  match index with
  | some index =>
    let cap : Syntax.Capture := Syntax.Capture.mk index name expr
    Hir.mk (HirKind.Capture cap) default
  | none => expr

def pop_concat_expr (stack : Array HirFrame) : Except String (Array HirFrame × Option Hir) :=
  match Array.pop? stack with
  | some (frame, stack) =>
    match frame with
    | .Concat => Except.ok (stack, none)
    | .Expr expr => Except.ok (stack, (some expr))
    | .Literal c => Except.ok (stack, (some (Hir.mk (Syntax.HirKind.Literal c) default)))
    | .ClassUnicode _ => Except.error "pop_concat_expr, unexpected frame"
    | .Repetition => Except.error "pop_concat_expr, unexpected frame .ClassUnicode"
    | .Group _ => Except.error "pop_concat_expr, unexpected frame .Group"
    | .Alternation => Except.error "pop_concat_expr, unexpected frame .Alternation"
  | none => Except.ok (stack, none)

partial def pop_concat_exprs (stack : Array HirFrame) (exprs : Array Hir)
    : Except String (Array HirFrame × Array Hir) :=
  match pop_concat_expr stack with
  | Except.ok (stack, some hir) => pop_concat_exprs stack (exprs.push hir)
  | Except.ok (stack, none) => Except.ok (stack, exprs)
  | Except.error e => Except.error e

def pop_alt_expr (stack : Array HirFrame) : Except String (Array HirFrame × Option Hir) :=
  match Array.pop? stack with
  | some (frame, stack) =>
    match frame with
    | .Alternation => Except.ok (stack, none)
    | .Expr expr => Except.ok (stack, (some expr))
    | .Literal c => Except.ok (stack, (some (Hir.mk (Syntax.HirKind.Literal c) default)))
    | __ => Except.error "pop_alt_expr, unexpected frame"
  | none => Except.ok (stack, none)

partial def pop_alt_exprs (stack : Array HirFrame) (exprs : Array Hir)
    : Except String (Array HirFrame × Array Hir) := do
  match pop_alt_expr stack with
  | Except.ok (stack, some hir) =>  pop_alt_exprs stack (exprs.push hir)
  | Except.ok (stack, none) => Except.ok (stack, exprs)
  | Except.error e => Except.error e

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
      let ranges : IntervalSet Char := ⟨Unicode.case_fold_char c⟩
      let cls : ClassUnicode := ClassUnicode.canonicalize ⟨ranges⟩
      let kind := (HirKind.Class (Class.Unicode cls))
      let expr := Hir.mk kind (Hir.toProperties kind)
      set {t with stack := t.stack.push (HirFrame.Expr expr)}
    else
      set {t with stack := push_char c t.stack}
  | .Dot _ =>
    let expr := (hir_dot t.flags)
    set {t with stack := t.stack.push (HirFrame.Expr expr)}
  | .ClassBracketed ast =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let cls := unicode_fold_and_negate cls t.flags ast.negate
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
def visit_class_set_item_pre (_ : ClassSetItem)
    : StateT Translator (Except String) PUnit := do
 pure ()

/-- This method is called on every [`ClassSetItem`] after descending into child nodes. -/
def visit_class_set_item_post (ast : ClassSetItem)
    : StateT Translator (Except String) PUnit := do
  let t ← get
  match ast with
  | .Literal lit =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let ranges := cls.set.ranges.push ⟨lit.c, lit.c⟩
      let cls := ⟨ClassUnicode.set ⟨⟨ranges⟩⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Literal in stack expected"
  | .Range range =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let ranges := cls.set.ranges.push ⟨range.start.c, range.end.c⟩
      let cls := ⟨ClassUnicode.set ⟨⟨ranges⟩⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Ascii asciicls =>
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let xcls ← hir_ascii_unicode_class asciicls t.flags
      let ranges := cls.set.ranges ++ xcls.set.ranges -- todo
      let cls := ⟨ClassUnicode.set ⟨⟨ranges⟩⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Unicode cls =>
    let xcls ← hir_unicode_class cls t.flags
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let ranges := cls.set.ranges ++ xcls.set.ranges -- todo
      let cls := ⟨ClassUnicode.set ⟨⟨ranges⟩⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Perl cls =>
    let xcls ← hir_perl_unicode_class cls t.flags
    match t.stack.pop? with
    | some (frame, stack) =>
      let cls ← frame.unwrap_class_unicode
      let ranges := cls.set.ranges ++ xcls.set.ranges -- todo
      let cls := ⟨ClassUnicode.set ⟨⟨ranges⟩⟩⟩
      set {t with stack := stack.push (HirFrame.ClassUnicode cls)}
    | none => Except.error "visit_class_set_item_post .Range in stack expected"
  | .Bracketed _ => pure ()
  | .Union _ => pure ()
  | .Empty _ => pure ()

instance : Ast.Visitor String Hir Translator where
  finish := finish
  start := start
  visit_pre := visit_pre
  visit_post := visit_post
  visit_class_set_item_pre := visit_class_set_item_pre
  visit_class_set_item_post := visit_class_set_item_post

/-- Translate the given abstract syntax tree into a high level intermediate representation. -/
def translate (flags : Flags := default) (ast : Ast) : Except String Hir :=
  visit instVisitorStringHirTranslator ⟨#[], flags⟩  ast