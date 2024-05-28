import Regex

open Syntax
open Regex

namespace Test.Hir

def cls : Syntax.ClassUnicode :=
  let cls : ClassUnicodeRange := ⟨⟨'b', 'c'⟩, by simp_arith⟩
  ⟨IntervalSet.canonicalize #[cls]⟩

def cls_neg : Syntax.ClassUnicode :=
  let cls1 : ClassUnicodeRange := ⟨⟨'\u0000', 'a'⟩, by simp_arith⟩
  let cls2 : ClassUnicodeRange := ⟨⟨'d', ⟨0x10FFFF, by simp_arith⟩⟩, by simp_arith⟩
  ⟨IntervalSet.canonicalize #[cls1, cls2]⟩

example : (Syntax.ClassUnicode.negate cls |> toString) = (cls_neg |> toString) := by native_decide

private def toString (x : Except String Hir) : String :=
  match x with
  | Except.ok hir => s!"{hir}"
  | Except.error e => s!"Error {e}"

private def build (s : String) : Except String Hir := do
  let ast ← Syntax.AstItems.parse s
  let hir ← Syntax.translate default ast
  Except.ok hir

private def hirOf'a' : Hir :=
    Hir.mk (HirKind.Literal 'a') default

private def «hirOf'(a)'» : Hir :=
    Hir.mk (HirKind.Capture (Capture.mk 1 none (Hir.mk (HirKind.Literal 'a') default))) default

example : (build "a" |> toString) = hirOf'a'.toString 0 := by native_decide

example : (build "(a)" |> toString) = «hirOf'(a)'».toString 0 := by native_decide

private def _mkCls (arr : Array $ Char × Char) : Syntax.ClassUnicode :=
  ⟨IntervalSet.canonicalize
    (arr |> Array.filterMap (fun (c1, c2) => if h : c1 ≤ c2 then some ⟨⟨ c1, c2⟩, h⟩ else none))⟩

private def mkCls (arr : Array $ Char × Char) : Hir :=
    Hir.mk (HirKind.Class
      (Class.Unicode (_mkCls arr))) default

private def mkConcat (hir : Hir) : Hir :=
  Hir.mk (HirKind.Concat #[hir]) default

example : (build "[[:alpha:]]" |> toString)
  = (mkCls #[('A', 'Z'), ('a', 'z')]).toString 0 := by native_decide

example : (build "[[:^alpha:]]" |> toString)
  = (mkCls #[('\u0000', '@'), ('[', '`'), ('{', ⟨0x10FFFF, by simp_arith⟩)]).toString 0 := by
    native_decide

example : (build "[^A-Za-z]" |> toString)
  = (mkCls #[('\u0000', '@'), ('[', '`'), ('{', ⟨0x10FFFF, by simp_arith⟩)]).toString 0 := by
    native_decide

example : (build "[x[^xyz]]" |> toString)
  = (mkCls #[('\u0000', 'x'), ('{', ⟨0x10FFFF, by simp_arith⟩)]).toString 0 := by native_decide

example : (build "[a-y&&xyz]" |> toString) = (mkCls #[('x', 'y')]).toString 0 := by native_decide

example : (build "[0-9&&[^4]]" |> toString)
  = (mkCls #[('0', '3'), ('5', '9')]).toString 0 := by native_decide

example : (build "[0-9--4]" |> toString)
  = (mkCls #[('0', '3'), ('5', '9')]).toString 0 := by native_decide

example : (build r"[\&&&&]" |> toString) = (mkCls #[('&', '&')]).toString 0 := by native_decide

example : (build "(?i)[abc&&b-c]" |> toString) =
      (mkConcat (mkCls #[('B', 'C'), ('b', 'c')])).toString 0 := by
    native_decide

example : (build "[a-z&&b-y&&c-x]" |> toString) = (mkCls #[('c', 'x')]).toString 0 := by
  native_decide

example : (build "[[:alpha:]--[:lower:]]" |> toString) = (mkCls #[('A', 'Z')]).toString 0 := by
  native_decide

example : (build "[a-g~~c-j]" |> toString) = (mkCls #[('a', 'b'), ('h', 'j')]).toString 0 := by
  native_decide

example : (build "[a&&b]" |> toString) = (mkCls #[]).toString 0 := by native_decide

end Test.Hir
