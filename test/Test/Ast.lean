import Regex

open Syntax
open AstItems
open Regex

namespace Test.Ast

private def toString (x : Except String Ast) : String :=
  match x with
  | Except.ok ast => s!"{ast}"
  | Except.error e => s!"Error {e}"

private def astOf'a' : Ast :=
    Ast.Literal ⟨String.toSpan "a" 0 1, LiteralKind.Verbatim, 'a'⟩

private def astOf'a?' : Ast :=
    Ast.Repetition
      (Repetition.mk
        (String.toSpan "a?" 0 2)
        ⟨String.toSpan "a?" 1 2, RepetitionKind.ZeroOrOne⟩
        true
        false
        (Ast.Literal ⟨String.toSpan "a?" 0 1, LiteralKind.Verbatim, 'a'⟩))

private def astOf'ab' : Ast :=
    Ast.Concat
      (Concat.mk
        (String.toSpan "ab" 0 2)
        #[Ast.Literal ⟨String.toSpan "ab" 0 1, LiteralKind.Verbatim, 'a'⟩,
          Ast.Literal ⟨String.toSpan "ab" 1 2, LiteralKind.Verbatim, 'b'⟩])

private def «astOf'[a]'» : Ast :=
    Ast.ClassBracketed
      (ClassBracketed.mk
        (String.toSpan "[a]" 0 3)
        false
        (ClassSet.Item (ClassSetItem.Literal ⟨String.toSpan "[a]" 1 2, LiteralKind.Verbatim, 'a'⟩)))

private def «astOf'[a-b]'» : Ast :=
    Ast.ClassBracketed
      (ClassBracketed.mk
        (String.toSpan "[a-b]" 0 5)
        false
        (ClassSet.Item (ClassSetItem.Range ⟨
            String.toSpan "[a-b]" 1 4,
            ⟨String.toSpan "[a-b]" 1 2, LiteralKind.Verbatim, 'a'⟩,
            ⟨String.toSpan "[a-b]" 3 4, LiteralKind.Verbatim, 'b'⟩,
            by simp_arith⟩)))

private def «astOf'a|b'» : Ast :=
    Ast.Alternation
      (Alternation.mk
        (String.toSpan "[a|b]" 0 3)
        #[Ast.Literal ⟨String.toSpan "a|b" 0 1, LiteralKind.Verbatim, 'a'⟩,
          Ast.Literal ⟨String.toSpan "a|b" 2 3, LiteralKind.Verbatim, 'b'⟩])

private def «astOf'(a)'» : Ast :=
    Syntax.AstItems.Ast.Group
      (Syntax.AstItems.Group.mk
        (String.toSpan "(a)" 0 3)
        (GroupKind.CaptureIndex 1 none)
        (Ast.Literal ⟨String.toSpan "(a)" 1 2, LiteralKind.Verbatim, 'a'⟩))

example : (parse "a" Syntax.Flavor.Rust |> toString) = s!"{astOf'a'}" := by native_decide

example : (parse "a?" Syntax.Flavor.Rust |> toString) = s!"{astOf'a?'}" := by native_decide

example : (parse "ab" Syntax.Flavor.Rust |> toString) = s!"{astOf'ab'}" := by native_decide

example : (parse "[a]" Syntax.Flavor.Rust |> toString) = s!"{«astOf'[a]'»}" := by native_decide

example : (parse "[a-b]" Syntax.Flavor.Rust |> toString) = s!"{«astOf'[a-b]'»}" := by native_decide

example : (parse "a|b" Syntax.Flavor.Rust |> toString) = s!"{«astOf'a|b'»}" := by native_decide

example : (parse "(a)" Syntax.Flavor.Rust |> toString) = s!"{«astOf'(a)'»}" := by native_decide

end Test.Ast
