import Regex.Data.Array.Basic
import Regex.Data.Array.Lemmas
import Regex.Syntax.Ast.Ast

/-!
## Visitor

Visit (`Syntax.Ast.visit`) every item in an abstract syntax tree `Syntax.Ast.Ast` recursively
using the class `Syntax.Ast.Visitor`.
-/

namespace Syntax.AstItems

open Syntax Ast

/-- A class for visiting an abstract syntax tree (AST) in depth first order. -/
class Visitor (α : Type v) (σ : Type w) where
  /-- The result of visiting the AST or an error. -/
  finish : (state : σ) -> Except String α
  /-- This method is called before beginning traversal of the AST. -/
  start :  σ -> σ
  /-- This method is called on an `Ast` before descending into child `Ast` nodes. -/
  visit_pre : (ast: Ast) -> StateT σ (Except String) PUnit
  /-- This method is called on an `Ast` after descending all of its child `Ast` nodes. -/
  visit_post : (ast: Ast) -> StateT σ (Except String) PUnit
  /-- This method is called on every [`ClassSetItem`] before descending into child nodes. -/
  visit_class_set_item_pre : (ast: ClassSetItem) -> StateT σ (Except String) PUnit
  /-- This method is called on every [`ClassSetItem`] after descending into child nodes. -/
  visit_class_set_item_post : (ast: ClassSetItem) -> StateT σ (Except String) PUnit
  /-- This method is called on every [`ClassSetBinaryOp`] before descending into
      child nodes. -/
  visit_class_set_binary_op_pre : (ast: ClassSetBinaryOp) -> StateT σ (Except String) PUnit
  /-- This method is called on every [`ClassSetBinaryOp`] after descending into
      child nodes. -/
  visit_class_set_binary_op_post : (ast: ClassSetBinaryOp) -> StateT σ (Except String) PUnit
  /-- This method is called between the left hand and right hand child nodes -/
  visit_class_set_binary_op_in : (ast: ClassSetBinaryOp) -> StateT σ (Except String) PUnit

abbrev M σ String := StateT σ (Except String)

private def visit_class_pre' {α σ: Type} (ast: ClassSet)
    (β : Visitor α σ) : M σ String PUnit := do
  match ast with
  | .Item cls =>
    β.visit_class_set_item_pre cls
  | .BinaryOp op =>
    β.visit_class_set_binary_op_pre op

private def visit_class_post' {α σ: Type} (ast: ClassSet)
    (β : Visitor α σ) : M σ String PUnit := do
  match ast with
  | .Item cls =>
    β.visit_class_set_item_post cls
  | .BinaryOp op =>
    β.visit_class_set_binary_op_post op

mutual

private def visit_class_item_loop' {α σ: Type} [Inhabited α]
    (β : Visitor α σ) (item : ClassSetItem) : M σ String PUnit := do
  β.visit_class_set_item_pre item
  match item with
  | .Bracketed ⟨_ , _, kind⟩  => visit_class_loop' β kind
  | .Union ⟨_, items⟩  =>
      items.attach.forM (fun (item : { x // x ∈ items}) => do
          have : sizeOf item.val < sizeOf items := Array.sizeOf_lt_of_mem item.property
          visit_class_item_loop' β item.val)
  | _ => pure ()
  β.visit_class_set_item_post item
termination_by sizeOf item

private def visit_class_loop' {α σ: Type} [Inhabited α]
    (β : Visitor α σ) (ast : ClassSet) : M σ String PUnit := do
  visit_class_pre' ast β

  match ast with
  | .Item (ClassSetItem.Bracketed ⟨_, _, kind⟩ ) => visit_class_loop'  β kind
  | .Item (ClassSetItem.Union  ⟨_, items⟩) =>
      items.attach.forM (fun (item : { x // x ∈ items}) => do
          have : sizeOf item.val < sizeOf items := Array.sizeOf_lt_of_mem item.property
          visit_class_item_loop' β item.val)
  | .BinaryOp op =>
    match op with
    | .mk _ _ lhs rhs =>
          visit_class_loop' β lhs
          let s ← get
          let (_, s) ← β.visit_class_set_binary_op_in op s
          set s
          visit_class_loop' β rhs
  | _ => pure ()

  visit_class_post' ast β
termination_by sizeOf ast

end

private def visit_class [Inhabited α] (ast: ClassBracketed)
    (β : Visitor α σ) : M σ String PUnit := do
  match ast with | .mk _ _ kind => visit_class_loop' β kind

def visit_loop {α σ: Type} [Inhabited α] (β : Visitor α σ) (ast : Ast) : M σ String PUnit := do
  β.visit_pre ast
  let res ← match h : ast with
    | .Empty | .Flags _ | .Literal _ | .BackRef _ | .Dot _ | .Assertion _ | .ClassUnicode _ | .ClassPerl _ =>
      pure default
    | .ClassBracketed cls =>
      visit_class cls β
      pure default
    | .Repetition rep =>
      match rep with
      | .mk _ _ _ _ ast' =>
        visit_loop β ast'
    | .Alternation alt =>
      match alt with
      | .mk _ items =>
        items.attach.forM (fun (ast : { x // x ∈ items}) => do
          have : sizeOf ast.val < sizeOf items := Array.sizeOf_lt_of_mem ast.property
          visit_loop β ast.val)
    | .Group g =>
      match g with
      | .mk _ _ ast' =>
        visit_loop β ast'
    | .Concat concat => do
        have : sizeOf concat.asts < sizeOf concat := Concat.sizeOfAstsOfConcat concat
        concat.asts.attach.forM (fun (ast : { x // x ∈ concat.asts}) => do
          have : sizeOf ast.val < sizeOf concat.asts := Array.sizeOf_lt_of_mem ast.property
          visit_loop β ast.val)

  β.visit_post ast
  pure res
termination_by sizeOf ast

/-- Visit every item in an `Ast` recursively -/
def visit {α σ: Type} [Inhabited α] (β : Visitor α σ) (state : σ) (ast : Ast)
    : Except String α := do
  let state := β.start state
  let (_, state) ← visit_loop β ast state
  β.finish state
