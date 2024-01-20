import Regex.Syntax.Ast.Ast

/-!
## Visitor

Visit (`Syntax.Ast.visit`) every item in an abstract syntax tree `Syntax.Ast.Ast` recursively
using the class `Syntax.Ast.Visitor`.
-/

namespace Syntax.Ast

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

/-- Represents a single stack frame while performing structural induction over an `Ast`.-/
private inductive Frame where
  | Repetition : Repetition -> Frame
  | Group : Group -> Frame
  | Concat : (head : Ast) -> (tail : Array Ast) -> Frame
  | Alternation : (head : Ast) -> (tail : Array Ast) -> Frame

/-- Represents a single stack frame while performing structural induction overa character class. -/
private inductive ClassFrame where
  /-- The stack frame used while visiting every child node of a union of character class items. -/
  | Union (head: ClassSetItem) (tail: Array ClassSetItem) : ClassFrame
  /-- The stack frame used while a binary class operation. -/
  | Binary (op: ClassSetBinaryOp) : ClassFrame
  /-- A stack frame allocated just before descending into a binary operator's
      left hand child node. -/
  | BinaryLHS
        (op: ClassSetBinaryOp)
        (lhs: ClassSet)
        (rhs: ClassSet) : ClassFrame
  /-- A stack frame allocated just before descending into a binary operator's
      right hand child node. -/
  | BinaryRHS (op: ClassSetBinaryOp) (rhs: ClassSet) : ClassFrame

namespace Frame

/-- Return the next child AST node to visit.-/
private def child : Frame -> Ast
  | .Repetition rep => rep.ast
  | .Group g => g.ast
  | .Concat head _ => head
  | .Alternation head _ => head

end Frame

abbrev CallStack := Array (Ast × Frame)

/-- A representation of the inductive step when performing structural induction . -/
inductive ClassInduct where
  | Item : ClassSetItem -> ClassInduct
  | BinaryOp : ClassSetBinaryOp -> ClassInduct

namespace ClassInduct

def from_set : ClassSet -> ClassInduct
  | .Item cls => ClassInduct.Item cls
  | .BinaryOp op => ClassInduct.BinaryOp op

def from_bracketed : ClassBracketed -> ClassInduct
  | .mk _ _ cls => from_set cls

end ClassInduct

namespace ClassFrame

def child (x : ClassFrame) : ClassInduct :=
  match x with
  | .Union head _ => ClassInduct.Item head
  | .Binary op => ClassInduct.BinaryOp op
  | .BinaryLHS _ lhs _ => ClassInduct.from_set lhs
  | .BinaryRHS _ rhs => ClassInduct.from_set rhs

end ClassFrame

private def visit_class_pre {α σ: Type} (ast: ClassInduct)
    (β : Visitor α σ) : M σ String PUnit := do
  match ast with
  | .Item cls => β.visit_class_set_item_pre cls
  | .BinaryOp op => β.visit_class_set_binary_op_pre op

private def visit_class_post {α σ: Type} (ast: ClassInduct)
    (β : Visitor α σ) : M σ String PUnit := do
  match ast with
  | .Item cls => β.visit_class_set_item_post cls
  | .BinaryOp op => β.visit_class_set_binary_op_post op

/-- Build a stack frame for the given class node -/
private def induct_class (ast: ClassInduct) : Option ClassFrame :=
  match ast with
  | .Item (ClassSetItem.Bracketed ⟨_, _, kind⟩ ) =>
    match kind with
    | .Item item => some (ClassFrame.Union item #[])
    | .BinaryOp op => some (ClassFrame.Binary op)
  | .Item (ClassSetItem.Union union) =>
    let ⟨_, items⟩ := union
    if items.size = 0 then none
    else
      match items.head? with
      | some (head, tail) => some (ClassFrame.Union head tail)
      | none => none
  | .BinaryOp op =>
    match op with
    | .mk _ _ lhs rhs => some (ClassFrame.BinaryLHS op lhs rhs)
  | _ => none

/-- Pops the given frame. If the frame has an additional inductive step,
    then return it, otherwise return `None`. -/
private partial def pop_class (induct: ClassFrame) : Option ClassFrame :=
  match induct with
  | .Union _ tail =>
    match tail.head? with
    | some (head, tail) => ClassFrame.Union head tail
    | none => none
  | .Binary _ => none
  | .BinaryLHS op _ rhs => ClassFrame.BinaryRHS op rhs
  | .BinaryRHS _ _ => none

/-- try to pop the call stack until it is either empty or hit another inductive case. -/
private partial def visit_class_inner_loop {α σ: Type} [Inhabited α]
    (β : Visitor α σ) (stack : Array (ClassInduct × ClassFrame))
    : M σ String (Option ClassInduct × (Array (ClassInduct × ClassFrame))) := do
  match Array.pop? stack with
  | some ((post_ast, frame), stack) =>
    match pop_class frame with
    | some x =>
      match x with
      | .BinaryRHS op _ =>
        let s ← get
        let (_, s) ← β.visit_class_set_binary_op_in op s
        set s
        let stack := stack.push (post_ast, x)
        pure (some (ClassFrame.child x), stack)
      | _ =>
        let stack := stack.push (post_ast, x)
        pure (some (ClassFrame.child x), stack)
    | none =>
      visit_class_post post_ast β
      visit_class_inner_loop β stack
  | none => pure (none, #[])

private partial def visit_class_loop {α σ: Type} [Inhabited α]
    (β : Visitor α σ) (ast : ClassInduct) (stack : Array (ClassInduct × ClassFrame))
    : M σ String PUnit := do
  visit_class_pre ast β
  match induct_class ast with
  | some x =>
    let child := ClassFrame.child x
    let stack := stack.push (ast, x)
    visit_class_loop β child stack
  | none =>
    /- No induction means we have a base case, so we can post visit it now.-/
    visit_class_post ast β
    match ← visit_class_inner_loop β stack with
    | (some ast, stack) =>
      /- Process new inductive steps. -/
      visit_class_loop β ast stack
    | (none, _) => pure ()

private def visit_class [Inhabited α] (ast: ClassBracketed)
    (β : Visitor α σ) : M σ String PUnit := do
  let ast := ClassInduct.from_bracketed ast
  visit_class_loop β ast #[]

/-- Build a stack frame for the given AST if one is needed-/
private def induct [Inhabited α] (β : Visitor α σ) (ast : Ast)
    : M σ String (Option Frame) := do
  match ast with
  | .ClassBracketed cls =>
      visit_class cls β
      pure none
  | .Repetition rep => pure (some (Frame.Repetition rep))
  | .Group g => pure (some (Frame.Group g))
  | .Concat concat =>
      match concat.asts.head? with
      | some (head, tail) => pure (some (Frame.Concat head tail))
      | none => pure none
  | .Alternation ⟨_, asts⟩  =>
      match asts.head? with
      | some (head, tail) => pure (some (Frame.Concat head tail))
      | none => pure none
  | _ => pure none

/-- Pops the given frame. If the frame has an additional inductive step,
    then return it, otherwise return `None`. -/
private def pop (induct: Frame) : Option Frame :=
  match induct with
  | .Repetition _ => none
  | .Group _ => none
  | .Concat _ tail =>
      match tail.head? with
      | some (head, tail) => some (Frame.Concat head tail)
      | none => none
  | .Alternation _ tail =>
      match tail.head? with
      | some (head, tail) => some (Frame.Concat head tail)
      | none => none

/- try to pop the call stack until it is either empty or we hit another inductive case.-/
private partial def visit_inner_loop {α σ: Type} [Inhabited α]
    (β : Visitor α σ) (stack : CallStack) : M σ String ((Option (Ast × (CallStack))) × α) := do
  let state ← get
  match Array.pop? stack with
  | some ((post_ast, frame), stack) =>
    match pop frame with
    | some x =>
      /- If this is a concat/alternate, then we might have additional inductive steps to process. -/
      let ast := x.child
      let stack := stack.push (post_ast, x)
      pure (some (ast, stack), default)
    | none =>
      /- Otherwise, we've finished visiting all the child nodes, so we can post visit it now. -/
      β.visit_post post_ast
      visit_inner_loop β stack
  | none =>
    /- Call stack is empty.  -/
    match β.finish state with
    | Except.ok x =>
        set state
        pure (none, x)
    | Except.error e => Except.error e

/-- Visit every item in an `Ast` recursively -/
partial def visit_loop {α σ: Type} [Inhabited α]
    (β : Visitor α σ) (ast : Ast) (stack : CallStack) : M σ String α := do
  β.visit_pre ast
  match ← induct β ast with
  | some x =>
    let child := x.child
    let stack := stack.push (ast, x)
    visit_loop β child stack
  | none =>
    /- No induction means we have a base case, so we can post visit it now.-/
    β.visit_post ast
    match ← visit_inner_loop β stack with
    | (some (ast, stack), _) =>
      /- Process new inductive steps. -/
      visit_loop β ast stack
    | (none, res) => pure res

/-- Visit every item in an `Ast` recursively -/
def visit {α σ: Type} [Inhabited α] (β : Visitor α σ) (state : σ) (ast : Ast)
    : Except String α := do
  let state := β.start state
  let (res, _) ← visit_loop β ast default state
  pure res
