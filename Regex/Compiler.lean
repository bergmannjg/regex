import Regex.Syntax.Hir
import Regex.Nfa

namespace Compiler

open Syntax
open NFA

/-!
## Compiler

Compile from a regex's high-level intermediate representation (`Syntax.Hir`)
into an NFA state graph (`NFA`).
-/

/-- The configuration used for a Thompson NFA compiler. -/
structure Config where
  /-- Whether to compile an unanchored prefix into this NFA. -/
  unanchored_prefix: Bool

instance : Inhabited Config := ⟨⟨true⟩⟩

/-- A value that represents the result of compiling a sub-expression of a regex's HIR.
    Specifically, this represents a sub-graph of the NFA that
    has an initial state at `start` and a final state at `end`.
-/
structure ThompsonRef where
  start: StateID
  «end»: StateID

instance : Inhabited ThompsonRef := ⟨0, 0⟩

instance : ToString ThompsonRef where
  toString s := s!"{s.start}, {s.end}"

abbrev CompilerM := StateT (Array State) (Except String)

/-- Add a transition from one state to another. -/
private def patch («from» to : StateID) : CompilerM PUnit := do
  let states ← get
  if h : «from» < states.size
  then
    match states.get ⟨«from», h⟩ with
    | .Empty _ =>  set (states.set ⟨«from», h⟩ (State.Empty to))
    | .Look look _ =>  set (states.set ⟨«from», h⟩ (State.Look look to))
    | .ByteRange trans =>
        set (states.set ⟨«from», h⟩ (State.ByteRange {trans with next := to}))
    | .Capture _ pattern_id group_index slot =>
        set (states.set ⟨«from», h⟩ (State.Capture to pattern_id group_index slot))
    | .BinaryUnion alt1 alt2 =>
        if alt1 = 0 then set (states.set ⟨«from», h⟩ (State.BinaryUnion to alt2))
        else if alt2 = 0 then set (states.set ⟨«from», h⟩ (State.BinaryUnion alt1 to))
        else Except.error "patch states, .BinaryUnion alt1 and alt2 not null"
    | .SparseTransitions _ => set states -- todo
    | .Union alternates =>
        set (states.set ⟨«from», h⟩ (State.Union (alternates.push to)))
    | .UnionReverse alternates =>
        set (states.set ⟨«from», h⟩ (State.UnionReverse (alternates.push to)))
    | .Match _ => Except.error s!"patch states .Match unexpected"
  else  Except.error s!"patch not valid, {«from»} ge size {states.size}"

private def push (s : State) : CompilerM StateID := do
  let states ← get
  set (states.push s)
  pure states.size

private def push' (s : State) : CompilerM ThompsonRef := do
  let states ← get
  set (states.push s)
  pure ⟨states.size, states.size⟩

private def add_match (pattern_id : PatternID) : CompilerM StateID :=
  push (State.Match pattern_id)

private def add_union : CompilerM StateID :=
  push (State.Union #[])

private def add_union_reverse : CompilerM StateID  :=
  push (State.UnionReverse #[])

private def c_range (start «end» : UInt32) : CompilerM ThompsonRef :=
  let trans: Transition := ⟨start, «end», 0⟩
  push' (State.ByteRange trans)

private def add_empty : CompilerM StateID  :=
  push (State.Empty 0)

private def c_empty : CompilerM ThompsonRef :=
  push' (State.Empty 0)

private def add_sparse (trans : Array Transition) : CompilerM StateID  :=
  push (State.SparseTransitions trans)

private def c_unicode_class (cls : ClassUnicode) : CompilerM ThompsonRef := do
  let «end» ← add_empty
  let trans : Array Transition := cls.set.ranges.map (fun r => ⟨r.start.val, r.end.val, «end»⟩)
  let start ← add_sparse trans
  pure ⟨start, «end»⟩

private def c_literal (c : Char) : CompilerM ThompsonRef :=
  c_range c.val c.val

private def c_look : Syntax.Look -> CompilerM ThompsonRef
  | .Start => push' (State.Look NFA.Look.Start 0)
  | .End => push' (State.Look NFA.Look.End 0)
  | .StartLF => push' (State.Look NFA.Look.StartLF 0)
  | .EndLF => push' (State.Look NFA.Look.EndLF 0)
  | .StartCRLF => push' (State.Look NFA.Look.StartCRLF 0)
  | .EndCRLF => push' (State.Look NFA.Look.EndCRLF 0)
  | .WordUnicode => push' (State.Look NFA.Look.WordUnicode 0)
  | .WordUnicodeNegate => push' (State.Look NFA.Look.WordUnicodeNegate 0)
  | .WordStartUnicode => push' (State.Look NFA.Look.WordStartUnicode 0)
  | .WordEndUnicode => push' (State.Look NFA.Look.WordEndUnicode 0)
  | .WordStartHalfUnicode => push' (State.Look NFA.Look.WordStartHalfUnicode 0)
  | .WordEndHalfUnicode => push' (State.Look NFA.Look.WordEndHalfUnicode 0)

private def c_cap' (pattern_id slot: Nat) : CompilerM StateID  :=
  push (State.Capture 0 0 pattern_id slot)

mutual

private partial def c_concat (hirs : Array Hir) : CompilerM ThompsonRef := do
  match hirs.head? with
  | some (head, tail) =>
    let ⟨start, «end»⟩ ← c head

    let hir ← tail.foldlM (init := «end»)
      (fun s h => do
        let hir ← c h
        patch s hir.start
        pure hir.end)

    pure ⟨start, hir⟩
  | none => c_empty

private partial def c_alt_iter (hirs : Array Hir) : CompilerM ThompsonRef := do
  match hirs.head? with
  | some (first, tail) =>
    match tail.head? with
    | some (second, tail) =>
      let first ← c first
      let second ← c second
      let union ← add_union
      let «end» ← add_empty

      patch union first.start
      patch first.end «end»
      patch union second.start
      patch second.end «end»

      tail.forM
        (fun h => do
          let compiled ← c h
          patch union compiled.start
          patch compiled.end «end»)

      pure ⟨union, «end»⟩
    | none => Except.error "c_alt_iter, size > 1 expected"
  | none => Except.error "c_alt_iter, size > 0 expected"

private partial def c_exactly (h : Hir) (n : Nat) : CompilerM ThompsonRef :=
    c_concat ⟨List.replicate n h⟩

private partial def c_zero_or_one (h : Hir) (greedy : Bool) : CompilerM ThompsonRef := do
  let union ← if greedy then add_union else add_union_reverse
  let compiled ← c h
  let empty ← add_empty
  patch union compiled.start
  patch union empty
  patch compiled.end empty
  pure ⟨union, empty⟩

/-- Compile the given expression such that it may be matched `n` or more times -/
private partial def c_at_least (h : Hir) (n : Nat) (greedy : Bool) : CompilerM ThompsonRef := do
  if n = 0 then
    let cannotMatchEmptyString : Bool :=
       match h.properties.minimum_len with
      | some n => n > 0
      | none => false

    if cannotMatchEmptyString
    then
      let union ← (if greedy then add_union else add_union_reverse)
      let compiled ← c h
      patch union compiled.start
      patch compiled.end union

      pure ⟨union, union⟩
    else
      /- compile x* as (x+)?, which preserves the correct preference order
         if x can match the empty string. -/
      let compiled ← c h
      let plus ← (if greedy then add_union else add_union_reverse)
      patch compiled.end plus
      patch plus compiled.start

      let question ← (if greedy then add_union else add_union_reverse)
      let empty ← add_empty
      patch question compiled.start
      patch question empty
      patch plus empty

      pure ⟨question, empty⟩
  else if n = 1 then
    let compiled ← c h
    let union ← (if greedy then add_union else add_union_reverse)
    patch compiled.end union
    patch union compiled.start

    pure ⟨compiled.start, union⟩
  else
    let «prefix» ← c_exactly h (n - 1)
    let last ← c h
    let union ← (if greedy then add_union else add_union_reverse)
    patch «prefix».end last.start
    patch last.end union
    patch union last.start

    pure ⟨«prefix».start, union⟩

/-- Compile the given expression such that it matches at least `min` times,
    but no more than `max` times.-/
private partial def c_bounded (h : Hir) (min max : Nat) (greedy : Bool)
    : CompilerM ThompsonRef := do
  let «prefix» ← c_exactly h min
  if min = max then pure «prefix»
  else
    let empty ← add_empty
    let prev_end ← (List.replicate (max-min) 0).foldlM (init := «prefix».end)
      (fun prev_end _ => do
        let union ← (if greedy then add_union else add_union_reverse)
        let compiled ← c h
        patch prev_end union
        patch union compiled.start
        patch union empty
        pure compiled.end)
    patch prev_end empty
    pure ⟨«prefix».start, empty⟩

private partial def c_repetition : Repetition -> CompilerM ThompsonRef
  | .mk 0 (some 1) greedy sub => c_zero_or_one sub greedy
  | .mk min none greedy sub => c_at_least sub min greedy
  | .mk min (some max) greedy sub => c_bounded sub min max greedy

private partial def c (hir : Hir) : CompilerM ThompsonRef :=
  match hir.kind with
  | .Empty => c_empty
  | .Literal c => c_literal c
  | .Class (.Unicode cls) => c_unicode_class cls
  | .Look look => c_look look
  | .Repetition rep => c_repetition rep
  | .Capture ⟨index, _, sub⟩  => c_cap index sub
  | .Concat hirs => c_concat hirs
  | .Alternation sub => c_alt_iter sub

private partial def c_cap (pattern_id : Nat) (hir : Hir) : CompilerM ThompsonRef := do
  let start ← c_cap' pattern_id (pattern_id * 2)
  let inner ← c hir
  let «end» ← c_cap' pattern_id (pattern_id * 2 + 1)
  patch start inner.start
  patch inner.end «end»
  pure ⟨start, «end»⟩

end

private def startsWithStart (hir : Hir) : Bool :=
  match hir.kind with
  | .Concat hirs =>
    match hirs.head? with
    | some (⟨HirKind.Look Syntax.Look.Start, _⟩  , _) => true
    | _ => false
  | _ => false

/-- Compile the HIR expression given. -/
private def compile' (anchored : Bool) (expr : Hir) : CompilerM PUnit := do
  let unanchored_prefix ← if anchored then c_empty else c_at_least (dot Dot.AnyChar) 0 false
  let one ← c_cap 0 expr
  let match_state_id ← add_match 0
  patch one.end match_state_id
  patch unanchored_prefix.end one.start

/-- Compile the HIR expression given. -/
def compile (config : Config := default) (expr : Hir) : Except String NFA := do
  let anchored := !config.unanchored_prefix || startsWithStart expr
  let (_, states) ← compile' anchored expr #[]
  let nfa : NFA := ⟨states, 0, 0⟩
  Except.ok nfa
