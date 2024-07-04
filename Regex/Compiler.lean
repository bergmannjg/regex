import Batteries.Data.Array.Basic
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
  /-- Whether to simulate an unanchored prefix with the backtracker. -/
  unanchored_prefix_simulation : Bool

instance : Inhabited Config := ⟨⟨true, false⟩⟩

/-- A value that represents the result of compiling a sub-expression of a regex's HIR.
    Specifically, this represents a sub-graph of the NFA that
    has an initial state at `start` and a final state at `end`.
-/
structure ThompsonRef where
  start: Unchecked.StateID
  «end»: Unchecked.StateID

instance : Inhabited ThompsonRef := ⟨0, 0⟩

instance : ToString ThompsonRef where
  toString s := s!"{s.start}, {s.end}"

abbrev CompilerM := StateT (Array Unchecked.State) (Except String)

/-- Add a transition from one state to another. -/
private def patch («from» «to» : Unchecked.StateID) : CompilerM PUnit := do
  let states ← get
  if h : «from» < states.size
  then
    match states.get ⟨«from», h⟩ with
    | .Empty _ =>  set (states.set ⟨«from», h⟩ (Unchecked.State.Empty «to»))
    | .NextChar offset _ =>  set (states.set ⟨«from», h⟩ (Unchecked.State.NextChar offset «to»))
    | .Fail =>  Except.error s!"patch states .Fail unexpected"
    | .Eat (.Until s) n =>
        if s = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.Eat (.Until «to») n))
        else if n = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.Eat (.Until s) «to»))
        else Except.error "patch states, .Eat s and n not null"
    | .Eat (.ToLast s) n =>
        if s = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.Eat (.ToLast «to») n))
        else if n = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.Eat (.ToLast s) «to»))
        else Except.error "patch states, .Eat s and n not null"
    | .ChangeFrameStep f t =>
        if f = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.ChangeFrameStep «to» t))
        else if t = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.ChangeFrameStep f «to»))
        else Except.error "patch states, .ChangeFrameStep from and to not null"
    | .RemoveFrameStep _ =>  set (states.set ⟨«from», h⟩ (Unchecked.State.RemoveFrameStep «to»))
    | .Look look _ =>  set (states.set ⟨«from», h⟩ (Unchecked.State.Look look «to»))
    | .BackRef b f _ =>  set (states.set ⟨«from», h⟩ (Unchecked.State.BackRef b f «to»))
    | .ByteRange t =>
        set (states.set ⟨«from», h⟩ (Unchecked.State.ByteRange {t with «next» := «to»}))
    | .Capture role _ pattern_id group_index slot =>
        set (states.set ⟨«from», h⟩ (Unchecked.State.Capture role «to» pattern_id group_index slot))
    | .BinaryUnion alt1 alt2 =>
        if alt1 = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.BinaryUnion «to» alt2))
        else if alt2 = 0 then set (states.set ⟨«from», h⟩ (Unchecked.State.BinaryUnion alt1 «to»))
        else Except.error "patch states, .BinaryUnion alt1 and alt2 not null"
    | .SparseTransitions _ => set states -- todo
    | .Union alternates =>
        set (states.set ⟨«from», h⟩ (Unchecked.State.Union (alternates.push «to»)))
    | .UnionReverse alternates =>
        set (states.set ⟨«from», h⟩ (Unchecked.State.UnionReverse (alternates.push «to»)))
    | .Match _ => Except.error s!"patch states .Match unexpected"
  else  Except.error s!"patch not valid, {«from»} ge size {states.size}"

private def push (s : Unchecked.State) : CompilerM Unchecked.StateID := do
  let states ← get
  set (states.push s)
  pure states.size

private def push' (s : Unchecked.State) : CompilerM ThompsonRef := do
  let states ← get
  set (states.push s)
  pure ⟨states.size, states.size⟩

private def add_match (pattern_id : PatternID) : CompilerM Unchecked.StateID :=
  push (Unchecked.State.Match pattern_id)

private def add_union : CompilerM Unchecked.StateID :=
  push (Unchecked.State.Union #[])

private def add_union_reverse : CompilerM Unchecked.StateID  :=
  push (Unchecked.State.UnionReverse #[])

private def add_backrefence (case_insensitive : Bool) (b : Nat)  : CompilerM Unchecked.StateID :=
  push (Unchecked.State.BackRef b case_insensitive 0)

private def c_range (start «end» : UInt32) : CompilerM ThompsonRef :=
  let trans: Unchecked.Transition := ⟨start, «end», 0⟩
  push' (Unchecked.State.ByteRange trans)

private def add_empty : CompilerM Unchecked.StateID  :=
  push (Unchecked.State.Empty 0)

private def add_fail  : CompilerM Unchecked.StateID :=
  push (Unchecked.State.Fail)

private def add_eat (mode : Unchecked.EatMode) : CompilerM Unchecked.StateID :=
  push (Unchecked.State.Eat mode 0)

private def add_change_state : CompilerM Unchecked.StateID  :=
  push (Unchecked.State.ChangeFrameStep 0 0)

private def add_remove_state : CompilerM Unchecked.StateID  :=
  push (Unchecked.State.RemoveFrameStep 0)

private def add_next_char (offset : Nat) : CompilerM Unchecked.StateID  :=
  push (Unchecked.State.NextChar offset 0)

private def c_empty : CompilerM ThompsonRef :=
  push' (Unchecked.State.Empty 0)

private def add_sparse (trans : Array Unchecked.Transition) : CompilerM Unchecked.StateID  :=
  push (Unchecked.State.SparseTransitions trans)

private def c_unicode_class (cls : ClassUnicode) : CompilerM ThompsonRef := do
  let «end» ← add_empty
  let trans : Array Unchecked.Transition :=
    cls.set.intervals.map (fun r => ⟨r.fst.val, r.snd.val, «end»⟩)
  let start ← add_sparse trans
  pure ⟨start, «end»⟩

private def c_literal (c : Char) : CompilerM ThompsonRef :=
  c_range c.val c.val

private def c_look : Syntax.Look -> CompilerM ThompsonRef
  | .Start => push' (Unchecked.State.Look NFA.Look.Start 0)
  | .End => push' (Unchecked.State.Look NFA.Look.End 0)
  | .EndWithOptionalLF => push' (Unchecked.State.Look NFA.Look.EndWithOptionalLF 0)
  | .StartLF => push' (Unchecked.State.Look NFA.Look.StartLF 0)
  | .EndLF => push' (Unchecked.State.Look NFA.Look.EndLF 0)
  | .StartCRLF => push' (Unchecked.State.Look NFA.Look.StartCRLF 0)
  | .EndCRLF => push' (Unchecked.State.Look NFA.Look.EndCRLF 0)
  | .WordUnicode => push' (Unchecked.State.Look NFA.Look.WordUnicode 0)
  | .WordUnicodeNegate => push' (Unchecked.State.Look NFA.Look.WordUnicodeNegate 0)
  | .WordStartUnicode => push' (Unchecked.State.Look NFA.Look.WordStartUnicode 0)
  | .WordEndUnicode => push' (Unchecked.State.Look NFA.Look.WordEndUnicode 0)
  | .WordStartHalfUnicode => push' (Unchecked.State.Look NFA.Look.WordStartHalfUnicode 0)
  | .WordEndHalfUnicode => push' (Unchecked.State.Look NFA.Look.WordEndHalfUnicode 0)
  | .PreviousMatch => push' (Unchecked.State.Look NFA.Look.PreviousMatch 0)
  | .ClearMatches => push' (Unchecked.State.Look NFA.Look.ClearMatches 0)

private def c_cap' (role : Capture.Role) (pattern_id slot: Nat) : CompilerM Unchecked.StateID  :=
  push (Unchecked.State.Capture role 0 0 pattern_id slot)

mutual

private def c_concat (hirs : Array Hir) : CompilerM ThompsonRef := do
  match h : hirs.head? with
  | some (head, tail) =>
    have : sizeOf head < sizeOf hirs := Array.sizeOf_head?_of_mem h
    let ⟨start, «end»⟩ ← c head

    have : sizeOf tail < sizeOf hirs := Array.sizeOf_head?_of_tail h
    let hir ← tail.attach.foldlM (init := «end»)
      (fun s (h : { x // x ∈ tail}) => do
        have : sizeOf h.val < sizeOf tail := Array.sizeOf_lt_of_mem h.property
        let hir ← c h.val
        patch s hir.start
        pure hir.end)

    pure ⟨start, hir⟩
  | none => c_empty
termination_by sizeOf hirs

private def c_alt_iter (hirs : Array Hir) : CompilerM ThompsonRef := do
  match hHead : hirs.head? with
  | some (first, tail) =>
    have : sizeOf tail < sizeOf hirs := Array.sizeOf_head?_of_tail hHead
    match hTail : tail.head? with
    | some (second, tail') =>
      have : sizeOf first < sizeOf hirs := Array.sizeOf_head?_of_mem hHead
      let first ← c first
      have : sizeOf second < sizeOf tail := Array.sizeOf_head?_of_mem hTail
      let second ← c second
      let union ← add_union
      let «end» ← add_empty

      patch union first.start
      patch first.end «end»
      patch union second.start
      patch second.end «end»

      have : sizeOf tail' < sizeOf tail := Array.sizeOf_head?_of_tail hTail
      tail'.attach.forM
        (fun (h : { x // x ∈ tail'}) => do
          have : sizeOf h.val < sizeOf tail' := Array.sizeOf_lt_of_mem h.property
          let compiled ← c h.val
          patch union compiled.start
          patch compiled.end «end»)

      pure ⟨union, «end»⟩
    | none => Except.error "c_alt_iter, size > 1 expected"
  | none => Except.error "c_alt_iter, size > 0 expected"
termination_by sizeOf hirs

private def c_exactly (hir : Hir) (n : Nat) : CompilerM ThompsonRef := do
  if 0 < n then
    let ⟨start, «end»⟩ ← c hir
    let s ← (List.replicate (n-1) 0).foldlM (init := «end»)
      (fun s _ => do
        let ref ← c hir
        patch s ref.start
        pure ref.end)
    pure ⟨start, s⟩
  else c_empty
termination_by sizeOf hir + sizeOf n

/-- embed `start` to `end` states in a possessive union,
    i.e. remove backtracking frames from stack if `end` state is reached
-/
private def c_possessive (tref : ThompsonRef) : CompilerM ThompsonRef := do
  let union ← add_union
  let fail ← add_fail
  let eat ← add_eat (Unchecked.EatMode.ToLast 0)
  let empty ← add_empty

  patch union tref.start
  patch tref.«end» eat
  patch union fail
  patch eat fail
  patch eat empty
  pure ⟨union, empty⟩

/-- Compile the given expression such that it may be matched `n` or more times -/
private def c_at_least (hir : Hir) (n : Nat) (greedy : Bool) (possessive : Bool) : CompilerM ThompsonRef := do
  if n = 0 then
    /- compile x* as (x+)?, which preserves the correct preference order
        if x can match the empty string. -/
    let compiled ← c hir
     let plus ← (if greedy then add_union else add_union_reverse)

    patch compiled.end plus
    patch plus compiled.start

    let question ← (if greedy then add_union else add_union_reverse)
    let empty ← add_empty
    patch question compiled.start
    patch question empty
    patch plus empty

    if possessive then
      c_possessive ⟨question, empty⟩
    else
      pure ⟨question, empty⟩
  else if n = 1 then
    let compiled ← c hir
    let union ← (if greedy then add_union else add_union_reverse)

    patch compiled.end union
    patch union compiled.start

    if possessive then
      c_possessive ⟨compiled.start, union⟩
    else
      pure ⟨compiled.start, union⟩
  else
    let «prefix» ← c_exactly hir (n-1)
    let last ← c hir
    let union ← (if greedy then add_union else add_union_reverse)

    patch «prefix».end last.start
    patch last.end union
    patch union last.start

    if possessive then
      c_possessive  ⟨«prefix».start, union⟩
    else
      pure ⟨«prefix».start, union⟩
termination_by sizeOf hir + sizeOf n + 1

/-- Compile the given expression such that it matches at least `min` times,
    but no more than `max` times.-/
private def c_bounded (hir : Hir) (min max : Nat) (greedy : Bool) (possessive : Bool)
    : CompilerM ThompsonRef := do
  if h : 0 < max then
    let «prefix» ← c_exactly hir min
    if min = max then
      if possessive then
        c_possessive «prefix»
      else
        pure «prefix»
    else
      let empty ← add_empty
      let prev_end ← (List.replicate (max-min) 0).foldlM (init := «prefix».end)
        (fun prev_end _ => do
          let compiled ← c hir
          let union ← (if greedy then add_union else add_union_reverse)

          patch prev_end union
          patch union compiled.start

          if possessive then
            let union ← add_union
            let fail ← add_fail
            let eat ← add_eat (Unchecked.EatMode.ToLast 0)

            patch union fail
            patch eat fail
            patch eat empty

            pure compiled.end
          else
            patch union empty
            pure compiled.end)
      patch prev_end empty
      pure ⟨«prefix».start, empty⟩
  else c_empty
termination_by sizeOf hir + sizeOf min + sizeOf max

private def c_back_ref (case_insensitive : Bool) (n : Nat) : CompilerM ThompsonRef := do
  let backrefence ← add_backrefence case_insensitive n
  let empty ← add_empty
  patch backrefence empty
  pure ⟨backrefence, empty⟩

private def c_lookaround (look : Lookaround) : CompilerM ThompsonRef := do
  match look with
  | .PositiveLookahead h =>
    let compiled ← c h
    let change_state ← add_change_state
    let fail ← add_fail
    let union ← add_union
    let «end» ← add_empty

    patch compiled.end change_state
    patch union compiled.start
    patch change_state fail
    patch change_state «end»
    patch union fail

    pure ⟨union, «end»⟩
  | .NegativeLookahead h =>
    let compiled ← c h
    let remove_state ← add_remove_state
    let empty ← add_empty
    let union ← add_union
    let «end» ← add_empty

    patch compiled.end remove_state
    patch remove_state empty
    patch union compiled.start
    patch empty «end»
    patch union empty

    pure ⟨union, «end»⟩
  | .PositiveLookbehind length h =>
    let next_char ← add_next_char length
    let compiled ← c h
    let «end» ← add_empty

    patch next_char compiled.start
    patch compiled.end «end»

    pure ⟨next_char, «end»⟩
  | .NegativeLookbehind length h =>
    let next_char ← add_next_char length
    let compiled ← c h
    let remove_state ← add_remove_state
    let empty ← add_empty
    let union ← add_union
    let «end» ← add_empty

    patch next_char compiled.start
    patch compiled.end remove_state
    patch remove_state empty
    patch union next_char
    patch empty «end»
    patch union empty

    pure ⟨union, «end»⟩
termination_by sizeOf look

private def c_repetition (rep : Repetition) : CompilerM ThompsonRef := do
  match rep with
  | .mk 0 (some 1) greedy false h => do
      let union ← if greedy then add_union else add_union_reverse
      let compiled ← c h
      let empty ← add_empty
      patch union compiled.start
      patch union empty
      patch compiled.end empty
      pure ⟨union, empty⟩
  | .mk 0 (some 1) _ true h => do
      let union ← add_union
      let compiled ← c h
      let eat ← add_eat (Unchecked.EatMode.Until 0)
      let empty ← add_empty
      patch union compiled.start
      patch union empty
      patch compiled.end eat
      patch eat empty
      patch eat empty
      pure ⟨union, empty⟩
  | .mk min none greedy possessive sub => do
      let cannotMatchEmptyString : Bool :=
        match sub.properties.minimum_len with
        | some n => n > 0
        | none => false
      if min = 0 && cannotMatchEmptyString
      then
        let union ← if greedy then add_union else add_union_reverse
        let compiled ← c sub
        patch union compiled.start
        patch compiled.end union
        pure ⟨union, union⟩
      else c_at_least sub min greedy possessive
  | .mk min (some max) greedy possessive sub =>
      if min ≤ max then c_bounded sub min max greedy possessive else c_empty
termination_by sizeOf rep

private def c (hir : Hir) : CompilerM ThompsonRef :=
  have : sizeOf hir.kind < sizeOf hir := Hir.sizeOfKindOfHir hir
  match h : hir.kind with
  | .Empty => c_empty
  | .Literal c => c_literal c
  | .Class (.Unicode cls) => c_unicode_class cls
  | .Look look => c_look look
  | .Lookaround look =>
    have : sizeOf look < sizeOf hir.kind := by simp [h]; omega
    c_lookaround look
  | .BackRef f n => c_back_ref f n
  | .Repetition rep =>
    have : sizeOf rep < sizeOf hir.kind := by simp [h]; omega
    c_repetition rep
  | .Capture cap =>
    have : sizeOf cap < sizeOf hir.kind := by simp [h]; omega
    c_cap cap
  | .Concat items =>
    have : sizeOf items < sizeOf hir.kind := by simp [h]; omega
    c_concat items
  | .Alternation sub =>
    have : sizeOf sub < sizeOf hir.kind := by simp [h]; omega
    c_alt_iter sub
termination_by sizeOf hir

private def c_cap (hir : Capture) : CompilerM ThompsonRef := do
  match hc : hir with
    | .mk pattern_id name sub =>
      let start ← c_cap' Capture.Role.Start pattern_id (pattern_id * 2)
      let inner ← c sub
      let «end» ← c_cap' Capture.Role.End pattern_id (pattern_id * 2 + 1)
      patch start inner.start
      patch inner.end «end»
      pure ⟨start, «end»⟩
termination_by sizeOf hir

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
  let unanchored_prefix ←
    if anchored then c_empty
    else c_repetition <| Repetition.mk 0 none false false (dot Dot.AnyChar)
  let one ← c_cap (Capture.mk 0 none expr)
  let match_state_id ← add_match 0
  patch one.end match_state_id
  patch unanchored_prefix.end one.start

/-- Compile the HIR expression given. -/
def compile (config : Config := default) (expr : Hir) : Except String Checked.NFA := do
  let unanchored_prefix_simulation := expr.containsLookaround || config.unanchored_prefix_simulation
  let anchored := !config.unanchored_prefix || startsWithStart expr || unanchored_prefix_simulation
  let (_, states) ← compile' anchored expr #[]
  let nfa ← NFA.toCkecked ⟨states, 0, 0⟩
  Except.ok {nfa with unanchored_prefix_in_backtrack :=
                  !startsWithStart expr && unanchored_prefix_simulation
            }
