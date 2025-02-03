import Init.Data.Random
import Regex
import Regex.Backtrack

open NFA
open Syntax
open Regex
open BoundedBacktracker

instance : MonadLift (Except String) IO where
  monadLift e :=
    match e with
    | Except.ok res => pure res
    | Except.error e => throw $ .userError e

private def stack_ops (stack : Stack 1) : Nat × Stack 1 :=
  let frameStep : Frame 1 := Frame.Step default default
  let frameRestoreCapture : Frame 1 := Frame.RestoreCapture Capture.Role.Start default default
  let stack := Stack.push stack frameStep
  let stack := Stack.push stack frameRestoreCapture
  match Stack.pop? stack with
  | some (_, stack) =>
      match Stack.pop? stack with
    | some (_, stack) => (4, stack)
    | none => (3, stack)
  | none => (2, stack)

private def ref_loop (n : Nat) (ref : ST.Ref Nat (Array UInt8)) : ST.Ref Nat (Array UInt8) :=
  if n = 0 then ref
  else
    let ref := BoundedBacktracker.Array.Ref.modifyRefValue ref n 1
    ref_loop (n-1) ref

private def createText (c1 c2 : Char) (n : Nat): String :=
  if c1.val < c2.val then
    let size :=  c2.val - c1.val |>.toNat
    let (content, _) : (List Char) × StdGen := n.fold (init := ([], mkStdGen n))
          (fun _ _ (content, generator) =>
            let (n, generator) := randNat generator 0 size
            if h : UInt32.isValidChar (c1.val + n.toUInt32)
            then (⟨c1.val + n.toUInt32, h⟩ :: content, generator)
            else (content, generator))
    ⟨content⟩
  else ""

def main (args : List String): IO Unit := do
  try {
    match args with
    | ["pattern", n] =>
        match n.toNat? with
        | some n =>
          let a? : String := List.replicateTR n "a?" |> String.join
          let a : String := ⟨List.replicateTR n 'a'⟩
          let re := a? ++ a
          let haystack := a
          IO.println s!"re {re} haystack {haystack}"
          let nl := "\n"

          let regex ← build re default default ⟨true, false⟩
          match Regex.Log.captures haystack.toSubstring regex default (logEnabled := false) with
          | (msgs, none) =>
            if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
            IO.println s!"captures: none"
          | (msgs, some res) =>
            if msgs.size > 0 then IO.println s!"msgs {msgs |> Array.map (· ++ nl)}"
            IO.println s!"{res}"

        | none => IO.println "Nat expected"
    | ["pattern", n, m] =>
        match n.toNat?, m.toNat? with
        | some n, some m =>
          let a? : String := List.replicateTR n "a?" |> String.join
          let a : String := ⟨List.replicateTR n 'a'⟩
          let re := a? ++ a
          let haystack := a
          IO.println s!"re {re} haystack {haystack}"

          let regex ← build re default default ⟨true, false⟩

          let count :=
            m.fold (init := 0) (fun acc _ _ =>
                let incr :=
                  match Regex.captures haystack.toSubstring regex with
                  | none => 0
                  | some _ => 1
                acc + incr)
          IO.println s!"matches {count}"
        | _, _ => IO.println "Nat expected"
    | ["visit", n, m] => -- check performance of Array.Ref
        match n.toNat?, m.toNat? with
        | some n, some m =>
          let size : Nat := m
          let loops : Nat := n
          if loops < size then
            let ref : ST.Ref Nat (Array UInt8) := Array.Ref.mkRef <| Array.mkArray size 0
            let ref := ref_loop loops ref
            let arr := Array.Ref.getRefValue ref
            let marked := arr |> Array.foldl (fun acc n => if n = 0 then acc else acc + 1) 0
            IO.println s!"arr {arr.size}, marked {marked}"
        | _, _ => IO.println "Nat expected"
    | ["split", sep, "-f", path] => -- check performance of Substring.splitOn
        let haystack ← IO.FS.readFile path
        let splits := haystack.toSubstring.splitOn sep
                      |> List.map (fun s => (s.startPos, s.stopPos))
        IO.println s!"splits {splits}"
    | ["stack", n] => -- check performance of Stack
        match n.toNat? with
        | some n =>
          let (ops, stack) : Nat × Stack 1 := n.fold
              (fun _ _ (ops, acc) => let (n, stack) := stack_ops acc; (n+ops, stack)) default
          IO.println s!"ops {ops}, stack {stack}"
        | none => IO.println "Nat expected"
    | ["randomfile", n, a, z, suffix] => -- create file with random content
        match n.toNat? with
        | some n  =>
          let content := createText (a.get 0) (z.get 0) n |>.append suffix
          IO.println content
        | _ => IO.println "Nat expected"
    | _ => IO.println
            "usage: [pattern <n> [<m>]"
  }
  catch e => IO.println s!"error: {e}"
