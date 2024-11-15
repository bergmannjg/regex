namespace Array

/-- get head element and array without head element -/
def head? (a : Array α) : Option (α × Array α) :=
  match a.toList with
  | [] => none
  | List.cons head tail => some (head, ⟨tail⟩)

/-- get last element and array without last element -/
def pop? (a : Array α) : Option (α × Array α) :=
  if h : 0 < a.toList.length
  then some ((a.toList.get ⟨a.toList.length - 1, Nat.sub_lt h Nat.one_pos⟩), a.pop)
  else none

/-- get last element of array -/
def last? (a : Array α) : Option α :=
  if h : 0 < a.toList.length
  then a.toList.get ⟨a.toList.length - 1, Nat.sub_lt h Nat.one_pos⟩
  else none

/-- unique array of sorted array -/
def unique [BEq α] (intervals: Array α) : Array α :=
  match intervals.toList with
  | [] => #[]
  | [r] => #[r]
  | head :: tail  =>
    let (_, unique) := tail |> List.foldl (init := (head, #[head]))
      (fun (prev, unique) r =>
        if prev == r then (r, unique)
        else (r, unique.push r))
    unique
