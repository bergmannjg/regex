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

/-- Unattach values of subtype in `arr` and collect their properties. -/
def map_option_subtype {p : α → Prop} [DecidablePred p] (arr : Array (Option { m : α // p m }))
    : { arr : Array (Option α) // arr.all (Option.all (p · ) ·) } :=
  ⟨arr.map (Option.map (·.val)), by
    cases arr
    rename_i l
    induction l with
    | nil => rfl
    | cons a l ih =>
        rw [Array.all_eq_true_iff_forall_mem] at ih
        rw [Array.all_eq_true_iff_forall_mem]
        intros x h
        match x with
        | none => rfl
        | some x =>
          unfold Option.all
          split <;> try simp_all
          rename_i val heq
          cases h
          · rename_i h
            simp [Option.unattach, -Option.map_subtype] at h
            unfold Option.map at h
            split at h <;> try simp_all
            rename_i x
            exact x.property
          · rename_i h
            let ⟨x, hx⟩ := h
            have h := ih x hx.left
            rw [hx.right] at h
            simp_all⟩
