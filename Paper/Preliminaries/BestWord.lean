import Paper.Preliminaries.SolutionWord

/-! Computable minimum-cost folding of optional solution words, used by
the fixed sequence of recursive branch calls. No graph/oracle is involved. -/
namespace Paper.BestWord
variable {V : Type} [DecidableEq V] {B : ℕ}

def better (old new : Option (SolutionWord.Word V B)) : Option (SolutionWord.Word V B) :=
  match old, new with
  | none, x => x
  | x, none => x
  | some a, some b => if SolutionWord.cost b < SolutionWord.cost a then some b else some a

def fold (old : Option (SolutionWord.Word V B)) : List (Option (SolutionWord.Word V B)) → Option (SolutionWord.Word V B)
  | [] => old
  | x :: xs => fold (better old x) xs

theorem better_sound (P : SolutionWord.Word V B → Prop) (old new : Option (SolutionWord.Word V B))
    (ho : ∀ w, old = some w → P w) (hn : ∀ w, new = some w → P w) :
    ∀ w, better old new = some w → P w := by
  cases old with
  | none => exact hn
  | some a =>
    cases new with
    | none => exact ho
    | some b =>
      by_cases h : SolutionWord.cost b < SolutionWord.cost a
      · simpa only [better, if_pos h] using hn
      · simpa only [better, if_neg h] using ho

theorem better_le_old (old new : Option (SolutionWord.Word V B)) {w : SolutionWord.Word V B}
    (ho : old = some w) : ∃ r, better old new = some r ∧ SolutionWord.cost r ≤ SolutionWord.cost w := by
  subst old
  cases new with
  | none => exact ⟨w, rfl, le_rfl⟩
  | some r =>
    by_cases h : SolutionWord.cost r < SolutionWord.cost w
    · exact ⟨r, by simp [better, h], h.le⟩
    · exact ⟨w, by simp [better, h], le_rfl⟩

theorem better_le_new (old new : Option (SolutionWord.Word V B)) {w : SolutionWord.Word V B}
    (hn : new = some w) : ∃ r, better old new = some r ∧ SolutionWord.cost r ≤ SolutionWord.cost w := by
  subst new
  cases old with
  | none => exact ⟨w, rfl, le_rfl⟩
  | some r =>
    by_cases h : SolutionWord.cost w < SolutionWord.cost r
    · exact ⟨w, by simp [better, h], le_rfl⟩
    · exact ⟨r, by simp [better, h], le_of_not_gt h⟩

theorem fold_sound (P : SolutionWord.Word V B → Prop) (old : Option (SolutionWord.Word V B))
    (xs : List (Option (SolutionWord.Word V B))) (ho : ∀ w, old = some w → P w)
    (hx : ∀ x ∈ xs, ∀ w, x = some w → P w) : ∀ w, fold old xs = some w → P w := by
  induction xs generalizing old with
  | nil => exact ho
  | cons x xs ih =>
    exact ih (better old x) (better_sound P old x ho (hx x List.mem_cons_self))
      (fun y hy => hx y (List.mem_cons_of_mem x hy))

theorem fold_le_old (old : Option (SolutionWord.Word V B)) (xs : List (Option (SolutionWord.Word V B)))
    {w : SolutionWord.Word V B} (ho : old = some w) :
    ∃ r, fold old xs = some r ∧ SolutionWord.cost r ≤ SolutionWord.cost w := by
  induction xs generalizing old w with
  | nil => exact ⟨w, ho, le_rfl⟩
  | cons x xs ih =>
    obtain ⟨r, hr, hcost⟩ := better_le_old old x ho
    obtain ⟨p, hp, hpcost⟩ := ih (better old x) hr
    exact ⟨p, hp, hpcost.trans hcost⟩

theorem fold_le_member (old : Option (SolutionWord.Word V B)) (xs : List (Option (SolutionWord.Word V B)))
    {w : SolutionWord.Word V B} (hw : some w ∈ xs) :
    ∃ r, fold old xs = some r ∧ SolutionWord.cost r ≤ SolutionWord.cost w := by
  induction xs generalizing old with
  | nil => simp at hw
  | cons x xs ih =>
    rcases List.mem_cons.mp hw with hx | hx
    · obtain ⟨r, hr, hcost⟩ := better_le_new old x hx.symm
      obtain ⟨p, hp, hpcost⟩ := fold_le_old (better old x) xs hr
      exact ⟨p, hp, hpcost.trans hcost⟩
    · exact ih (better old x) hx
end Paper.BestWord
