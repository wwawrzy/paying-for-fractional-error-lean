import Paper.Preliminaries.MaskedMinimum

/-! Exact finite minimum enumeration used as the mathematical specification
of repeated, locally computed task minimum queries. -/
namespace Paper.MinimumList
variable {V : Type} [LinearOrder V]

def next (S : Finset V) (l : List V) : List V :=
  match MaskedMinimum.minimum (S \ l.toFinset) with
  | none => l
  | some u => l ++ [u]

def run (S : Finset V) : ℕ → List V
  | 0 => []
  | n + 1 => next S (run S n)

theorem minimum_none (S : Finset V) (h : MaskedMinimum.minimum S = none) : S = ∅ := by
  unfold MaskedMinimum.minimum at h
  split at h
  · contradiction
  · exact Finset.not_nonempty_iff_eq_empty.mp ‹¬S.Nonempty›

theorem next_length (S : Finset V) (l : List V) : (next S l).length ≤ l.length + 1 := by
  cases h : MaskedMinimum.minimum (S \ l.toFinset) <;> simp [next, h]

theorem next_subset (S : Finset V) (l : List V) (hl : l.toFinset ⊆ S) :
    (next S l).toFinset ⊆ S := by
  cases h : MaskedMinimum.minimum (S \ l.toFinset) with
  | none => simpa only [next, h] using hl
  | some u =>
    have hu := Finset.mem_sdiff.mp (MaskedMinimum.minimum_mem h)
    simp only [next, h, List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    exact Finset.union_subset hl (by simpa using hu.1)

theorem next_nodup (S : Finset V) (l : List V) (hl : l.Nodup) : (next S l).Nodup := by
  cases h : MaskedMinimum.minimum (S \ l.toFinset) with
  | none => simpa only [next, h] using hl
  | some u =>
    have hu : u ∉ l := by simpa using (Finset.mem_sdiff.mp (MaskedMinimum.minimum_mem h)).2
    simp [next, h, List.nodup_append, hl]
    intro a ha he
    exact hu (he ▸ ha)

theorem residual_step (S : Finset V) (l : List V) :
    (S \ (next S l).toFinset).card = (S \ l.toFinset).card - 1 := by
  cases h : MaskedMinimum.minimum (S \ l.toFinset) with
  | none =>
    have he := minimum_none (S \ l.toFinset) h
    have hn : next S l = l := by simp only [next, h]
    simp [hn, he]
  | some u =>
    have hu := MaskedMinimum.minimum_mem h
    have he : S \ (l ++ [u]).toFinset = (S \ l.toFinset).erase u := by
      ext v
      simp
      tauto
    simpa only [next, h, he] using Finset.card_erase_of_mem hu

theorem run_nodup (S : Finset V) (n : ℕ) : (run S n).Nodup := by
  induction n with
  | zero => simp [run]
  | succ n ih => exact next_nodup S (run S n) ih

theorem run_length (S : Finset V) (n : ℕ) : (run S n).length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => exact (next_length S (run S n)).trans (Nat.add_le_add_right ih 1)

theorem run_subset (S : Finset V) (n : ℕ) : (run S n).toFinset ⊆ S := by
  induction n with
  | zero => simp [run]
  | succ n ih => exact next_subset S (run S n) ih

theorem residual_card (S : Finset V) (n : ℕ) :
    (S \ (run S n).toFinset).card = S.card - n := by
  induction n with
  | zero => simp [run]
  | succ n ih => rw [run, residual_step, ih]; omega

theorem complete (S : Finset V) (n : ℕ) (hn : S.card ≤ n) : (run S n).toFinset = S := by
  have he : S \ (run S n).toFinset = ∅ := Finset.card_eq_zero.mp (by rw [residual_card]; omega)
  exact Finset.Subset.antisymm (run_subset S n) (Finset.sdiff_eq_empty_iff_subset.mp he)
end Paper.MinimumList
