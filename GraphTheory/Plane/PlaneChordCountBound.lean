import GraphTheory.Plane.PlanePermutationSurgery

/-!
# A chord changes the actual face count by at most one

The upper bound also applies when the two chosen corners are on different
faces. It is the missing numerical ingredient for constructing edge deletion:
the cellular Euler inequality then forces a connected restriction to be plane.
-/

namespace PlaneTopology.PlaneChordCountBound

open Equiv Equiv.Perm PlaneTopology.PlanePermutationSurgery

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A transposition between distinct permutation orbits joins its endpoints.
The proof follows the old orbit until its first positive return. -/
theorem sameCycle_swap_mul_of_not_sameCycle (p : Perm α) (a b : α)
    (hnot : ¬p.SameCycle a b) : (swap a b * p).SameCycle a b := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ (p ^ n) b = b :=
    ⟨orderOf p, orderOf_pos p, by simp⟩
  let n := Nat.find hex
  have hn : 0 < n ∧ (p ^ n) b = b := Nat.find_spec hex
  let q := swap a b * p
  have hpow : ∀ k < n, (q ^ k) b = (p ^ k) b := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hpa : (p ^ (k + 1)) b ≠ a := by
        intro h
        apply hnot
        exact (show p.SameCycle b a from ⟨(k + 1 : ℕ), by simpa using h⟩).symm
      have hpb : (p ^ (k + 1)) b ≠ b := by
        intro h
        exact Nat.find_min hex hk ⟨by omega, h⟩
      rw [pow_succ', mul_apply, ih (by omega)]
      change swap a b (p ((p ^ k) b)) = _
      have hstep : p ((p ^ k) b) = (p ^ (k + 1)) b := by
        rw [pow_succ', mul_apply]
      rw [hstep, swap_apply_of_ne_of_ne hpa hpb]
  have hlast : (q ^ n) b = a := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    change n = k + 1 at hk
    rw [hk, pow_succ', mul_apply, hpow k (by omega)]
    change swap a b (p ((p ^ k) b)) = a
    have hstep : p ((p ^ k) b) = (p ^ (k + 1)) b := by
      rw [pow_succ', mul_apply]
    rw [hstep, ← hk, hn.2, swap_apply_right]
  exact (show q.SameCycle b a from ⟨n, by simpa using hlast⟩).symm

/-- Joining two nontrivial disjoint orbits decreases the cycle count by one. -/
theorem cycleType_card_swap_mul_of_not_sameCycle (p : Perm α) (a b : α)
    (hnot : ¬p.SameCycle a b) (ha : p a ≠ a) (hb : p b ≠ b) :
    (swap a b * p).cycleType.card + 1 = p.cycleType.card := by
  have hab : a ≠ b := fun h => hnot (h ▸ SameCycle.refl p a)
  have hqa : (swap a b * p) a ≠ b := by
    intro h
    apply ha
    exact (swap a b).injective (h.trans (swap_apply_left a b).symm)
  have hqb : (swap a b * p) b ≠ a := by
    intro h
    apply hb
    exact (swap a b).injective (h.trans (swap_apply_right a b).symm)
  have h := cycleType_card_swap_mul_of_sameCycle (swap a b * p) a b hab
    (sameCycle_swap_mul_of_not_sameCycle p a b hnot) hqa hqb
  simpa using h.symm

/-- A swap at two moved, nonadjacent positions raises the cycle count by at
most one, with no assumption that the positions belong to the same orbit. -/
theorem cycleType_card_swap_mul_le (p : Perm α) (a b : α) (hab : a ≠ b)
    (ha : p a ≠ a) (hb : p b ≠ b) (hab' : p a ≠ b) (hba' : p b ≠ a) :
    (swap a b * p).cycleType.card ≤ p.cycleType.card + 1 := by
  by_cases hcycle : p.SameCycle a b
  · rw [cycleType_card_swap_mul_of_sameCycle p a b hab hcycle hab' hba']
  · have h := cycleType_card_swap_mul_of_not_sameCycle p a b hcycle ha hb
    omega

/-- Inserting the two new orientations of a chord raises the number of
actual nontrivial facial cycles by at most one, on one or on two old faces. -/
theorem cycleType_card_chordPerm_le (p : Perm α) (a b : α)
    (hab : a ≠ b) (ha : p a ≠ a) (hb : p b ≠ b) :
    (chordPerm p a b).cycleType.card ≤ p.cycleType.card + 1 := by
  classical
  let p₀ : Perm (α ⊕ Bool) := Equiv.sumCongr p (Equiv.refl Bool)
  let p₁ := swap (Sum.inl a) (Sum.inr false) * p₀
  let p₂ := swap (Sum.inl b) (Sum.inr true) * p₁
  have hp₀N : p₀ (Sum.inr false) = Sum.inr false := rfl
  have hp₀a : p₀ (Sum.inl a) ≠ Sum.inl a := by simpa [p₀] using ha
  have hp₁M : p₁ (Sum.inr true) = Sum.inr true := by
    simp [p₁, p₀, mul_apply, Equiv.swap_apply_def]
  have hp₁b : p₁ (Sum.inl b) ≠ Sum.inl b := by
    by_cases hpa : p b = a <;> simp_all [p₁, p₀, mul_apply, Equiv.swap_apply_def]
  have hp₁N : p₁ (Sum.inr false) = Sum.inl a := by simp [p₁, p₀, mul_apply]
  have hp₂N : p₂ (Sum.inr false) = Sum.inl a := by
    simp [p₂, mul_apply, hp₁N, Equiv.swap_apply_def, hab]
  have hp₂M : p₂ (Sum.inr true) = Sum.inl b := by simp [p₂, mul_apply, hp₁M]
  have hp₂a : p₂ (Sum.inl a) ≠ Sum.inl b := by
    intro h
    have := p₂.injective (h.trans hp₂M.symm)
    contradiction
  have hp₂b : p₂ (Sum.inl b) ≠ Sum.inl a := by
    intro h
    have := p₂.injective (h.trans hp₂N.symm)
    contradiction
  have hp₂aa : p₂ (Sum.inl a) ≠ Sum.inl a := by
    intro h
    have := p₂.injective (h.trans hp₂N.symm)
    contradiction
  have hp₂bb : p₂ (Sum.inl b) ≠ Sum.inl b := by
    intro h
    have := p₂.injective (h.trans hp₂M.symm)
    contradiction
  have hcount₀ : p₀.cycleType.card = p.cycleType.card := by
    rw [cycleType_sumCongr_refl (β := Bool)]
  have hcount₁ : p₁.cycleType.card = p₀.cycleType.card :=
    cycleType_card_swap_mul_of_fixed p₀ _ _ hp₀a hp₀N
  have hcount₂ : p₂.cycleType.card = p₁.cycleType.card :=
    cycleType_card_swap_mul_of_fixed p₁ _ _ hp₁b hp₁M
  rw [chordPerm_factorization p a b hab]
  change (swap (Sum.inl a) (Sum.inl b) * p₂).cycleType.card ≤ _
  have h := cycleType_card_swap_mul_le p₂ _ _ (by simpa using hab)
    hp₂aa hp₂bb hp₂a hp₂b
  simpa only [hcount₂, hcount₁, hcount₀] using h

#print axioms sameCycle_swap_mul_of_not_sameCycle
#print axioms cycleType_card_swap_mul_of_not_sameCycle
#print axioms cycleType_card_chordPerm_le

end PlaneTopology.PlaneChordCountBound
