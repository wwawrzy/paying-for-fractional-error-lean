import Paper.Preliminaries.FiniteCoordinateCount

/-! An exact finite lower bound for one zero priority and nonzero
priorities on a bounded conflict family, by a union bound. -/
namespace Paper.FiniteZeroSelection
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def good (Q : ℕ) (s : A) (T : Finset A) : Finset (A → Fin Q) :=
  Finset.univ.filter (fun ω => (ω s).val = 0 ∧ ∀ t ∈ T, (ω t).val ≠ 0)

set_option maxHeartbeats 2000000 in
theorem count (Q : ℕ) (hQ : 0 < Q) (s : A) (T : Finset A) (hs : s ∉ T)
    (hT : 2 * T.card ≤ Q) :
    Fintype.card (A → Fin Q) ≤ 2 * Q * (good Q s T).card := by
  classical
  let b : Fin Q := ⟨0, hQ⟩
  let E := Finset.univ.filter (fun ω : A → Fin Q => ω s = b)
  let B (t : A) := Finset.univ.filter (fun ω : A → Fin Q => ω s = b ∧ ω t = b)
  let W := Fintype.card (A → Fin Q)
  have hone : Q * E.card = W := FiniteCoordinateCount.one s b
  have htwo : ∀ t ∈ T, Q ^ 2 * (B t).card = W := by
    intro t ht
    exact FiniteCoordinateCount.two s t (fun he => hs (he ▸ ht)) b b
  have hcover : E ⊆ good Q s T ∪ T.biUnion B := by
    intro ω hω
    have hωs := (Finset.mem_filter.mp hω).2
    by_cases hgood : ∀ t ∈ T, (ω t).val ≠ 0
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨congrArg Fin.val hωs, hgood⟩⟩
    · push_neg at hgood
      obtain ⟨t, ht, hz⟩ := hgood
      have hωt : ω t = b := Fin.ext hz
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨t, ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hωs, hωt⟩⟩)
  have hc : E.card ≤ (good Q s T).card + ∑ t ∈ T, (B t).card :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hsum : Q ^ 2 * (∑ t ∈ T, (B t).card) = T.card * W := by
    rw [Finset.mul_sum]
    simp [Finset.sum_congr rfl htwo]
  have hmul := Nat.mul_le_mul_left (Q ^ 2) hc
  have hWT := Nat.mul_le_mul_right W hT
  have hmul' : Q * W ≤ Q ^ 2 * (good Q s T).card + T.card * W := by
    calc
      _ = Q ^ 2 * E.card := by rw [← hone]; ring
      _ ≤ Q ^ 2 * ((good Q s T).card + ∑ t ∈ T, (B t).card) := hmul
      _ = _ := by rw [Nat.mul_add, hsum]
  have hresult : Q * W ≤ Q * (2 * Q * (good Q s T).card) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hresult hQ
end Paper.FiniteZeroSelection
