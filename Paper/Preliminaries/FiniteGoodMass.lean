import Mathlib.Tactic

/-! A finite boundary budget forces at least half of the vertex mass to
belong to parts with boundary at most four times the accuracy budget. -/
namespace Paper.FiniteGoodMass
open scoped BigOperators

theorem half {ι : Type*} (F : Finset ι) (size cost : ι → ℕ) {ε : ℝ} (hε : 0 < ε)
    (hbudget : (∑ i ∈ F, (cost i : ℝ)) ≤ 2 * ε * ∑ i ∈ F, (size i : ℝ)) :
    (∑ i ∈ F, (size i : ℝ)) / 2 ≤
      ∑ i ∈ F.filter (fun i => (cost i : ℝ) ≤ 4 * ε * size i), (size i : ℝ) := by
  classical
  let P := fun i => (cost i : ℝ) ≤ 4 * ε * size i
  have hsplit := Finset.sum_filter_add_sum_filter_not F P (fun i => (size i : ℝ))
  have hbad : 4 * ε * (∑ i ∈ F.filter (fun i => ¬ P i), (size i : ℝ)) ≤ ∑ i ∈ F, (cost i : ℝ) := by
    calc
      _ = ∑ i ∈ F.filter (fun i => ¬ P i), 4 * ε * size i := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ F.filter (fun i => ¬ P i), (cost i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
  dsimp only [P] at hsplit ⊢
  nlinarith
end Paper.FiniteGoodMass
