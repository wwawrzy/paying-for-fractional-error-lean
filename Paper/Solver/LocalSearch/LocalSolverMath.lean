import Paper.Certificates.Counting.PartialOptimum

/-! Mathematical bounded local fractional solver, including attained optimum,
fixed common denominator and actual exact search. Broadcast execution remains open. -/
namespace Paper.LocalSolverMath
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def denominator (a : ℕ) (xi : ℝ) : ℕ := ⌈2 * (a : ℝ) / xi⌉₊ + 1

theorem denominator_pos (a : ℕ) (xi : ℝ) : 1 ≤ denominator a xi := by
  unfold denominator
  omega

theorem denominator_accuracy (a : ℕ) (xi : ℝ) (hxi : 0 < xi) :
    2 * (a : ℝ) / denominator a xi ≤ xi := by
  have hq : (0 : ℝ) < denominator a xi := by
    exact_mod_cast (by have h := denominator_pos a xi; omega : 0 < denominator a xi)
  have hceil := Nat.le_ceil (2 * (a : ℝ) / xi)
  have hbound : 2 * (a : ℝ) / xi ≤ denominator a xi := by
    dsimp [denominator]
    push_cast
    linarith
  have hmul := (div_le_iff₀ hxi).mp hbound
  exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hmul)

/-- This theorem constructs the finite search output and proves its guarantee.
It does not claim a distributed implementation of the search. -/
theorem local_solver (R : Finset V) (t : ℝ) (ht : 1 ≤ t)
    (hden : Incidence.InducedDensityBound G t) (a : ℕ) (ha : 1 ≤ a) (hat : t ≤ a)
    (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (K xi : ℝ) (hxi : 0 < xi)
    (hK : PartialOptimum.number G R c ≤ K) :
    ∃ p : V → ℕ,
      LocalFractional.best G t c ⌈(denominator a xi + 2 * (a : ℝ)) * K⌉₊
        (LocalFractional.demand R (denominator a xi)) = some p ∧
      (∀ v, 0 ≤ LocalFractional.vector (denominator a xi) p v) ∧
      (∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, LocalFractional.vector (denominator a xi) p v) ∧
      (∑ v, c v * LocalFractional.vector (denominator a xi) p v) ≤
        (1 + xi) * PartialOptimum.number G R c ∧
      ∀ v, (denominator a xi : ℝ) * LocalFractional.vector (denominator a xi) p v = p v := by
  have hcn : ∀ v, 0 ≤ c v := fun v => le_trans zero_le_one (hc v)
  obtain ⟨x, hx, hopt⟩ := PartialOptimum.exists_optimum_eq_number G R c hcn
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density G hden a hat
  obtain ⟨p, hp, hpcover, hpcost⟩ := LocalFractional.best_approximation G R t ht O ha
    (denominator a xi) (denominator_pos a xi) c x hc hx.1 hx.2 K (by change PartialOptimum.objective c x ≤ K; rw [hopt]; exact hK)
  have hnonneg : 0 ≤ PartialOptimum.number G R c := by
    rw [← hopt]
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (hcn v) (hx.1 v))
  refine ⟨p, hp, LocalFractional.vector_nonneg _ p, hpcover, ?_, ?_⟩
  · change (∑ v, c v * LocalFractional.vector (denominator a xi) p v) ≤ _
    change (∑ v, c v * LocalFractional.vector (denominator a xi) p v) ≤
      (1 + 2 * (a : ℝ) / denominator a xi) * PartialOptimum.objective c x at hpcost
    rw [hopt] at hpcost
    exact hpcost.trans (mul_le_mul_of_nonneg_right
      (add_le_add (le_refl (1 : ℝ)) (denominator_accuracy a xi hxi)) hnonneg)
  · intro v
    have hq : (denominator a xi : ℝ) ≠ 0 := by
      have hp : 0 < denominator a xi := by have h := denominator_pos a xi; omega
      exact_mod_cast (Nat.ne_of_gt hp)
    unfold LocalFractional.vector
    field_simp
end Paper.LocalSolverMath
