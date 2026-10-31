import Paper.Solver.Density.RationalEpochDecay

/-! Finite summation of epoch charges. Normalizing the requirement mass by
the current geometric threshold replaces the continuous logarithm argument. -/
namespace Paper.Density.RationalChargeSeries
open scoped BigOperators

theorem weighted_prefix (a d : ℕ → ℝ) (N : ℕ) (C q M : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : ∀ j, j ≤ N → a j ≤ M)
    (hd : ∀ j, j < N → d j ≤ C * (a j - q * a (j + 1))) :
    (∑ j ∈ Finset.range N, d j) + C * q * a N ≤
      C * q * a 0 + C * M * (N : ℝ) * (1 - q) := by
  have hp : ∀ j, j ≤ N →
      (∑ i ∈ Finset.range j, d i) + C * q * a j ≤
        C * q * a 0 + C * M * (j : ℝ) * (1 - q) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hstep := hd j (by omega)
      have hmass := mul_le_mul_of_nonneg_left (ha j (by omega))
        (mul_nonneg hC (sub_nonneg.mpr hq1))
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith
  exact hp N le_rfl

theorem total_charge_bound (a d : ℕ → ℝ) (N : ℕ) (C q M : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : ∀ j, j ≤ N → a j ≤ M) (haN : 0 ≤ a N)
    (hd : ∀ j, j < N → d j ≤ C * (a j - q * a (j + 1))) :
    (∑ j ∈ Finset.range N, d j) ≤ C * M * (q + (N : ℝ) * (1 - q)) := by
  have hp := weighted_prefix a d N C q M hC hq hq1 ha hd
  have hterminal : 0 ≤ C * q * a N := mul_nonneg (mul_nonneg hC hq) haN
  have hinitial := mul_le_mul_of_nonneg_left (ha 0 (Nat.zero_le N)) (mul_nonneg hC hq)
  nlinarith

end Paper.Density.RationalChargeSeries

#print axioms Paper.Density.RationalChargeSeries.weighted_prefix
#print axioms Paper.Density.RationalChargeSeries.total_charge_bound
