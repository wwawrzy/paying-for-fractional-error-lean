import Paper.Solver.Density.RationalDualPacking
import Paper.Solver.Density.RationalDualNonnegative
import Paper.Solver.Density.RationalDualFlush
import Paper.Solver.Density.RationalFeasibility
import Paper.Solver.Density.RationalParameters

/-! Approximation of the genuine rational program with an explicit public
degree parameter. This intermediate endpoint does not remove that knowledge. -/
namespace Paper.Density.RationalApproximation
open RationalRuntime RationalRequirementDecay RationalEpochDecay RationalTermination
open RationalDualLedger RationalDualFlush RationalDualNonnegative RationalPhaseCharge RationalDualPacking
open RationalFeasibility SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def normalizer (m K : ℕ) : ℝ := ((denominator m K * target m K : ℕ) : ℝ)
def factor (m : ℕ) : ℝ := (scale m : ℝ) ^ 5

theorem normalizer_pos {m K : ℕ} (hm : 1 ≤ m) : 0 < normalizer m K := by
  unfold normalizer
  exact_mod_cast denominator_pos (K := K) hm

theorem factor_pos {m : ℕ} (hm : 1 ≤ m) : 0 < factor m := by
  have hp : (0 : ℝ) < (scale m : ℚ) := by
    exact_mod_cast ((by norm_num : (0 : ℚ) < 1).trans (scale_bounds hm).1)
  exact pow_pos hp _

noncomputable def dual (m K : ℕ) (v : V) : ℝ :=
  (actualLedger G m K).paid v / (normalizer m K * factor m)

theorem dual_nonnegative {m K : ℕ} (hm : 1 ≤ m) (v : V) : 0 ≤ dual G m K v :=
  div_nonneg (actual_paid_nonnegative G hm v) (mul_pos (normalizer_pos hm) (factor_pos hm)).le

theorem dual_packing {m K : ℕ} (hm : 1 ≤ m) (hK : m ≤ K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    UnitDomination.mass G (dual G m K) v ≤ 1 := by
  unfold UnitDomination.mass dual
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (mul_pos (normalizer_pos hm) (factor_pos hm))).2
  simpa only [one_mul, normalizer, factor, paidMass, UnitDomination.mass] using actual_packing G hm hK hdegree v

theorem objectives {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) :
    (∑ v, output G m K v) = factor m * ∑ v, dual G m K v := by
  have hout : (∑ v, output G m K v) = (∑ v, (actualLedger G m K).paid v) / normalizer m K := by
    simp_rw [output_fraction]
    rw [← Finset.sum_div, ← actual_paid_eq_primal G hm hk hdegree]
    rfl
  rw [hout]
  simp only [dual, ← Finset.sum_div]
  field_simp [ne_of_gt (normalizer_pos (K := K) hm), ne_of_gt (factor_pos hm)]

/-- A comparison against every feasible LP vector, proved by the explicitly
constructed dual vector and weak duality. -/
theorem approximation {m K : ℕ} (hm : 1 ≤ m) (hK : m ≤ K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ))
    (z : V → ℝ) (hz : feasible (ordinary G) z) :
    (∑ v, output G m K v) ≤ factor m * ∑ v, z v := by
  have hparts := (UnitDomination.ordinary_feasible G z).1 hz
  have hw := UnitDomination.weak_duality G z (dual G m K) hparts.1
    (dual_nonnegative G hm) hparts.2 (dual_packing G hm hK hdegree)
  rw [objectives G hm (by omega) hdegree]
  exact mul_le_mul_of_nonneg_left hw (factor_pos hm).le

theorem factor_accuracy {m : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (haccuracy : (1 + 1 / (m : ℝ)) ^ 5 ≤ 1 + δ) : factor m ≤ 1 + δ := by
  have hp : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have he : (scale m : ℝ) = 1 + 1 / (m : ℝ) := by
    simp only [scale, Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one]
    field_simp
  simpa only [factor, he] using haccuracy

theorem near_optimal {m K : ℕ} (hm : 1 ≤ m) (hK : m ≤ K) {δ : ℝ}
    (haccuracy : (1 + 1 / (m : ℝ)) ^ 5 ≤ 1 + δ)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ))
    (z : V → ℝ) (hz : feasible (ordinary G) z) :
    (∑ v, output G m K v) ≤ (1 + δ) * ∑ v, z v := by
  have hz0 := ((UnitDomination.ordinary_feasible G z).1 hz).1
  exact (approximation G hm hK hdegree z hz).trans
    (mul_le_mul_of_nonneg_right (factor_accuracy hm haccuracy) (Finset.sum_nonneg (fun v _ => hz0 v)))

end Paper.Density.RationalApproximation

#print axioms Paper.Density.RationalApproximation.dual_packing
#print axioms Paper.Density.RationalApproximation.objectives
#print axioms Paper.Density.RationalApproximation.approximation
#print axioms Paper.Density.RationalApproximation.near_optimal
