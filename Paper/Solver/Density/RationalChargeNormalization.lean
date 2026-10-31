import Paper.Solver.Density.RationalCleanupCharge

/-! The finite geometric charge bound has the same fifth-power accuracy
budget as the public rational parameter choice. -/
namespace Paper.Density.RationalChargeNormalization
open RationalRuntime RationalRequirementDecay RationalEpochDecay RationalCleanupCharge

theorem expression_eq {m : ℕ} (hm : 1 ≤ m) (K : ℕ) :
    (coefficient m * scale m ^ 2 *
      (base m + (K + target m K : ℕ) * (1 - base m))) / target m K =
    scale m ^ 4 * ((m + (K + target m K) : ℕ) /
      (((m + 1) * (K + 1) : ℕ) : ℚ)) := by
  have hp : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold coefficient scale base target
  push_cast
  field_simp
  <;> ring

theorem ratio_le_scale {m K : ℕ} (hm : 1 ≤ m) (hK : m ≤ K) :
    ((m + (K + target m K) : ℕ) : ℚ) / (((m + 1) * (K + 1) : ℕ) : ℚ) ≤ scale m := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hk : (m : ℚ) ≤ K := by exact_mod_cast hK
  unfold scale target
  push_cast
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < (m + 1) * (K + 1)) hp).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) (by positivity : (0 : ℚ) ≤ m + 1)]

theorem charge_factor {m K : ℕ} (hm : 1 ≤ m) (hK : m ≤ K) :
    coefficient m * scale m ^ 2 * (base m + (K + target m K : ℕ) * (1 - base m)) ≤
      (target m K : ℚ) * scale m ^ 5 := by
  have hF : (0 : ℚ) < target m K := by
    unfold target
    exact_mod_cast Nat.mul_pos (by omega : 0 < m) (by omega : 0 < K + 1)
  rw [mul_comm (target m K : ℚ)]
  apply (div_le_iff₀ hF).mp
  rw [expression_eq hm]
  have h := mul_le_mul_of_nonneg_left (ratio_le_scale hm hK) (pow_nonneg (le_of_lt
    ((by norm_num : (0 : ℚ) < 1).trans (scale_bounds hm).1)) 4)
  simpa only [← pow_succ] using h

end Paper.Density.RationalChargeNormalization

#print axioms Paper.Density.RationalChargeNormalization.expression_eq
#print axioms Paper.Density.RationalChargeNormalization.ratio_le_scale
#print axioms Paper.Density.RationalChargeNormalization.charge_factor
