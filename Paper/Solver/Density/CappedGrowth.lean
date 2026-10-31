import Mathlib

/-! Scalar growth estimates for the capped dual process. The growth factor
depends only on m. The maximum degree enters only the analysis time bound,
not the update factor or its reciprocal freezing threshold. -/

namespace Paper.Density.CappedGrowth

noncomputable def factor (m : ℕ) : ℝ := ((m : ℝ) + 1) / m

noncomputable def rho (m : ℕ) : ℝ := (m : ℝ) / ((m : ℝ) + 1)

def timeBound (m Delta : ℕ) : ℕ := m * Nat.clog 2 (Delta + 1)

theorem factor_bounds {m : ℕ} (hm : 0 < m) : 1 < factor m ∧ factor m ≤ 2 := by
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  constructor
  · apply (lt_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

theorem rho_bounds {m : ℕ} (hm : 0 < m) : 0 < rho m ∧ rho m < 1 := by
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  constructor
  · exact div_pos hp hd
  · apply (div_lt_one hd).mpr
    linarith

theorem factor_mul_rho {m : ℕ} (hm : 0 < m) : factor m * rho m = 1 := by
  have hp : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hd : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold factor rho
  field_simp

/-- Bernoulli's inequality gives a factor of two after m updates. -/
theorem factor_pow_m {m : ℕ} (hm : 0 < m) : (2 : ℝ) ≤ factor m ^ m := by
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  have he : 1 + 1 / (m : ℝ) = factor m := by
    unfold factor
    field_simp
  have hh := one_add_mul_le_pow (by
    have hr : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    linarith : (-2 : ℝ) ≤ 1 / (m : ℝ)) m
  rw [he] at hh
  have hl : 1 + (m : ℝ) * (1 / (m : ℝ)) = 2 := by field_simp; norm_num
  linarith

theorem factor_pow_timeBound {m : ℕ} (hm : 0 < m) (Delta : ℕ) :
    (Delta : ℝ) + 1 ≤ factor m ^ timeBound m Delta := by
  calc
    _ ≤ (2 : ℝ) ^ Nat.clog 2 (Delta + 1) := by
      exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (Delta + 1)
    _ ≤ (factor m ^ m) ^ Nat.clog 2 (Delta + 1) :=
      pow_le_pow_left₀ (by norm_num) (factor_pow_m hm) _
    _ = _ := by rw [← pow_mul]; rfl

/-- An initial value at least the locally established lower bound reaches
the cap by the analysis time, unless it has already frozen for another row. -/
theorem cap_le_grown {m : ℕ} (hm : 0 < m) (Delta : ℕ) {cap x : ℝ}
    (hcap : 0 < cap) (hcap_one : cap ≤ 1)
    (hx : min cap (1 / ((Delta : ℝ) + 1)) ≤ x) :
    cap ≤ factor m ^ timeBound m Delta * x := by
  have hd : (0 : ℝ) < (Delta : ℝ) + 1 := by positivity
  have hpow := factor_pow_timeBound hm Delta
  have hone : 1 ≤ factor m ^ timeBound m Delta := by
    have hDelta : (0 : ℝ) ≤ Delta := Nat.cast_nonneg Delta
    exact (by linarith : (1 : ℝ) ≤ (Delta : ℝ) + 1).trans hpow
  have hnonneg : 0 ≤ factor m ^ timeBound m Delta := le_trans zero_le_one hone
  rcases le_total cap (1 / ((Delta : ℝ) + 1)) with hc | hc
  · rw [min_eq_left hc] at hx
    calc
      cap ≤ factor m ^ timeBound m Delta * cap := by
        simpa using mul_le_mul_of_nonneg_right hone hcap.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hnonneg
  · rw [min_eq_right hc] at hx
    have hr := mul_le_mul_of_nonneg_right hpow (one_div_pos.mpr hd).le
    have he : ((Delta : ℝ) + 1) * (1 / ((Delta : ℝ) + 1)) = 1 := by
      rw [one_div, mul_inv_cancel₀ hd.ne']
    rw [he] at hr
    exact hcap_one.trans (hr.trans (mul_le_mul_of_nonneg_left hx hnonneg))

end Paper.Density.CappedGrowth

#print axioms Paper.Density.CappedGrowth.factor_mul_rho
#print axioms Paper.Density.CappedGrowth.factor_pow_m
#print axioms Paper.Density.CappedGrowth.factor_pow_timeBound
#print axioms Paper.Density.CappedGrowth.cap_le_grown
