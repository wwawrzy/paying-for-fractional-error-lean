import Paper.Solver.Density.RationalPendingBudget

/-! Every actual cleanup payment is bounded by the corresponding decrease
of the full requirement. No primal/dual charge inequality is assumed. -/
namespace Paper.Density.RationalCleanupCharge
open RationalRuntime RationalCounters RationalRequirementDecay RationalEpochDecay
open RationalDualLedger RationalPendingBound RationalPendingCleanup RationalPendingBudget

def coefficient (m : ℕ) : ℚ := scale m ^ 2 / (scale m - 1)

theorem coefficient_pos {m : ℕ} (hm : 1 ≤ m) : 0 < coefficient m := by
  unfold coefficient
  exact div_pos (pow_pos ((by norm_num : (0 : ℚ) < 1).trans (scale_bounds hm).1) _)
    (sub_pos.mpr (scale_bounds hm).1)

theorem coefficient_once {m : ℕ} (hm : 1 ≤ m) :
    coefficient m * (1 - base m) = scale m := by
  have hp : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold coefficient scale base
  push_cast
  field_simp

theorem coefficient_twice {m : ℕ} (hm : 1 ≤ m) :
    coefficient m * (1 - base m ^ 2) = 1 + scale m := by
  have hp : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold coefficient scale base
  push_cast
  field_simp
  <;> ring

theorem clean_drop_two {m K : ℕ} (s : State m K) (hs : Consistent s)
    (hw : 2 * denominator m K ≤ s.weight) : value (clean s) ≤ base m ^ 2 * value s := by
  have hD : 0 < denominator m K := by unfold denominator; positivity
  have hw1 : denominator m K ≤ s.weight := by omega
  by_cases hf : target m K * denominator m K ≤ s.fulfilled
  · simp only [clean, if_pos hw1, if_pos hf, value, requirement]
    exact mul_nonneg (pow_nonneg (base_bounds m).1 _) (value_nonneg s)
  · have hfalse : s.stopped = false := by
      cases hh : s.stopped with
      | false => rfl
      | true => exact False.elim (hf (hs.1 hh))
    have hcap := exponent_uncapped s (hs.2 hfalse) (Nat.lt_of_not_ge hf)
    have hdiv : 2 ≤ s.weight / denominator m K :=
      (Nat.le_div_iff_mul_le hD).2 (by simpa only [Nat.mul_comm] using hw)
    simp only [clean, if_pos hw1, if_neg hf, value, requirement, hfalse,
      Bool.not_false, if_true, CappedCount.cap, min_eq_left hcap]
    change base m ^ (s.exponent.value.val + s.weight / denominator m K) ≤
      base m ^ 2 * base m ^ s.exponent.value.val
    rw [pow_add, mul_comm (base m ^ 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (base_bounds m).1 (base_bounds m).2 hdiv)
      (pow_nonneg (base_bounds m).1 _)

theorem cleanup_charge {V : Type} [Fintype V] [DecidableEq V]
    {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (L : Ledger (V := V) m K)
    (hc : ∀ v, Consistent (L.state v)) (hB : Budget ep L) (v : V) :
    payout ep (L.state v) (L.pending v) ≤
      (coefficient m : ℝ) * denominator m K / threshold m ep *
        ((value (L.state v) : ℝ) - (value (clean (L.state v)) : ℝ)) := by
  let s := L.state v
  change payout ep s (L.pending v) ≤
    (coefficient m : ℝ) * denominator m K / threshold m ep *
      ((value s : ℝ) - (value (clean s) : ℝ))
  have hθ := threshold_pos hm ep
  have hC : (0 : ℝ) < (coefficient m : ℚ) := by exact_mod_cast coefficient_pos hm
  have hr : (0 : ℝ) ≤ (value s : ℚ) := by exact_mod_cast value_nonneg s
  have hD : (0 : ℝ) ≤ (denominator m K : ℕ) := Nat.cast_nonneg _
  have hone : (coefficient m : ℝ) * (1 - (base m : ℝ)) = (scale m : ℝ) := by
    exact_mod_cast coefficient_once hm
  have htwo : (coefficient m : ℝ) * (1 - (base m : ℝ) ^ 2) = 1 + (scale m : ℝ) := by
    exact_mod_cast coefficient_twice hm
  have hCle : 1 + (scale m : ℝ) ≤ (coefficient m : ℝ) := by
    nlinarith [mul_nonneg hC.le (sq_nonneg (base m : ℝ))]
  by_cases hw : denominator m K ≤ s.weight
  · by_cases hf : target m K * denominator m K ≤ s.fulfilled
    · have hz : value (clean s) = 0 := by simp [clean, hw, hf, value, requirement]
      have hb := hB v
      have hfactor := mul_le_mul_of_nonneg_left hCle hr
      have hbound := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfactor hD) hθ.le
      simp only [payout, if_pos hw, if_pos (Or.inl hf), hz, Rat.cast_zero, sub_zero]
      exact hb.trans (hbound.trans_eq (by ring))
    · by_cases hw2 : 2 * denominator m K ≤ s.weight
      · have hdrop : (value (clean s) : ℝ) ≤ (base m : ℝ) ^ 2 * (value s : ℝ) := by
          exact_mod_cast clean_drop_two s (hc v) hw2
        have htwoR := congrArg (fun x : ℝ => (value s : ℝ) * x) htwo
        have hfactor : (value s : ℝ) * (1 + (scale m : ℝ)) ≤
            (coefficient m : ℝ) * ((value s : ℝ) - (value (clean s) : ℝ)) := by
          nlinarith only [mul_le_mul_of_nonneg_left hdrop hC.le, htwoR]
        have hbound := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfactor hD) hθ.le
        simp only [payout, if_pos hw, if_pos (Or.inr hw2)]
        exact (hB v).trans (hbound.trans_eq (by ring))
      · have he : (value (clean s) : ℝ) = (base m : ℝ) * (value s : ℝ) := by
          exact_mod_cast clean_value_once s (hc v) hw (Nat.lt_of_not_ge hw2) (Nat.lt_of_not_ge hf)
        have heq : (value s : ℝ) * (scale m : ℝ) =
            (coefficient m : ℝ) * ((value s : ℝ) - (value (clean s) : ℝ)) := by
          rw [he]
          calc
            _ = (value s : ℝ) * ((coefficient m : ℝ) * (1 - (base m : ℝ))) := by rw [hone]
            _ = _ := by ring
        simp only [payout, if_pos hw, if_neg (not_or.mpr ⟨hf, hw2⟩)]
        have hcap := min_le_right (L.pending v) ((value s : ℝ) * scale m * denominator m K / threshold m ep)
        rw [heq] at hcap
        rw [heq]
        exact hcap.trans_eq (by ring)
  · simp only [payout, if_neg hw, clean, if_neg hw, sub_self, mul_zero, le_refl]

end Paper.Density.RationalCleanupCharge

#print axioms Paper.Density.RationalCleanupCharge.coefficient_once
#print axioms Paper.Density.RationalCleanupCharge.coefficient_twice
#print axioms Paper.Density.RationalCleanupCharge.clean_drop_two
#print axioms Paper.Density.RationalCleanupCharge.cleanup_charge
