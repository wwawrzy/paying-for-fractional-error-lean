import Paper.Solver.Density.RationalPendingBound

/-! Cleanup preserves the pending-allocation invariant. The single-unit
case uses the exact uncapped exponent and the rational scale identity. -/
namespace Paper.Density.RationalPendingCleanup
open RationalRuntime RationalCounters RationalRequirementDecay RationalEpochDecay
open RationalDualLedger RationalPendingBound

theorem partial_cleanup_bound (q s r w D p θ : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hs : 1 ≤ s) (hqs : q * s = 1)
    (hr : 0 ≤ r) (hD : 0 < D) (hw : D ≤ w) (hw2 : w ≤ 2 * D)
    (hθ : 0 < θ) (hp : p ≤ r * w / θ) :
    p - min p (r * s * D / θ) ≤ q * r * (w - D) / θ := by
  have htarget : 0 ≤ q * r * (w - D) / θ :=
    div_nonneg (mul_nonneg (mul_nonneg hq hr) (sub_nonneg.mpr hw)) hθ.le
  by_cases hc : p ≤ r * s * D / θ
  · rw [min_eq_left hc, sub_self]
    exact htarget
  · rw [min_eq_right (le_of_not_ge hc)]
    have hsum : 2 ≤ q + s := by
      have hh := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hq1)
      nlinarith
    have hwq := mul_le_mul_of_nonneg_left hw2 (sub_nonneg.mpr hq1)
    have hscale := mul_le_mul_of_nonneg_right hsum hD.le
    have hdiff : w - s * D ≤ q * (w - D) := by nlinarith
    have hrw := mul_le_mul_of_nonneg_left hdiff hr
    have hdiv := div_le_div_of_nonneg_right hrw hθ.le
    have he : r * (q * (w - D)) = q * r * (w - D) := by ring
    rw [he] at hdiv
    calc
      _ ≤ r * w / θ - r * s * D / θ := sub_le_sub_right hp _
      _ = r * (w - s * D) / θ := by ring
      _ ≤ _ := hdiv

theorem single_unit_div {D w : ℕ} (hD : 0 < D) (hw : D ≤ w) (hw2 : w < 2 * D) :
    w / D = 1 := by
  have hlow : 1 ≤ w / D := (Nat.le_div_iff_mul_le hD).2 (by simpa using hw)
  have hupp : w / D < 2 := (Nat.div_lt_iff_lt_mul hD).2 (by simpa [Nat.mul_comm] using hw2)
  omega

theorem clean_value_once {m K : ℕ} (s : State m K) (hs : Consistent s)
    (hw : denominator m K ≤ s.weight) (hw2 : s.weight < 2 * denominator m K)
    (hf : s.fulfilled < target m K * denominator m K) :
    value (clean s) = base m * value s := by
  have hD : 0 < denominator m K := by unfold denominator; positivity
  have hfalse : s.stopped = false := by
    cases hh : s.stopped with
    | false => rfl
    | true => exact False.elim (not_le_of_gt hf (hs.1 hh))
  have hcap := exponent_uncapped s (hs.2 hfalse) hf
  have hdiv := single_unit_div hD hw hw2
  simp only [clean, if_pos hw, if_neg (not_le_of_gt hf), value, requirement,
    hfalse, Bool.not_false, if_true, CappedCount.cap, min_eq_left hcap]
  change base m ^ (s.exponent.value.val + s.weight / denominator m K) =
    base m * base m ^ s.exponent.value.val
  rw [hdiv, pow_succ, mul_comm]

theorem clean_pending_bound {V : Type} [Fintype V] [DecidableEq V]
    {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (L : Ledger (V := V) m K)
    (hc : ∀ v, Consistent (L.state v)) (hL : PendingBound ep L) :
    PendingBound ep (accountClean ep L) := by
  intro v
  let s := L.state v
  change L.pending v - payout ep s (L.pending v) ≤
    (value (clean s) : ℝ) * (clean s).weight / threshold m ep
  have hv : (0 : ℝ) ≤ (value (clean s) : ℚ) := by exact_mod_cast value_nonneg (clean s)
  have hrhs : (0 : ℝ) ≤ (value (clean s) : ℝ) * (clean s).weight / threshold m ep :=
    div_nonneg (mul_nonneg hv (Nat.cast_nonneg _)) (threshold_pos hm ep).le
  by_cases hw : denominator m K ≤ s.weight
  · by_cases hf : target m K * denominator m K ≤ s.fulfilled
    · simpa only [payout, if_pos hw, if_pos (Or.inl hf), sub_self] using hrhs
    · by_cases hw2 : 2 * denominator m K ≤ s.weight
      · simpa only [payout, if_pos hw, if_pos (Or.inr hw2), sub_self] using hrhs
      · have hD : 0 < denominator m K := by unfold denominator; positivity
        have hdiv := single_unit_div hD hw (Nat.lt_of_not_ge hw2)
        have hmod := Nat.mod_add_div s.weight (denominator m K)
        rw [hdiv, Nat.mul_one] at hmod
        have hwclean : (clean s).weight = s.weight % denominator m K := by
          simp only [clean, if_pos hw, if_neg hf]
        have hwcast : ((clean s).weight : ℝ) = (s.weight : ℝ) - denominator m K := by
          rw [hwclean]
          have hh : ((s.weight % denominator m K : ℕ) : ℝ) + denominator m K = s.weight := by
            exact_mod_cast hmod
          linarith
        have hvalue : (value (clean s) : ℝ) = (base m : ℝ) * (value s : ℝ) := by
          exact_mod_cast clean_value_once s (hc v) hw (Nat.lt_of_not_ge hw2) (Nat.lt_of_not_ge hf)
        have hq : (0 : ℝ) ≤ (base m : ℚ) := by exact_mod_cast (base_bounds m).1
        have hq1 : (base m : ℝ) ≤ 1 := by exact_mod_cast (base_bounds m).2
        have hs : (1 : ℝ) ≤ (scale m : ℚ) := by exact_mod_cast (scale_bounds hm).1.le
        have hqs : (base m : ℝ) * (scale m : ℝ) = 1 := by exact_mod_cast base_scale hm
        have hr : (0 : ℝ) ≤ (value s : ℚ) := by exact_mod_cast value_nonneg s
        have hdR : (0 : ℝ) < (denominator m K : ℕ) := by exact_mod_cast hD
        have hwR : (denominator m K : ℝ) ≤ (s.weight : ℕ) := by exact_mod_cast hw
        have hw2R : (s.weight : ℝ) ≤ 2 * denominator m K := by exact_mod_cast (Nat.lt_of_not_ge hw2).le
        have hp := partial_cleanup_bound (base m) (scale m) (value s) s.weight
          (denominator m K) (L.pending v) (threshold m ep) hq hq1 hs hqs hr hdR hwR hw2R
          (threshold_pos hm ep) (hL v)
        simpa only [payout, if_pos hw, if_neg (not_or.mpr ⟨hf, hw2⟩), hvalue, hwcast, mul_assoc] using hp
  · simpa only [payout, if_neg hw, sub_zero, clean, if_neg hw] using hL v

end Paper.Density.RationalPendingCleanup

#print axioms Paper.Density.RationalPendingCleanup.partial_cleanup_bound
#print axioms Paper.Density.RationalPendingCleanup.clean_value_once
#print axioms Paper.Density.RationalPendingCleanup.clean_pending_bound
