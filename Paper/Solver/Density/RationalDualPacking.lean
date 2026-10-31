import Paper.Solver.Density.RationalEpochTrace
import Paper.Solver.Density.RationalChargeSeries
import Paper.Solver.Density.RationalChargeNormalization

/-! The actual paid dual vector has bounded mass at every physical
candidate. The proof sums the executed epoch charges, without a supplied
packing or solver contract. The public degree bound is still explicit. -/
namespace Paper.Density.RationalDualPacking
open RationalRuntime RationalRequirementDecay RationalEpochDecay RationalDualLedger
open RationalPendingBound RationalCleanupCharge RationalPhaseCharge RationalEpochCharge
open RationalEpochTrace RationalChargeSeries RationalChargeNormalization SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem threshold_pred {m : ℕ} (hm : 1 ≤ m) (ep : ℤ) :
    threshold m (ep - 1) = base m * threshold m ep := by
  have h := threshold_succ hm (ep - 1)
  have he : ep - 1 + 1 = ep := by ring
  rw [he] at h
  rw [h, ← mul_assoc, base_scale hm, one_mul]

noncomputable def normalizedMass (m K j : ℕ) (v : V) : ℝ :=
  fullMass G (trace G m K j).state v / threshold m (epoch m K j)

noncomputable def epochPayment (m K : ℕ) (v : V) (j : ℕ) : ℝ :=
  paidMass G (trace G m K (j + 1)) v - paidMass G (trace G m K j) v

theorem normalized_mass_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (j : ℕ) (v : V) :
    normalizedMass G m K j v ≤ (scale m : ℝ) ^ 2 := by
  unfold normalizedMass
  apply (div_le_iff₀ (threshold_pos hm (epoch m K j))).2
  have he : (K : ℤ) - j = epoch m K j + 2 := by unfold epoch; ring
  have hb := trace_mass_bound G hm hk hdegree j v
  rw [he, threshold_two hm, Rat.cast_mul, Rat.cast_pow] at hb
  exact hb

theorem normalized_mass_nonneg {m K : ℕ} (hm : 1 ≤ m) (j : ℕ) (v : V) :
    0 ≤ normalizedMass G m K j v :=
  div_nonneg (trace_mass_nonneg G m K j v) (threshold_pos hm (epoch m K j)).le

theorem normalized_payment_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (j : ℕ) (v : V) :
    epochPayment G m K v j ≤ (coefficient m : ℝ) * denominator m K *
      (normalizedMass G m K j v - (base m : ℝ) * normalizedMass G m K (j + 1) v) := by
  have hb : epochPayment G m K v j ≤
      (coefficient m : ℝ) * denominator m K / threshold m (epoch m K j) *
        (fullMass G (trace G m K j).state v - fullMass G (trace G m K (j + 1)).state v) :=
    block_charge G hm hk (epoch m K j) (2 * m) (trace G m K j)
      (trace_consistent G m K j) (trace_pending G hm j) (trace_small G m K j) hdegree v
  have ht : (threshold m (epoch m K (j + 1)) : ℝ) =
      (base m : ℝ) * (threshold m (epoch m K j) : ℝ) := by
    have he : epoch m K (j + 1) = epoch m K j - 1 := by unfold epoch; push_cast; ring
    rw [he, threshold_pred hm, Rat.cast_mul]
  have hq : (0 : ℝ) < (base m : ℚ) := by
    have hqQ : (0 : ℚ) < base m := div_pos (by exact_mod_cast (by omega : 0 < m)) (by positivity)
    exact_mod_cast hqQ
  have hrel : (base m : ℝ) * normalizedMass G m K (j + 1) v =
      fullMass G (trace G m K (j + 1)).state v / threshold m (epoch m K j) := by
    unfold normalizedMass
    rw [ht]
    field_simp [ne_of_gt hq, ne_of_gt (threshold_pos hm (epoch m K j))]
  calc
    _ ≤ (coefficient m : ℝ) * denominator m K / threshold m (epoch m K j) *
        (fullMass G (trace G m K j).state v - fullMass G (trace G m K (j + 1)).state v) := hb
    _ = _ := by rw [hrel]; unfold normalizedMass; ring

theorem payment_sum (m K N : ℕ) (v : V) :
    (∑ j ∈ Finset.range N, epochPayment G m K v j) = paidMass G (trace G m K N) v := by
  induction N with
  | zero => simp [trace, initialLedger, paidMass, UnitDomination.mass]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold epochPayment
    ring

theorem actual_packing {m K : ℕ} (hm : 1 ≤ m) (hK : m ≤ K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    paidMass G (actualLedger G m K) v ≤
      ((denominator m K * target m K : ℕ) : ℝ) * (scale m : ℝ) ^ 5 := by
  have hk : 0 < K := by omega
  let N := K + target m K
  let C : ℝ := (coefficient m : ℝ) * denominator m K
  have hC : 0 ≤ C := mul_nonneg (by exact_mod_cast (coefficient_pos hm).le) (Nat.cast_nonneg _)
  have hq : (0 : ℝ) ≤ (base m : ℚ) := by exact_mod_cast (base_bounds m).1
  have hq1 : (base m : ℝ) ≤ 1 := by exact_mod_cast (base_bounds m).2
  have hsum := total_charge_bound (fun j => normalizedMass G m K j v) (epochPayment G m K v)
    N C (base m) ((scale m : ℝ) ^ 2) hC hq hq1
    (fun j _ => normalized_mass_bound G hm hk hdegree j v)
    (normalized_mass_nonneg G hm N v)
    (fun j _ => normalized_payment_bound G hm hk hdegree j v)
  have hn : (coefficient m : ℝ) * (scale m : ℝ) ^ 2 *
      ((base m : ℝ) + (N : ℝ) * (1 - (base m : ℝ))) ≤ (target m K : ℝ) * (scale m : ℝ) ^ 5 := by
    exact_mod_cast charge_factor hm hK
  calc
    _ = ∑ j ∈ Finset.range N, epochPayment G m K v j := by
      rw [payment_sum, trace_actual]
    _ ≤ C * (scale m : ℝ) ^ 2 * ((base m : ℝ) + (N : ℝ) * (1 - (base m : ℝ))) := hsum
    _ = (denominator m K : ℝ) * ((coefficient m : ℝ) * (scale m : ℝ) ^ 2 *
        ((base m : ℝ) + (N : ℝ) * (1 - (base m : ℝ)))) := by dsimp only [C]; ring
    _ ≤ (denominator m K : ℝ) * ((target m K : ℝ) * (scale m : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

end Paper.Density.RationalDualPacking

#print axioms Paper.Density.RationalDualPacking.normalized_mass_bound
#print axioms Paper.Density.RationalDualPacking.normalized_payment_bound
#print axioms Paper.Density.RationalDualPacking.actual_packing
