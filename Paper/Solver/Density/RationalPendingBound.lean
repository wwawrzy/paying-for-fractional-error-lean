import Paper.Solver.Density.RationalDualLedger
import Paper.Solver.Density.RationalIncrementGrowth

/-! The pending proof-side allocation is controlled by the actual coverage
counter. Each increment is charged using its real eligibility threshold. -/
namespace Paper.Density.RationalPendingBound
open BroadcastModel RationalRuntime RationalAccounting RationalSaturation
open RationalRequirementDecay RationalEpochDecay RationalDualLedger RationalIncrementGrowth SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem source_le_value {m K : ℕ} (s : V → State m K) (v : V) :
    source s v ≤ (value (s v) : ℝ) := by
  cases hs : (s v).stopped <;> cases ha : (s v).active <;>
    simp only [source, value, request, hs, ha, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_and, Bool.false_eq_true, if_false, requirement,
      if_true, Rat.cast_zero, le_refl]
  positivity

theorem threshold_pos {m : ℕ} (hm : 1 ≤ m) (ep : ℤ) :
    (0 : ℝ) < (threshold m ep : ℚ) := by
  have ht : (0 : ℚ) < threshold m ep := by
    change (0 : ℚ) < scale m ^ ep
    exact zpow_pos ((by norm_num : (0 : ℚ) < 1).trans (scale_bounds hm).1) _
  exact_mod_cast ht

theorem ratio_bound {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ)
    (s : V → State m K) (v : V) :
    increment G m K ep ed s v / gamma G s v ≤
      increment G m K ep ed s v / threshold m ep := by
  by_cases h : threshold m ep ≤ localGamma G s v
  · have hR : (threshold m ep : ℝ) ≤ gamma G s v := by
      rw [gamma_eq]
      exact_mod_cast h
    exact div_le_div_of_nonneg_left (increment_nonneg G m K ep ed s v) (threshold_pos hm ep) hR
  · have hi : increment G m K ep ed s v = 0 := by
      change ((CappedCount.cap (denominator m K)
        (if threshold m ep ≤ localGamma G s v then gridIncrement m K ed else 0)).value.val : ℝ) = 0
      simp only [if_neg h, CappedCount.cap, Nat.zero_min, Nat.cast_zero]
    simp only [hi, zero_div, le_refl]

theorem allocation_bound {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ)
    (s : V → State m K) (r : V) :
    allocation G m K ep ed s r ≤ (value (s r) : ℝ) *
      (∑ u ∈ closed G r, increment G m K ep ed s u) / threshold m ep := by
  have hsum : UnitDomination.mass G (fun v => increment G m K ep ed s v / gamma G s v) r ≤
      (∑ u ∈ closed G r, increment G m K ep ed s u) / threshold m ep := by
    unfold UnitDomination.mass
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun v _ => ratio_bound G hm ep ed s v)
  have hmass : 0 ≤ (∑ u ∈ closed G r, increment G m K ep ed s u) / (threshold m ep : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun v _ => increment_nonneg G m K ep ed s v)) (threshold_pos hm ep).le
  calc
    _ ≤ source s r * ((∑ u ∈ closed G r, increment G m K ep ed s u) / threshold m ep) :=
      mul_le_mul_of_nonneg_left hsum (source_nonneg s r)
    _ ≤ (value (s r) : ℝ) * ((∑ u ∈ closed G r, increment G m K ep ed s u) / threshold m ep) :=
      mul_le_mul_of_nonneg_right (source_le_value s r) hmass
    _ = _ := (mul_div_assoc _ _ _).symm

def PendingBound {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) : Prop :=
  ∀ v, L.pending v ≤ (value (L.state v) : ℝ) * (L.state v).weight / threshold m ep

theorem inner_pending_bound {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ)
    (L : Ledger (V := V) m K) (hL : PendingBound ep L) :
    PendingBound ep (accountInner G ep ed L) := by
  intro v
  have he : value (after G m K ep ed L.state v) = value (L.state v) := rfl
  have hw : ((after G m K ep ed L.state v).weight : ℝ) = ((L.state v).weight : ℝ) +
      ∑ u ∈ closed G v, increment G m K ep ed L.state u := by
    rw [weight_step]
    push_cast
    rfl
  change L.pending v + allocation G m K ep ed L.state v ≤
    (value (after G m K ep ed L.state v) : ℝ) *
      (after G m K ep ed L.state v).weight / threshold m ep
  rw [he, hw, mul_add, add_div]
  exact add_le_add (hL v) (allocation_bound G hm ep ed L.state v)

end Paper.Density.RationalPendingBound

#print axioms Paper.Density.RationalPendingBound.ratio_bound
#print axioms Paper.Density.RationalPendingBound.allocation_bound
#print axioms Paper.Density.RationalPendingBound.inner_pending_bound
