import Paper.Solver.Density.RationalPendingExecution

/-! A uniform pending-allocation budget before actual cleanup. Once a row
becomes inactive, further physical coverage does not add dual allocation. -/
namespace Paper.Density.RationalPendingBudget
open BroadcastModel RationalRuntime RationalAccounting RationalSaturation
open RationalRequirementDecay RationalEpochDecay RationalIncrementGrowth
open RationalDualLedger RationalPendingBound RationalPendingExecution SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Budget {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) : Prop :=
  ∀ v, L.pending v ≤ (value (L.state v) : ℝ) * (1 + scale m) * denominator m K / threshold m ep

def ActiveSmall {m K : ℕ} (s : V → State m K) : Prop :=
  ∀ v, (s v).active = true → (s v).weight < denominator m K

def SmallStep {m K : ℕ} (ep : ℤ) (ed : ℕ) (s : V → State m K) : Prop :=
  ∀ v, (s v).active = true →
    (∑ u ∈ closed G v, increment G m K ep ed s u) ≤ (scale m : ℝ) * denominator m K

theorem scaled_nat_bound {m : ℕ} (hm : 1 ≤ m) (n D : ℕ)
    (h : m * n ≤ (m + 1) * D) : (n : ℝ) ≤ (scale m : ℝ) * D := by
  have hp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr : (m : ℝ) * n ≤ ((m + 1 : ℕ) : ℝ) * D := by exact_mod_cast h
  have he : (scale m : ℝ) * D = ((m + 1 : ℕ) : ℝ) * D / m := by
    simp only [scale, Rat.cast_div, Rat.cast_natCast]
    ring
  rw [he]
  apply (le_div_iff₀ hp).2
  nlinarith only [hr]

theorem row_increment_cast (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    ((∑ u ∈ closed G v, step G m K ep ed s u : ℕ) : ℝ) =
      ∑ u ∈ closed G v, increment G m K ep ed s u := by
  push_cast
  rfl

theorem first_step_small {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (ep : ℤ)
    (s : V → State m K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) :
    SmallStep G ep (K - 1) s := by
  intro v _
  have h := scaled_nat_bound hm _ _ (first_increment_bound G hm hk ep s v (hdegree v))
  simpa only [row_increment_cast] using h

theorem next_step_small {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ) (hed : ed + 1 ≤ K)
    (s : V → State m K) : SmallStep G ep ed (after G m K ep (ed + 1) s) := by
  intro v ha
  have h := scaled_nat_bound hm _ _ (active_next_increment G m K ep ed hed s v ha).le
  simpa only [row_increment_cast] using h

theorem after_active_small (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) :
    ActiveSmall (after G m K ep ed s) := by
  intro v ha
  rw [after_active] at ha
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp ha).2

theorem budget_of_pending {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (L : Ledger (V := V) m K)
    (hL : PendingBound ep L) (hw : ∀ v, (L.state v).weight < denominator m K) : Budget ep L := by
  have hs : (0 : ℝ) ≤ (scale m : ℚ) := by
    exact_mod_cast le_trans (by norm_num : (0 : ℚ) ≤ 1) (scale_bounds hm).1.le
  intro v
  have hr : (0 : ℝ) ≤ (value (L.state v) : ℚ) := by exact_mod_cast value_nonneg (L.state v)
  have hwR : ((L.state v).weight : ℝ) ≤ denominator m K := by exact_mod_cast (hw v).le
  have hscale : (denominator m K : ℝ) ≤ (1 + (scale m : ℝ)) * denominator m K := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (denominator m K)]
  exact (hL v).trans (div_le_div_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_left (hwR.trans hscale) hr]) (threshold_pos hm ep).le)

theorem inner_budget {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ)
    (L : Ledger (V := V) m K) (hP : PendingBound ep L) (hB : Budget ep L)
    (hA : ActiveSmall L.state) (hS : SmallStep G ep ed L.state) : Budget ep (accountInner G ep ed L) := by
  intro v
  by_cases ha : (L.state v).active = true
  · have hw : ((after G m K ep ed L.state v).weight : ℝ) ≤
        (1 + (scale m : ℝ)) * denominator m K := by
      rw [weight_step, Nat.cast_add, row_increment_cast]
      have hweight : ((L.state v).weight : ℝ) ≤ denominator m K := by exact_mod_cast (hA v ha).le
      nlinarith only [hweight, hS v ha]
    have hr : (0 : ℝ) ≤ (value (L.state v) : ℚ) := by exact_mod_cast value_nonneg (L.state v)
    have hnew := inner_pending_bound G hm ep ed L hP v
    change (accountInner G ep ed L).pending v ≤
      (value (L.state v) : ℝ) * (after G m K ep ed L.state v).weight / threshold m ep at hnew
    change (accountInner G ep ed L).pending v ≤
      (value (L.state v) : ℝ) * (1 + scale m) * denominator m K / threshold m ep
    exact hnew.trans (div_le_div_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_left hw hr]) (threshold_pos hm ep).le)
  · have haf : (L.state v).active = false := by
      cases hh : (L.state v).active with
      | false => rfl
      | true => exact False.elim (ha hh)
    have hz : source L.state v = 0 := by
      simp only [source, request, haf, Bool.false_and, requirement, Bool.false_eq_true, if_false, Rat.cast_zero]
    have halloc : allocation G m K ep ed L.state v = 0 := by simp only [allocation, hz, zero_mul]
    change L.pending v + allocation G m K ep ed L.state v ≤
      (value (L.state v) : ℝ) * (1 + scale m) * denominator m K / threshold m ep
    rw [halloc, add_zero]
    exact hB v

theorem scan_budget {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) :
    ∀ j, j < K → ∀ L : Ledger (V := V) m K,
      PendingBound ep L → Budget ep L → ActiveSmall L.state → SmallStep G ep j L.state →
        Budget ep (accountScan G ep (j + 1) L) := by
  intro j
  induction j with
  | zero =>
    intro _ L hP hB hA hS
    exact inner_budget G hm ep 0 L hP hB hA hS
  | succ j ih =>
    intro hj L hP hB hA hS
    exact ih (by omega) (accountInner G ep (j + 1) L)
      (inner_pending_bound G hm ep (j + 1) L hP)
      (inner_budget G hm ep (j + 1) L hP hB hA hS)
      (after_active_small G m K ep (j + 1) L.state)
      (next_step_small G hm ep j (by omega) L.state)

theorem phase_scan_budget {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (ep : ℤ)
    (L : Ledger (V := V) m K) (hP : PendingBound ep L)
    (hw : ∀ v, (L.state v).weight < denominator m K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) :
    let R : Ledger (V := V) m K :=
      { L with state := fun v => { L.state v with active := !(L.state v).stopped } }
    Budget ep (accountScan G ep K R) := by
  dsimp only
  let R : Ledger (V := V) m K :=
    { L with state := fun v => { L.state v with active := !(L.state v).stopped } }
  have hp : PendingBound ep R := hP
  have hwr : ∀ v, (R.state v).weight < denominator m K := hw
  have hcount : K - 1 + 1 = K := by omega
  have h := scan_budget G hm ep (K - 1) (by omega) R hp
    (budget_of_pending hm ep R hp hwr) (fun v _ => hwr v)
    (first_step_small G hm hk ep R.state hdegree)
  simpa only [hcount] using h

end Paper.Density.RationalPendingBudget

#print axioms Paper.Density.RationalPendingBudget.next_step_small
#print axioms Paper.Density.RationalPendingBudget.inner_budget
#print axioms Paper.Density.RationalPendingBudget.phase_scan_budget
