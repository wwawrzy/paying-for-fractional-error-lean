import Paper.Solver.Density.RationalTermination

/-! Proof-only dual bookkeeping for the actual execution. The real ledger
is not sent or used by any protocol decision. Its state projection is the
literal runtime, and every primal increment is conserved as pending or paid
dual allocation. -/
namespace Paper.Density.RationalDualLedger
open BroadcastModel RationalRuntime RationalAccounting RationalSaturation
open RationalRequirementDecay RationalEpochDecay RationalTermination
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Ledger (m K : ℕ) where
  state : V → State m K
  pending : V → ℝ
  paid : V → ℝ

noncomputable def payout {m K : ℕ} (ep : ℤ) (s : State m K) (p : ℝ) : ℝ :=
  if denominator m K ≤ s.weight then
    if target m K * denominator m K ≤ s.fulfilled ∨ 2 * denominator m K ≤ s.weight then p
    else min p ((value s : ℝ) * scale m * denominator m K / threshold m ep)
  else 0

noncomputable def accountInner {m K : ℕ} (ep : ℤ) (ed : ℕ) (L : Ledger (V := V) m K) :
    Ledger (V := V) m K where
  state := after G m K ep ed L.state
  pending v := L.pending v + allocation G m K ep ed L.state v
  paid := L.paid

noncomputable def accountClean {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) :
    Ledger (V := V) m K where
  state v := clean (L.state v)
  pending v := L.pending v - payout ep (L.state v) (L.pending v)
  paid v := L.paid v + payout ep (L.state v) (L.pending v)

def Conserved {m K : ℕ} (L : Ledger (V := V) m K) : Prop :=
  (∑ v, (L.pending v + L.paid v)) = ∑ v, ((L.state v).primal : ℝ)

theorem payout_bounds {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (s : State m K)
    (p : ℝ) (hp : 0 ≤ p) : 0 ≤ payout ep s p ∧ payout ep s p ≤ p := by
  have hscale : (0 : ℝ) ≤ (scale m : ℚ) := by
    exact_mod_cast (le_of_lt ((by norm_num : (0 : ℚ) < 1).trans (scale_bounds hm).1))
  have hv : (0 : ℝ) ≤ (value s : ℚ) := by exact_mod_cast value_nonneg s
  have ht : (0 : ℚ) < threshold m ep := by
    change (0 : ℚ) < scale m ^ ep
    exact zpow_pos ((by norm_num : (0 : ℚ) < 1).trans (scale_bounds hm).1) _
  have htR : (0 : ℝ) < (threshold m ep : ℚ) := by exact_mod_cast ht
  unfold payout
  split_ifs
  · exact ⟨hp, le_rfl⟩
  · exact ⟨le_min hp (div_nonneg (mul_nonneg (mul_nonneg hv hscale) (Nat.cast_nonneg _)) htR.le), min_le_left _ _⟩
  · exact ⟨le_rfl, hp⟩

theorem inner_conserved {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ)
    (L : Ledger (V := V) m K) (hL : Conserved L) : Conserved (accountInner G ep ed L) := by
  have hp (v : V) : ((after G m K ep ed L.state v).primal : ℝ) =
      ((L.state v).primal : ℝ) + increment G m K ep ed L.state v := by
    change (((L.state v).primal +
      (eval G (primalRound m K ep ed) L.state v).increment.value.val : ℕ) : ℝ) = _
    rw [Nat.cast_add]
    rfl
  unfold Conserved accountInner
  simp only [hp, Finset.sum_add_distrib]
  have hsum := total_allocation G hm ep ed L.state
  unfold Conserved at hL
  simp only [Finset.sum_add_distrib] at hL
  linarith

theorem clean_conserved {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K)
    (hL : Conserved L) : Conserved (accountClean ep L) := by
  have hp (v : V) : (clean (L.state v)).primal = (L.state v).primal := by
    unfold clean
    split_ifs <;> rfl
  unfold Conserved accountClean
  simp only [hp]
  unfold Conserved at hL
  convert hL using 1
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem inner_nonnegative {m K : ℕ} (ep : ℤ) (ed : ℕ) (L : Ledger (V := V) m K)
    (hp : ∀ v, 0 ≤ L.pending v) (hy : ∀ v, 0 ≤ L.paid v) :
    (∀ v, 0 ≤ (accountInner G ep ed L).pending v) ∧
      ∀ v, 0 ≤ (accountInner G ep ed L).paid v :=
  ⟨fun v => add_nonneg (hp v) (allocation_nonneg G m K ep ed L.state v), hy⟩

omit [Fintype V] [DecidableEq V] in
theorem clean_nonnegative {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (L : Ledger (V := V) m K)
    (hp : ∀ v, 0 ≤ L.pending v) (hy : ∀ v, 0 ≤ L.paid v) :
    (∀ v, 0 ≤ (accountClean ep L).pending v) ∧
      ∀ v, 0 ≤ (accountClean ep L).paid v := by
  exact ⟨fun v => sub_nonneg.mpr (payout_bounds hm ep (L.state v) _ (hp v)).2,
    fun v => add_nonneg (hy v) (payout_bounds hm ep (L.state v) _ (hp v)).1⟩

noncomputable def accountScan {m K : ℕ} (ep : ℤ) : ℕ → Ledger (V := V) m K → Ledger (V := V) m K
  | 0, L => L
  | j + 1, L => accountScan ep j (accountInner G ep j L)

noncomputable def accountPhase {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) :
    Ledger (V := V) m K :=
  accountClean ep (accountScan G ep K { L with state := fun v => { L.state v with active := !(L.state v).stopped } })

noncomputable def accountBlock {m K : ℕ} (ep : ℤ) : ℕ → Ledger (V := V) m K → Ledger (V := V) m K
  | 0, L => L
  | j + 1, L => accountPhase G ep (accountBlock ep j L)

noncomputable def accountOuter {m K : ℕ} : ℕ → Ledger (V := V) m K → Ledger (V := V) m K
  | 0, L => L
  | j + 1, L => accountOuter j (accountBlock G ((j : ℤ) - target m K - 1) (2 * m) L)

def initialLedger (m K : ℕ) : Ledger (V := V) m K :=
  ⟨fun _ => initial m K, fun _ => 0, fun _ => 0⟩

theorem scan_state {m K : ℕ} (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K) :
    (accountScan G ep j L).state = (scan m K ep j).run G L.state := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    change (accountScan G ep j (accountInner G ep j L)).state = _
    rw [ih]
    rfl

theorem phase_state {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) :
    (accountPhase G ep L).state = (phase m K ep).run G L.state := by
  unfold accountPhase accountClean
  simp only [scan_state]
  rfl

theorem block_state {m K : ℕ} (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K) :
    (accountBlock G ep j L).state = ((phase m K ep).iterate j).run G L.state := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (accountPhase G ep (accountBlock G ep j L)).state = _
    rw [phase_state, ih]
    rfl

theorem outer_state {m K : ℕ} (j : ℕ) (L : Ledger (V := V) m K) :
    (accountOuter G j L).state = (outer m K j).run G L.state := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    change (accountOuter G j (accountBlock G ((j : ℤ) - target m K - 1) (2 * m) L)).state = _
    rw [ih, block_state]
    rfl

theorem scan_conserved {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (j : ℕ)
    (L : Ledger (V := V) m K) (hL : Conserved L) : Conserved (accountScan G ep j L) := by
  induction j generalizing L with
  | zero => exact hL
  | succ j ih => exact ih _ (inner_conserved G hm ep j L hL)

theorem phase_conserved {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ)
    (L : Ledger (V := V) m K) (hL : Conserved L) : Conserved (accountPhase G ep L) :=
  clean_conserved ep _ (scan_conserved G hm ep K _ hL)

theorem block_conserved {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (j : ℕ)
    (L : Ledger (V := V) m K) (hL : Conserved L) : Conserved (accountBlock G ep j L) := by
  induction j with
  | zero => exact hL
  | succ j ih => exact phase_conserved G hm ep _ ih

theorem outer_conserved {m K : ℕ} (hm : 1 ≤ m) (j : ℕ)
    (L : Ledger (V := V) m K) (hL : Conserved L) : Conserved (accountOuter G j L) := by
  induction j generalizing L with
  | zero => exact hL
  | succ j ih => exact ih _ (block_conserved G hm _ (2 * m) L hL)

noncomputable def actualLedger (m K : ℕ) : Ledger (V := V) m K :=
  accountOuter G (K + target m K) (initialLedger m K)

theorem actual_state (m K : ℕ) :
    (actualLedger G m K).state = finalState G m K :=
  outer_state G (K + target m K) (initialLedger m K)

theorem actual_conserved {m K : ℕ} (hm : 1 ≤ m) :
    (∑ v, ((actualLedger G m K).pending v + (actualLedger G m K).paid v)) =
      ∑ v, ((finalState G m K v).primal : ℝ) := by
  have hi : Conserved (initialLedger (V := V) m K) := by
    simp [Conserved, initialLedger, initial]
  have h := outer_conserved G hm (K + target m K) (initialLedger m K) hi
  change Conserved (actualLedger G m K) at h
  unfold Conserved at h
  rw [actual_state] at h
  exact h

end Paper.Density.RationalDualLedger

#print axioms Paper.Density.RationalDualLedger.payout_bounds
#print axioms Paper.Density.RationalDualLedger.inner_conserved
#print axioms Paper.Density.RationalDualLedger.clean_conserved
#print axioms Paper.Density.RationalDualLedger.clean_nonnegative
#print axioms Paper.Density.RationalDualLedger.actual_state
#print axioms Paper.Density.RationalDualLedger.actual_conserved
