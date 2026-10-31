import Paper.Solver.Density.RationalDualLedger

/-! Every stopped row has no pending dual allocation. Actual termination
therefore converts conservation of pending plus paid allocation into exact
equality of the final primal and paid dual objectives. -/
namespace Paper.Density.RationalDualFlush
open BroadcastModel RationalRuntime RationalAccounting RationalSaturation
open RationalRequirementDecay RationalEpochDecay RationalTermination RationalDualLedger SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def StoppedEmpty {m K : ℕ} (L : Ledger (V := V) m K) : Prop :=
  ∀ v, (L.state v).stopped = true → L.pending v = 0

theorem inner_stopped_empty {m K : ℕ} (ep : ℤ) (ed : ℕ) (L : Ledger (V := V) m K)
    (hL : StoppedEmpty L) : StoppedEmpty (accountInner G ep ed L) := by
  intro v hstop
  have hs : (L.state v).stopped = true := hstop
  have hz : source L.state v = 0 := by
    simp only [source, request, hs, Bool.not_true, Bool.and_false, requirement,
      Bool.false_eq_true, if_false, Rat.cast_zero]
  have ha : allocation G m K ep ed L.state v = 0 := by
    simp only [allocation, hz, zero_mul]
  change L.pending v + allocation G m K ep ed L.state v = 0
  rw [hL v hs, ha, zero_add]

theorem clean_stopped_empty {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (L : Ledger (V := V) m K)
    (hL : StoppedEmpty L) : StoppedEmpty (accountClean ep L) := by
  intro v hstop
  have hs : (clean (L.state v)).stopped = true := hstop
  change L.pending v - payout ep (L.state v) (L.pending v) = 0
  by_cases hold : (L.state v).stopped = true
  · have hz := hL v hold
    have hp : payout ep (L.state v) 0 = 0 :=
      le_antisymm (payout_bounds hm ep (L.state v) 0 le_rfl).2
        (payout_bounds hm ep (L.state v) 0 le_rfl).1
    rw [hz, hp, sub_self]
  · by_cases hw : denominator m K ≤ (L.state v).weight
    · by_cases hf : target m K * denominator m K ≤ (L.state v).fulfilled
      · simp only [payout, if_pos hw, if_pos (Or.inl hf), sub_self]
      · simp only [clean, if_pos hw, if_neg hf] at hs
        exact False.elim (hold hs)
    · simp only [clean, if_neg hw] at hs
      exact False.elim (hold hs)

theorem scan_stopped_empty {m K : ℕ} (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K)
    (hL : StoppedEmpty L) : StoppedEmpty (accountScan G ep j L) := by
  induction j generalizing L with
  | zero => exact hL
  | succ j ih => exact ih _ (inner_stopped_empty G ep j L hL)

theorem phase_stopped_empty {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (L : Ledger (V := V) m K)
    (hL : StoppedEmpty L) : StoppedEmpty (accountPhase G ep L) :=
  clean_stopped_empty hm ep _ (scan_stopped_empty G ep K _ hL)

theorem block_stopped_empty {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (j : ℕ)
    (L : Ledger (V := V) m K) (hL : StoppedEmpty L) : StoppedEmpty (accountBlock G ep j L) := by
  induction j with
  | zero => exact hL
  | succ j ih => exact phase_stopped_empty G hm ep _ ih

theorem outer_stopped_empty {m K : ℕ} (hm : 1 ≤ m) (j : ℕ)
    (L : Ledger (V := V) m K) (hL : StoppedEmpty L) : StoppedEmpty (accountOuter G j L) := by
  induction j generalizing L with
  | zero => exact hL
  | succ j ih => exact ih _ (block_stopped_empty G hm _ (2 * m) L hL)

theorem actual_pending_zero {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    (actualLedger G m K).pending v = 0 := by
  have hi : StoppedEmpty (initialLedger (V := V) m K) := by
    simp [StoppedEmpty, initialLedger, initial]
  have h := outer_stopped_empty G hm (K + target m K) (initialLedger m K) hi
  change StoppedEmpty (actualLedger G m K) at h
  apply h v
  rw [actual_state]
  exact all_stopped G hm hk hdegree v

/-- Exact equality of the objectives is proved from the executed protocol,
not supplied as a primal/dual solver contract. -/
theorem actual_paid_eq_primal {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) :
    (∑ v, (actualLedger G m K).paid v) = ∑ v, ((finalState G m K v).primal : ℝ) := by
  simpa only [actual_pending_zero G hm hk hdegree, zero_add] using actual_conserved G (K := K) hm

end Paper.Density.RationalDualFlush

#print axioms Paper.Density.RationalDualFlush.inner_stopped_empty
#print axioms Paper.Density.RationalDualFlush.clean_stopped_empty
#print axioms Paper.Density.RationalDualFlush.actual_pending_zero
#print axioms Paper.Density.RationalDualFlush.actual_paid_eq_primal
