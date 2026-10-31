import Paper.Solver.Density.RationalPendingCleanup

/-! The pending-allocation inequality holds throughout the actual nested
execution. Lowering the public epoch threshold preserves the inequality. -/
namespace Paper.Density.RationalPendingExecution
open BroadcastModel RationalRuntime RationalCounters RationalRequirementDecay RationalEpochDecay
open RationalDualLedger RationalPendingBound RationalPendingCleanup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem pending_lower_threshold {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ)
    (L : Ledger (V := V) m K) (hL : PendingBound (ep + 1) L) : PendingBound ep L := by
  have hs : (1 : ℝ) ≤ (scale m : ℚ) := by exact_mod_cast (scale_bounds hm).1.le
  have ht : (threshold m ep : ℝ) ≤ (threshold m (ep + 1) : ℝ) := by
    rw [threshold_succ hm, Rat.cast_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (threshold_pos hm ep).le
  intro v
  have hr : (0 : ℝ) ≤ (value (L.state v) : ℚ) := by exact_mod_cast value_nonneg (L.state v)
  exact (hL v).trans (div_le_div_of_nonneg_left
    (mul_nonneg hr (Nat.cast_nonneg _)) (threshold_pos hm ep) ht)

theorem scan_pending_bound {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (j : ℕ)
    (L : Ledger (V := V) m K) (hL : PendingBound ep L) :
    PendingBound ep (accountScan G ep j L) := by
  induction j generalizing L with
  | zero => exact hL
  | succ j ih => exact ih _ (inner_pending_bound G hm ep j L hL)

theorem phase_pending_bound {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ)
    (L : Ledger (V := V) m K) (hc : ∀ v, Consistent (L.state v)) (hL : PendingBound ep L) :
    PendingBound ep (accountPhase G ep L) := by
  let R : Ledger (V := V) m K :=
    { L with state := fun v => { L.state v with active := !(L.state v).stopped } }
  have hr : ∀ v, Consistent (R.state v) := hc
  have hb : PendingBound ep R := hL
  have hcs : ∀ v, Consistent ((accountScan G ep K R).state v) := by
    rw [scan_state]
    exact scan_consistent G m K ep K R.state hr
  exact clean_pending_bound hm ep _ hcs (scan_pending_bound G hm ep K R hb)

theorem block_consistent {m K : ℕ} (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K)
    (hc : ∀ v, Consistent (L.state v)) : ∀ v, Consistent ((accountBlock G ep j L).state v) := by
  rw [block_state]
  exact iterate_consistent G _ (phase_consistent G m K ep) j L.state hc

theorem block_pending_bound {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (j : ℕ)
    (L : Ledger (V := V) m K) (hc : ∀ v, Consistent (L.state v)) (hL : PendingBound ep L) :
    PendingBound ep (accountBlock G ep j L) := by
  induction j with
  | zero => exact hL
  | succ j ih => exact phase_pending_bound G hm ep _ (block_consistent G ep j L hc) ih

theorem outer_pending_bound {m K : ℕ} (hm : 1 ≤ m) (j : ℕ)
    (L : Ledger (V := V) m K) (hc : ∀ v, Consistent (L.state v))
    (hL : PendingBound ((j : ℤ) - target m K - 2) L) :
    PendingBound (-(target m K : ℤ) - 2) (accountOuter G j L) := by
  induction j generalizing L with
  | zero => simpa only [accountOuter, Int.natCast_zero, zero_sub] using hL
  | succ j ih =>
    let ep : ℤ := (j : ℤ) - target m K - 1
    let A := accountBlock G ep (2 * m) L
    have hinput : ((j + 1 : ℕ) : ℤ) - target m K - 2 = ep := by dsimp only [ep]; push_cast; ring
    have houtput : ep = ((j : ℤ) - target m K - 2) + 1 := by dsimp only [ep]; ring
    have hb : PendingBound ep A := block_pending_bound G hm ep (2 * m) L hc
      (by simpa only [hinput] using hL)
    have hnext : PendingBound ((j : ℤ) - target m K - 2) A :=
      pending_lower_threshold hm _ A (by simpa only [houtput] using hb)
    exact ih A (block_consistent G ep (2 * m) L hc) hnext

theorem actual_pending_bound {m K : ℕ} (hm : 1 ≤ m) :
    PendingBound (-(target m K : ℤ) - 2) (actualLedger G m K) := by
  have hi : PendingBound (((K + target m K : ℕ) : ℤ) - target m K - 2)
      (initialLedger (V := V) m K) := by
    simp [PendingBound, initialLedger, initial]
  exact outer_pending_bound G hm (K + target m K) (initialLedger m K)
    (fun _ => initial_consistent m K) hi

end Paper.Density.RationalPendingExecution

#print axioms Paper.Density.RationalPendingExecution.pending_lower_threshold
#print axioms Paper.Density.RationalPendingExecution.phase_pending_bound
#print axioms Paper.Density.RationalPendingExecution.actual_pending_bound
