import Paper.Solver.Density.RationalPhaseCharge

/-! Summing actual phase payments at one fixed threshold telescopes. The
bound does not acquire a factor for the padded number of phases. -/
namespace Paper.Density.RationalEpochCharge
open RationalRuntime RationalCounters RationalRequirementDecay RationalEpochDecay
open RationalDualLedger RationalPendingBound RationalPendingExecution RationalCleanupCharge RationalPhaseCharge SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem block_small {m K : ℕ} (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K)
    (hw : ∀ v, (L.state v).weight < denominator m K) :
    ∀ v, ((accountBlock G ep j L).state v).weight < denominator m K := by
  induction j with
  | zero => exact hw
  | succ j _ => exact phase_small G ep (accountBlock G ep j L)

theorem block_charge {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (ep : ℤ) (j : ℕ)
    (L : Ledger (V := V) m K) (hc : ∀ v, Consistent (L.state v))
    (hP : PendingBound ep L) (hw : ∀ v, (L.state v).weight < denominator m K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    paidMass G (accountBlock G ep j L) v - paidMass G L v ≤
      (coefficient m : ℝ) * denominator m K / threshold m ep *
        (fullMass G L.state v - fullMass G (accountBlock G ep j L).state v) := by
  induction j with
  | zero => simp only [accountBlock, sub_self, mul_zero, le_refl]
  | succ j ih =>
    let A := accountBlock G ep j L
    have hphase := phase_charge G hm hk ep A (block_consistent G ep j L hc)
      (block_pending_bound G hm ep j L hc hP) (block_small G ep j L hw) hdegree v
    have hprev : paidMass G A v - paidMass G L v ≤
        (coefficient m : ℝ) * denominator m K / threshold m ep *
          (fullMass G L.state v - fullMass G A.state v) := ih
    change paidMass G (accountPhase G ep A) v - paidMass G L v ≤
      (coefficient m : ℝ) * denominator m K / threshold m ep *
        (fullMass G L.state v - fullMass G (accountPhase G ep A).state v)
    nlinarith only [hprev, hphase]

end Paper.Density.RationalEpochCharge

#print axioms Paper.Density.RationalEpochCharge.block_small
#print axioms Paper.Density.RationalEpochCharge.block_charge
