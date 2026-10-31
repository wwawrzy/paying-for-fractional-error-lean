import Paper.Solver.Density.RationalCleanupCharge

/-! Local dual charging for a whole literal phase, including restart,
the descending scan, and cleanup. -/
namespace Paper.Density.RationalPhaseCharge
open BroadcastModel RationalRuntime RationalCounters RationalRequirementDecay RationalEpochDecay
open RationalDualLedger RationalPendingBound RationalPendingExecution RationalPendingBudget RationalCleanupCharge SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def restart {m K : ℕ} (L : Ledger (V := V) m K) : Ledger (V := V) m K :=
  { L with state := fun v => { L.state v with active := !(L.state v).stopped } }

noncomputable def beforeClean {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) : Ledger (V := V) m K :=
  accountScan G ep K (restart L)

theorem phase_eq {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) :
    accountPhase G ep L = accountClean ep (beforeClean G ep L) := rfl

theorem scan_paid {m K : ℕ} (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K) :
    (accountScan G ep j L).paid = L.paid := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    change (accountScan G ep j (accountInner G ep j L)).paid = _
    rw [ih]
    rfl

theorem before_paid {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) :
    (beforeClean G ep L).paid = L.paid := scan_paid G ep K (restart L)

theorem before_value {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) (v : V) :
    value ((beforeClean G ep L).state v) = value (L.state v) := by
  unfold beforeClean
  rw [scan_state]
  exact scan_value G m K ep K (restart L).state v

theorem before_consistent {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K)
    (hc : ∀ v, Consistent (L.state v)) : ∀ v, Consistent ((beforeClean G ep L).state v) := by
  unfold beforeClean
  rw [scan_state]
  exact scan_consistent G m K ep K (restart L).state hc

def paidMass {m K : ℕ} (L : Ledger (V := V) m K) (v : V) : ℝ := UnitDomination.mass G L.paid v

theorem phase_small {m K : ℕ} (ep : ℤ) (L : Ledger (V := V) m K) (v : V) :
    ((accountPhase G ep L).state v).weight < denominator m K :=
  RationalBalance.clean_weight_lt ((beforeClean G ep L).state v)

theorem phase_charge {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (ep : ℤ)
    (L : Ledger (V := V) m K) (hc : ∀ v, Consistent (L.state v))
    (hP : PendingBound ep L) (hw : ∀ v, (L.state v).weight < denominator m K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    paidMass G (accountPhase G ep L) v - paidMass G L v ≤
      (coefficient m : ℝ) * denominator m K / threshold m ep *
        (fullMass G L.state v - fullMass G (accountPhase G ep L).state v) := by
  let S := beforeClean G ep L
  have hb : Budget ep S := phase_scan_budget G hm hk ep L hP hw hdegree
  have hcs : ∀ u, Consistent (S.state u) := before_consistent G ep L hc
  have hpaid : paidMass G (accountPhase G ep L) v - paidMass G L v =
      ∑ u ∈ closed G v, payout ep (S.state u) (S.pending u) := by
    rw [phase_eq]
    unfold paidMass UnitDomination.mass
    simp only [accountClean, Finset.sum_add_distrib, before_paid]
    ring
  have hmass : fullMass G S.state v = fullMass G L.state v := by
    apply Finset.sum_congr rfl
    intro u _
    exact congrArg (fun x : ℚ => (x : ℝ)) (before_value G ep L u)
  rw [hpaid]
  calc
    _ ≤ ∑ u ∈ closed G v, (coefficient m : ℝ) * denominator m K / threshold m ep *
        ((value (S.state u) : ℝ) - (value (clean (S.state u)) : ℝ)) :=
      Finset.sum_le_sum (fun u _ => cleanup_charge hm ep S hcs hb u)
    _ = (coefficient m : ℝ) * denominator m K / threshold m ep *
        (fullMass G S.state v - fullMass G (accountPhase G ep L).state v) := by
      rw [phase_eq]
      simp only [fullMass, accountClean, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      rfl
    _ = _ := by rw [hmass]

end Paper.Density.RationalPhaseCharge

#print axioms Paper.Density.RationalPhaseCharge.before_value
#print axioms Paper.Density.RationalPhaseCharge.phase_small
#print axioms Paper.Density.RationalPhaseCharge.phase_charge
