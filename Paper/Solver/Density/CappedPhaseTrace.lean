import Paper.Communication.CachedProgram
import Paper.Solver.Density.CappedOutputRegister
import Paper.Solver.Density.CappedFrozenMessages

/-! The generic per-slot trace of the actual phase with a private output
register is exactly the six-message trace used in the permanence proof.
This identifies the cached words with executed senders; it does not itself
implement or prove the repeated silent execution. -/

namespace Paper.Density.CappedPhaseTrace

open CappedCounterState (State)

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem phase_sent (cap : ℚ) (m : ℕ) (rho : ℚ)
    (s : V → State × Option Bool) (i : ℕ) (v : V) (hi : i < 6) :
    (CappedOutputRegister.phase cap m rho).sent G s i v =
      ((CappedFrozenMessages.phaseMessages G cap m rho (fun u => (s u).1) v)[i]?).getD [] := by
  interval_cases i <;> rfl

/-- The fourth slot is the sender's locally computed readiness notification. -/
theorem near_notification (cap : ℚ) (m : ℕ) (rho : ℚ)
    (s : V → State × Option Bool) (v : V)
    (hn : (CappedHaltRounds.nearStatuses G cap m rho (fun u => (s u).1) v).near = true) :
    (CappedOutputRegister.phase cap m rho).sent G s 3 v = [true] := by
  rw [phase_sent G cap m rho s 3 v (by decide)]
  exact congrArg (fun word : Option (List Bool) => word.getD [])
    (CappedFrozenMessages.near_notification G cap m rho (fun u => (s u).1) v hn)

/-- Any private register contents give the same permanently cached words
after near=true. Only the decoded protocol state determines the senders. -/
theorem sent_stable (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n k : ℕ) (v : V)
    (hn : (CappedHaltRounds.nearStatuses G cap m rho (CappedExecution.run G cap m rho n) v).near = true)
    (old future : V → Option Bool) (i : ℕ) (hi : i < 6) :
    (CappedOutputRegister.phase cap m rho).sent G
        (fun u => (CappedExecution.run G cap m rho (n + k) u, future u)) i v =
      (CappedOutputRegister.phase cap m rho).sent G
        (fun u => (CappedExecution.run G cap m rho n u, old u)) i v := by
  rw [phase_sent G cap m rho _ i v hi, phase_sent G cap m rho _ i v hi,
    CappedFrozenMessages.phaseMessages_stable G cap hm hcap rho hrho n k v hn]

end Paper.Density.CappedPhaseTrace

#print axioms Paper.Density.CappedPhaseTrace.phase_sent
#print axioms Paper.Density.CappedPhaseTrace.near_notification
#print axioms Paper.Density.CappedPhaseTrace.sent_stable
