import Paper.Solver.Density.CappedStartup
import Paper.Solver.Density.CappedEncodedRounds

/-! Repeated finite-string execution from a local degree broadcast. The
transition and startup have no degree or horizon input. The natural index
only names a prefix of the execution for convergence and resource analysis. -/
namespace Paper.Density.CappedExecution
open BroadcastModel
open CappedCounterState (State decode)
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def initial (cap : ℚ) : V → State :=
  eval G (PrefixBroadcast.round PrefixCode.nat (CappedStartup.degreeRound cap))
    (fun _ => PUnit.unit)

def run (cap : ℚ) (m : ℕ) (rho : ℚ) : ℕ → V → State
  | 0 => initial G cap
  | n+1 => CappedEncodedRounds.transition G cap m rho (run cap m rho n)

theorem initial_eq (cap : ℚ) (v : V) :
    initial G cap v = CappedCounterState.initial cap (CappedInitialization.denominator G v) := by
  unfold initial
  rw [PrefixBroadcast.eval_eq]
  exact CappedStartup.degreeRound_eq G cap v

theorem initial_cast (cap : ℚ) (m : ℕ) (v : V) :
    (decode cap m (initial G cap v) : ℝ) = CappedInitialization.initial G (cap : ℝ) v := by
  unfold initial
  rw [PrefixBroadcast.eval_eq]
  exact CappedStartup.startup_cast G cap m v

/-- Every prefix of actual encoded execution refines the mathematical
recurrence, starting from the local packing rather than an assumed vector. -/
theorem run_cast (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (n : ℕ) :
    (fun v => (decode cap m (run G cap m rho n v) : ℝ)) =
      CappedDynamics.run G (cap : ℝ) (CappedCounterState.scale m : ℝ) (rho : ℝ)
        (CappedInitialization.initial G (cap : ℝ)) n := by
  induction n with
  | zero => funext v; exact initial_cast G cap m v
  | succ n ih =>
    change (fun v => (decode cap m (CappedEncodedRounds.transition G cap m rho
      (run G cap m rho n) v) : ℝ)) = _
    rw [CappedEncodedRounds.transition_cast G cap hm hcap rho, ih]
    rfl

theorem run_denominator (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) (v : V) :
    (run G cap m rho n v).denominator = CappedInitialization.denominator G v := by
  induction n with
  | zero => rw [run, initial_eq]; rfl
  | succ n ih => rw [run, CappedEncodedRounds.transition_denominator, ih]

theorem run_exponent_le (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) (v : V) :
    (run G cap m rho n v).exponent ≤ n := by
  induction n with
  | zero => rw [run, initial_eq]; exact Nat.le_refl 0
  | succ n ih =>
    exact (CappedEncodedRounds.transition_exponent_le G cap m rho _ v).trans
      (Nat.add_le_add_right ih 1)

/-- Reachable packet lengths, including an explicit allowance for final
certificate phases. The analysis bound is absent from run and both senders. -/
theorem packet_length (cap : ℚ) (m : ℕ) (rho : ℚ) (n Delta extra : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Delta) (hD : Delta ≤ Fintype.card V)
    (hn : n ≤ CappedGrowth.timeBound m Delta+extra) (v : V) :
    ((CappedEncodedRounds.tightRound cap m rho).send v (G.neighborFinset v)
      (run G cap m rho n v)).length ≤
      (2*m+2*extra+5)*Nat.clog 2 (Fintype.card V+2) := by
  apply CappedEncodedRounds.tight_message_bound G cap m rho _ Delta extra hD
  · intro u
    rw [run_denominator]
    exact CappedInitialization.denominator_le G hdegree u
  · intro u
    exact (run_exponent_le G cap m rho n u).trans hn

theorem startup_message_length (cap : ℚ) (v : V) :
    ((PrefixBroadcast.round PrefixCode.nat (CappedStartup.degreeRound cap)).send
      v (G.neighborFinset v) PUnit.unit).length ≤
      2*Nat.clog 2 (Fintype.card V+2)+1 := by
  change (PrefixCode.nat.encode ((G.neighborFinset v).card+1)).length ≤ _
  have hh := PrefixCode.nat_length_bound ((G.neighborFinset v).card+1)
  have hc : (G.neighborFinset v).card ≤ Fintype.card V := Finset.card_le_univ _
  have hl := Nat.clog_mono_right 2 (show (G.neighborFinset v).card+1+1 ≤
      Fintype.card V+2 by omega)
  omega

end Paper.Density.CappedExecution
#print axioms Paper.Density.CappedExecution.run_cast
#print axioms Paper.Density.CappedExecution.run_denominator
#print axioms Paper.Density.CappedExecution.run_exponent_le
#print axioms Paper.Density.CappedExecution.packet_length
#print axioms Paper.Density.CappedExecution.startup_message_length
