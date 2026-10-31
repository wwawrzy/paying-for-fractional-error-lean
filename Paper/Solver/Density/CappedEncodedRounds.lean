import Paper.Solver.Density.CappedStateCode
import Paper.Solver.Density.CappedPacketRounds

/-! Actual finite-string broadcasts for the capped transition. Every sender
uses the same graph-independent prefix codec, with no public degree bound. -/
namespace Paper.Density.CappedEncodedRounds
open BroadcastModel
open CappedCounterState (State decode)
variable {V : Type} [DecidableEq V]

def tightRound (cap : ℚ) (m : ℕ) (rho : ℚ) : Round V State (State × Bool) (List Bool) :=
  PrefixBroadcast.round CappedStateCode.code (CappedPacketRounds.tightRound cap m rho)

def freezeRound (cap : ℚ) (m : ℕ) : Round V (State × Bool) State (List Bool) :=
  PrefixBroadcast.round PrefixCode.bool (CappedPacketRounds.freezeRound cap m)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def transition (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) : V → State :=
  eval G (freezeRound cap m) (eval G (tightRound cap m rho) s)

theorem transition_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) :
    transition G cap m rho s = CappedPacketRounds.transition G cap m rho s := by
  unfold transition tightRound freezeRound
  rw [PrefixBroadcast.eval_eq, PrefixBroadcast.eval_eq]
  rfl

theorem transition_cast (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (s : V → State) :
    (fun v => (decode cap m (transition G cap m rho s v) : ℝ)) =
      CappedDynamics.step G (cap : ℝ) (CappedCounterState.scale m : ℝ) (rho : ℝ)
        (fun v => (decode cap m (s v) : ℝ)) := by
  rw [transition_eq]
  exact CappedPacketRounds.transition_cast G cap hm hcap rho s

theorem transition_denominator (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (transition G cap m rho s v).denominator = (s v).denominator := by
  rw [transition_eq]
  exact CappedPacketRounds.transition_denominator G cap m rho s v

theorem transition_exponent_le (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (transition G cap m rho s v).exponent ≤ (s v).exponent+1 := by
  rw [transition_eq]
  exact CappedPacketRounds.transition_exponent_le G cap m rho s v

/-- The width is proved for the sent string, not supplied to the sender. -/
theorem tight_message_bound (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State)
    (Delta extra : ℕ) (hdegree : Delta ≤ Fintype.card V)
    (hden : ∀ v, (s v).denominator ≤ Delta+1)
    (hexp : ∀ v, (s v).exponent ≤ CappedGrowth.timeBound m Delta+extra) (v : V) :
    ((tightRound cap m rho).send v (G.neighborFinset v) (s v)).length ≤
      (2*m+2*extra+5)*Nat.clog 2 (Fintype.card V+2) :=
  CappedStateCode.logarithmic_length m Delta (Fintype.card V) extra (s v)
    hdegree (hden v) (hexp v)

theorem freeze_message_length (cap : ℚ) (m : ℕ) (s : State × Bool) (v : V) (N : Finset V) :
    ((freezeRound cap m).send v N s).length = 1 := rfl

end Paper.Density.CappedEncodedRounds
#print axioms Paper.Density.CappedEncodedRounds.transition_cast
#print axioms Paper.Density.CappedEncodedRounds.transition_denominator
#print axioms Paper.Density.CappedEncodedRounds.transition_exponent_le
#print axioms Paper.Density.CappedEncodedRounds.tight_message_bound
