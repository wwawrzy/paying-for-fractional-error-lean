import Paper.Solver.Density.CappedCounterState

/-! Raw broadcast execution using compact counter packets. Rational values
are reconstructed privately from the denominator, exponent, and cap bit.
The second broadcast contains only tightness bits. Prefix encodings and
packet-length analysis are separate from these execution semantics. -/

namespace Paper.Density.CappedPacketRounds

open BroadcastModel
open CappedCounterState (State decode)
open scoped BigOperators

variable {V : Type} [DecidableEq V]

def tightRound (cap : ℚ) (m : ℕ) (rho : ℚ) : Round V State (State × Bool) State where
  send _ _ s := s
  update _ N s msg :=
    (s, decide (rho ≤ decode cap m s + ∑ u : N, decode cap m (msg u)))

def freezeRound (cap : ℚ) (m : ℕ) : Round V (State × Bool) State Bool where
  send _ _ s := s.2
  update _ N s msg := CappedCounterState.step cap m
    (decide (s.2 = true ∨ ∃ u : N, msg u = true)) s.1

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def transition (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) : V → State :=
  eval G (freezeRound cap m) (eval G (tightRound cap m rho) s)

theorem tightRound_value (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (eval G (tightRound cap m rho) s v).1 = s v := rfl

theorem tightRound_flag (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (eval G (tightRound cap m rho) s v).2 =
      (eval G (CappedRationalRounds.tightRound rho) (fun u => decode cap m (s u)) v).2 := rfl

/-- Decoding actual packet execution gives the already verified rational
two-round transition, without assuming correctness of any packet output. -/
theorem transition_decode (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (s : V → State) :
    (fun v => decode cap m (transition G cap m rho s v)) =
      CappedRationalRounds.transition G cap (CappedCounterState.scale m) rho
        (fun v => decode cap m (s v)) := by
  funext v
  let tight := eval G (CappedRationalRounds.tightRound rho) (fun u => decode cap m (s u))
  change decode cap m (CappedCounterState.step cap m
      (decide ((tight v).2 = true ∨ ∃ u : G.neighborFinset v, (tight u).2 = true)) (s v)) =
    if (tight v).2 = true ∨ ∃ u : G.neighborFinset v, (tight u).2 = true
    then decode cap m (s v) else min cap (CappedCounterState.scale m * decode cap m (s v))
  rw [CappedCounterState.step_decode cap hm hcap]
  simp only [decide_eq_true_eq]

theorem transition_denominator (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (transition G cap m rho s v).denominator = (s v).denominator := by
  unfold transition eval freezeRound
  exact CappedCounterState.step_denominator cap m _ _

theorem transition_exponent_le (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    (transition G cap m rho s v).exponent ≤ (s v).exponent + 1 := by
  unfold transition eval freezeRound
  exact CappedCounterState.step_exponent_le cap m _ _

/-- The compact packets implement the real capped dynamics exactly. -/
theorem transition_cast (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (s : V → State) :
    (fun v => (decode cap m (transition G cap m rho s v) : ℝ)) =
      CappedDynamics.step G (cap : ℝ) (CappedCounterState.scale m : ℝ) (rho : ℝ)
        (fun v => (decode cap m (s v) : ℝ)) := by
  have he := congrArg (fun f : V → ℚ => fun v => (f v : ℝ))
    (transition_decode G cap hm hcap rho s)
  exact he.trans (CappedRationalRounds.transition_cast G cap (CappedCounterState.scale m) rho
    (fun v => decode cap m (s v)))

end Paper.Density.CappedPacketRounds

#print axioms Paper.Density.CappedPacketRounds.transition_decode
#print axioms Paper.Density.CappedPacketRounds.transition_denominator
#print axioms Paper.Density.CappedPacketRounds.transition_exponent_le
#print axioms Paper.Density.CappedPacketRounds.transition_cast
