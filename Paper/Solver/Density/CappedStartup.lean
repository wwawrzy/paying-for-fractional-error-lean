import Paper.Solver.Density.CappedPacketRounds
import Paper.Solver.Density.CappedInitialization

/-! One local degree broadcast constructs the compact initial state. The
instruction receives only its own neighbor list and neighbor messages. Its
maximum equals the denominator used in the initial-packing proof, without
any supplied maximum-degree bound. Natural-message encoding is separate. -/

namespace Paper.Density.CappedStartup

open BroadcastModel SevenFoundation

variable {V : Type} [DecidableEq V]

def degreeRound (cap : ℚ) : Round V PUnit CappedCounterState.State ℕ where
  send _ N _ := N.card + 1
  update _ N _ msg := CappedCounterState.initial cap
    (max (N.card + 1) (N.attach.sup msg))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degreeRound_eq (cap : ℚ) (v : V) :
    eval G (degreeRound cap) (fun _ => PUnit.unit) v =
      CappedCounterState.initial cap (CappedInitialization.denominator G v) := by
  have hcard (u : V) : (G.neighborFinset u).card + 1 = (closed G u).card := by
    rw [UnitDomination.occurrence_count]
    rfl
  have hsup : CappedInitialization.denominator G v =
      max (closed G v).card ((G.neighborFinset v).sup (fun u => (closed G u).card)) := by
    unfold CappedInitialization.denominator
    conv_lhs => rw [UnitDomination.closed_eq_insert, Finset.sup_insert]
  change CappedCounterState.initial cap
    (max ((G.neighborFinset v).card + 1)
      ((G.neighborFinset v).attach.sup (fun u => (G.neighborFinset u).card + 1))) = _
  rw [Finset.sup_attach (G.neighborFinset v) (fun u => (G.neighborFinset u).card + 1)]
  simp_rw [hcard]
  rw [← hsup]

theorem startup_denominator (cap : ℚ) (v : V) :
    (eval G (degreeRound cap) (fun _ => PUnit.unit) v).denominator =
      CappedInitialization.denominator G v := by
  rw [degreeRound_eq]
  rfl

theorem startup_decode (cap : ℚ) (m : ℕ) (v : V) :
    CappedCounterState.decode cap m (eval G (degreeRound cap) (fun _ => PUnit.unit) v) =
      min cap (1 / (CappedInitialization.denominator G v : ℚ)) := by
  rw [degreeRound_eq, CappedCounterState.initial_decode]

theorem startup_cast (cap : ℚ) (m : ℕ) (v : V) :
    (CappedCounterState.decode cap m
      (eval G (degreeRound cap) (fun _ => PUnit.unit) v) : ℝ) =
      CappedInitialization.initial G (cap : ℝ) v := by
  rw [startup_decode]
  simp only [Rat.cast_min, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    CappedInitialization.initial]

end Paper.Density.CappedStartup

#print axioms Paper.Density.CappedStartup.degreeRound_eq
#print axioms Paper.Density.CappedStartup.startup_denominator
#print axioms Paper.Density.CappedStartup.startup_decode
#print axioms Paper.Density.CappedStartup.startup_cast
