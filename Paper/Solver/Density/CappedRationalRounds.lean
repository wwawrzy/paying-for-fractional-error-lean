import Paper.Communication.BroadcastModel
import Paper.Solver.Density.CappedDynamics

/-! Two executable rational broadcast rounds for one capped dual update.
The first broadcasts the current value and computes own row tightness. The
second broadcasts that bit and freezes precisely the closed neighbors of
tight rows. These raw rounds do not supply finite-bit encodings or a message
size bound. No maximum degree or stopping horizon is an instruction input. -/

namespace Paper.Density.CappedRationalRounds

open BroadcastModel SevenFoundation
open scoped BigOperators

variable {V : Type} [DecidableEq V]

def tightRound (rho : ℚ) : Round V ℚ (ℚ × Bool) ℚ where
  send _ _ y := y
  update _ N y msg := (y, decide (rho ≤ y + ∑ u : N, msg u))

def freezeRound (cap factor : ℚ) : Round V (ℚ × Bool) ℚ Bool where
  send _ _ s := s.2
  update _ N s msg :=
    if s.2 = true ∨ ∃ u : N, msg u = true then s.1 else min cap (factor * s.1)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def transition (cap factor rho : ℚ) (y : V → ℚ) : V → ℚ :=
  eval G (freezeRound cap factor) (eval G (tightRound rho) y)

theorem row_closed (y : V → ℚ) (v : V) :
    y v + (∑ u : G.neighborFinset v, y u) = ∑ u ∈ closed G v, y u := by
  rw [UnitDomination.closed_eq_insert, Finset.sum_insert (by simp)]
  exact congrArg (fun z => y v + z) (Finset.sum_coe_sort (G.neighborFinset v) y)

theorem tightRound_value (rho : ℚ) (y : V → ℚ) (v : V) :
    (eval G (tightRound rho) y v).1 = y v := rfl

theorem tightRound_flag (rho : ℚ) (y : V → ℚ) (v : V) :
    (eval G (tightRound rho) y v).2 = true ↔ rho ≤ ∑ u ∈ closed G v, y u := by
  change decide (rho ≤ y v + ∑ u : G.neighborFinset v, y u) = true ↔ _
  rw [decide_eq_true_eq, row_closed]

theorem mass_cast (y : V → ℚ) (r : V) :
    ((∑ u ∈ closed G r, y u : ℚ) : ℝ) =
      UnitDomination.mass G (fun u => (y u : ℝ)) r := by
  simp only [Rat.cast_sum, UnitDomination.mass]

/-- The second round sees exactly the tight rows in the receiver's closed
neighborhood, including its own locally computed tightness bit. -/
theorem freeze_test (rho : ℚ) (y : V → ℚ) (v : V) :
    ((eval G (tightRound rho) y v).2 = true ∨
      ∃ u : G.neighborFinset v, (eval G (tightRound rho) y u).2 = true) ↔
      CappedDynamics.blocked G (rho : ℝ) (fun u => (y u : ℝ)) v := by
  have hcast (r : V) : (rho ≤ ∑ u ∈ closed G r, y u) ↔
      (rho : ℝ) ≤ UnitDomination.mass G (fun u => (y u : ℝ)) r := by
    rw [← mass_cast]
    exact Rat.cast_le.symm
  simp_rw [tightRound_flag, hcast]
  constructor
  · rintro (hself | ⟨u, hu⟩)
    · exact ⟨v, self_mem_closed G v, hself⟩
    · exact ⟨u, (mem_closed G u v).mpr
        (Or.inr ((SimpleGraph.mem_neighborFinset G v u).mp u.property)), hu⟩
  · rintro ⟨r, hr, hm⟩
    rcases (mem_closed G r v).mp hr with he | ha
    · subst r
      exact Or.inl hm
    · exact Or.inr ⟨⟨r, (SimpleGraph.mem_neighborFinset G v r).mpr ha⟩, hm⟩

/-- Exact semantics of the evaluated two-round rational transition. -/
theorem transition_cast (cap factor rho : ℚ) (y : V → ℚ) :
    (fun v => (transition G cap factor rho y v : ℝ)) =
      CappedDynamics.step G (cap : ℝ) (factor : ℝ) (rho : ℝ)
        (fun v => (y v : ℝ)) := by
  funext v
  change ((if (eval G (tightRound rho) y v).2 = true ∨
      ∃ u : G.neighborFinset v, (eval G (tightRound rho) y u).2 = true
    then y v else min cap (factor * y v) : ℚ) : ℝ) = _
  by_cases hb : CappedDynamics.blocked G (rho : ℝ) (fun u => (y u : ℝ)) v
  · rw [if_pos ((freeze_test G rho y v).mpr hb)]
    exact (if_pos hb).symm
  · rw [if_neg (fun h => hb ((freeze_test G rho y v).mp h))]
    rw [CappedDynamics.step, if_neg hb, Rat.cast_min, Rat.cast_mul]

end Paper.Density.CappedRationalRounds

#print axioms Paper.Density.CappedRationalRounds.tightRound_flag
#print axioms Paper.Density.CappedRationalRounds.freeze_test
#print axioms Paper.Density.CappedRationalRounds.transition_cast
