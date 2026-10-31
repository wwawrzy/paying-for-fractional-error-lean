import GraphTheory.Surfaces.SignedRotationDeletionSteps

/-! A removed dart at a nonisolated surviving vertex has a surviving rotation
successor. No connectedness assumption on the remaining graph is needed. -/

namespace SimpleGraph.SignedRotation

open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion

variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- Local cyclicity prevents the removed dart from being fixed when another
dart at its source survives. -/
theorem fresh_successor_survives (r : SignedRotation (G ⊔ edge u v))
    (b : Bool) (d : G.Dart)
    (hd : (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    ∃ e : G.Dart, pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inr b) = Sum.inl e := by
  let p := pulledPerm G u v hne hmiss r.toRotationSystem
  have hc := pulledPerm_sameCycle G u v hne hmiss r.faithfulRotation
    (Sum.inr b) (Sum.inl d) hd
  have hnf : p (Sum.inr b) ≠ Sum.inr b := by
    intro h
    have heq := hc.eq_of_left h
    cases heq
  have hs := pulledPerm_source G u v hne hmiss r.toRotationSystem (Sum.inr b)
  change (augmentedDart G u v hne (p (Sum.inr b))).fst =
    (augmentedDart G u v hne (Sum.inr b)).fst at hs
  cases hp : p (Sum.inr b) with
  | inl e => exact ⟨e, rfl⟩
  | inr c =>
    rw [hp] at hs
    cases b <;> cases c
    · exact (hnf hp).elim
    · exact (hne hs.symm).elim
    · exact (hne hs).elim
    · exact (hnf hp).elim

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.fresh_successor_survives
