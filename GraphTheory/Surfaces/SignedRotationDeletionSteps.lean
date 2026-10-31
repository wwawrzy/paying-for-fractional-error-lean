import GraphTheory.Surfaces.SignedRotationDeletionBypass

/-! A deleted edge has distinct endpoints, so a surviving vertex cycle skips
at most one removed dart. This gives an exhaustive description of deletion. -/

namespace SimpleGraph.SignedRotation

open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion

variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- The successor of a removed dart reached from a surviving dart survives. -/
theorem removed_successor_survives (r : SignedRotation (G ⊔ edge u v))
    (d : G.Dart) (b : Bool)
    (h : pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) = Sum.inr b) :
    ∃ e : G.Dart, pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inr b) = Sum.inl e := by
  let p := pulledPerm G u v hne hmiss r.toRotationSystem
  change p (Sum.inl d) = Sum.inr b at h
  have hs := pulledPerm_source G u v hne hmiss r.toRotationSystem (Sum.inr b)
  change (augmentedDart G u v hne (p (Sum.inr b))).fst =
    (augmentedDart G u v hne (Sum.inr b)).fst at hs
  cases hp : p (Sum.inr b) with
  | inl e => exact ⟨e, rfl⟩
  | inr c =>
    have hbc : b ≠ c := by
      intro heq
      subst c
      have heq := p.injective (h.trans hp.symm)
      cases heq
    rw [hp] at hs
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact (hne hs.symm).elim
    · exact (hne hs).elim
    · exact (hbc rfl).elim

/-- Every new successor is either the old successor or its successor after
one removed dart; there are no further hidden bypass steps. -/
theorem deleteAddedEdge_step_cases (r : SignedRotation (G ⊔ edge u v)) (d : G.Dart) :
    ∃ e : G.Dart, (deleteAddedEdge G u v hne hmiss r).σ d = e ∧
      (pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) = Sum.inl e ∨
       ∃ b : Bool,
         pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) = Sum.inr b ∧
         pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inr b) = Sum.inl e) := by
  cases hp : pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) with
  | inl e =>
    refine ⟨e, ?_, Or.inl rfl⟩
    apply deleteAddedEdge_sigma
    have h := congrArg (augmentedDartEquiv G u v hne hmiss) hp
    simpa only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
  | inr b =>
    obtain ⟨e, he⟩ := removed_successor_survives G u v hne hmiss r d b hp
    exact ⟨e, deleteAddedEdge_bypass G u v hne hmiss r d e b hp he,
      Or.inr ⟨b, rfl, he⟩⟩

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.removed_successor_survives
#print axioms SimpleGraph.SignedRotation.deleteAddedEdge_step_cases
