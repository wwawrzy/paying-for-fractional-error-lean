import GraphTheory.Surfaces.SignedRotationDeletionNeighbors

/-! Both corners of a removed dart lead to surviving flags when the source
retains an incident edge. -/

namespace SimpleGraph.SignedRotation

open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion

variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- The predecessor also survives at a nonisolated remaining vertex. -/
theorem fresh_predecessor_survives (r : SignedRotation (G ⊔ edge u v))
    (b : Bool) (d : G.Dart)
    (hd : (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    ∃ e : G.Dart,
      (pulledPerm G u v hne hmiss r.toRotationSystem).symm (Sum.inr b) = Sum.inl e := by
  let p := pulledPerm G u v hne hmiss r.toRotationSystem
  obtain ⟨e, he⟩ := fresh_successor_survives G u v hne hmiss r b d hd
  have hnf : p (Sum.inr b) ≠ Sum.inr b := by
    change p (Sum.inr b) = Sum.inl e at he
    rw [he]
    simp
  have hs := pulledPerm_source G u v hne hmiss r.toRotationSystem (p.symm (Sum.inr b))
  change (augmentedDart G u v hne (p (p.symm (Sum.inr b)))).fst =
    (augmentedDart G u v hne (p.symm (Sum.inr b))).fst at hs
  rw [Equiv.apply_symm_apply] at hs
  cases hp : p.symm (Sum.inr b) with
  | inl f => exact ⟨f, rfl⟩
  | inr c =>
    have hpc : p (Sum.inr c) = Sum.inr b := by
      rw [← hp, Equiv.apply_symm_apply]
    rw [hp] at hs
    cases b <;> cases c
    · exact (hnf hpc).elim
    · exact (hne hs).elim
    · exact (hne hs.symm).elim
    · exact (hnf hpc).elim

include hmiss in
/-- Either side of a removed dart reaches a surviving flag in one corner step. -/
theorem fresh_corner_survives (r : SignedRotation (G ⊔ edge u v))
    (b c : Bool) (d : G.Dart)
    (hd : (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    ∃ e : G.Dart, r.cornerFlip (augmentedDart G u v hne (Sum.inr b), c) =
      (augmentedDart G u v hne (Sum.inl e), !c) := by
  cases c
  · obtain ⟨e, he⟩ := fresh_successor_survives G u v hne hmiss r b d hd
    refine ⟨e, ?_⟩
    have h := congrArg (augmentedDartEquiv G u v hne hmiss) he
    have hσ : r.σ (augmentedDart G u v hne (Sum.inr b)) =
        augmentedDart G u v hne (Sum.inl e) := by
      simpa only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm,
        Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
    simp [cornerFlip, hσ]
  · obtain ⟨e, he⟩ := fresh_predecessor_survives G u v hne hmiss r b d hd
    refine ⟨e, ?_⟩
    have hp : pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl e) = Sum.inr b := by
      rw [← he, Equiv.apply_symm_apply]
    have h := congrArg (augmentedDartEquiv G u v hne hmiss) hp
    have hσ : r.σ (augmentedDart G u v hne (Sum.inl e)) =
        augmentedDart G u v hne (Sum.inr b) := by
      simpa only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm,
        Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
    have hi : r.σ.symm (augmentedDart G u v hne (Sum.inr b)) =
        augmentedDart G u v hne (Sum.inl e) := by
      rw [← hσ, Equiv.symm_apply_apply]
    simp [cornerFlip, hi]

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.fresh_predecessor_survives
#print axioms SimpleGraph.SignedRotation.fresh_corner_survives
