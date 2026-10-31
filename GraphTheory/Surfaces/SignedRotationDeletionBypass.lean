import GraphTheory.Surfaces.SignedRotationDeletionCorners

/-! Exact bypass of a removed dart in a signed vertex rotation. -/

namespace SimpleGraph.SignedRotation

open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
open PlaneTopology.PlanePermutationDeletion

variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- When the old rotation traverses a removed dart, deletion joins its two
surviving neighbors directly. Both orientations of the removed edge are covered. -/
theorem deleteAddedEdge_bypass (r : SignedRotation (G ⊔ edge u v))
    (d e : G.Dart) (b : Bool)
    (h₁ : pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) = Sum.inr b)
    (h₂ : pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inr b) = Sum.inl e) :
    (deleteAddedEdge G u v hne hmiss r).σ d = e := by
  let p := pulledPerm G u v hne hmiss r.toRotationSystem
  have he : erasedPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) = Sum.inl e := by
    change erasePoint (erasePoint p (Sum.inr true)) (Sum.inr false) (Sum.inl d) = _
    change p (Sum.inl d) = Sum.inr b at h₁
    change p (Sum.inr b) = Sum.inl e at h₂
    cases b
    · have hfirst : erasePoint p (Sum.inr true) (Sum.inl d) = Sum.inr false := by
        rw [erasePoint_apply_of_ne _ _ _ (by simp) (by rw [h₁]; simp), h₁]
      rw [erasePoint_apply_of_eq _ _ _ hfirst]
      rw [erasePoint_apply_of_ne _ _ _ (by simp) (by rw [h₂]; simp), h₂]
    · have hfirst : erasePoint p (Sum.inr true) (Sum.inl d) = Sum.inl e := by
        rw [erasePoint_apply_of_eq _ _ _ h₁, h₂]
      rw [erasePoint_apply_of_ne _ _ _ (by simp) (by rw [hfirst]; simp), hfirst]
  have hi := restrictLeft_inl_apply _
    (erasedPerm_fixed G u v hne hmiss r.toRotationSystem) d
  change Sum.inl ((deleteAddedEdge G u v hne hmiss r).σ d) = _ at hi
  exact Sum.inl.inj (hi.trans he)

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.deleteAddedEdge_bypass
