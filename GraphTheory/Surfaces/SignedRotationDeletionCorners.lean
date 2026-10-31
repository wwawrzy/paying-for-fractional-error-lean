import GraphTheory.Surfaces.SignedRotationDeletion

/-! Local corner identities for signed edge deletion. These identities isolate
exactly the corners affected by bypassing a removed dart. -/

namespace SimpleGraph.SignedRotation

open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
open PlaneTopology.PlanePermutationDeletion

variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- A rotation step between surviving darts is unchanged by deletion. -/
theorem deleteAddedEdge_sigma (r : SignedRotation (G ⊔ edge u v)) (d e : G.Dart)
    (h : r.σ (augmentedDart G u v hne (Sum.inl d)) =
      augmentedDart G u v hne (Sum.inl e)) :
    (deleteAddedEdge G u v hne hmiss r).σ d = e := by
  have hp : pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) = Sum.inl e := by
    apply (augmentedDartEquiv G u v hne hmiss).injective
    simpa only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
  have he : erasedPerm G u v hne hmiss r.toRotationSystem (Sum.inl d) = Sum.inl e := by
    have hfirst : erasePoint (pulledPerm G u v hne hmiss r.toRotationSystem)
        (Sum.inr true) (Sum.inl d) = Sum.inl e := by
      rw [erasePoint_apply_of_ne _ _ _ (by simp) (by rw [hp]; simp), hp]
    unfold erasedPerm
    rw [erasePoint_apply_of_ne _ _ _ (by simp) (by rw [hfirst]; simp), hfirst]
  have hi := restrictLeft_inl_apply _
    (erasedPerm_fixed G u v hne hmiss r.toRotationSystem) d
  change Sum.inl ((deleteAddedEdge G u v hne hmiss r).σ d) = _ at hi
  exact Sum.inl.inj (hi.trans he)

/-- The reverse rotation step is unchanged whenever its endpoints survive. -/
theorem deleteAddedEdge_sigma_symm (r : SignedRotation (G ⊔ edge u v)) (d e : G.Dart)
    (h : r.σ.symm (augmentedDart G u v hne (Sum.inl d)) =
      augmentedDart G u v hne (Sum.inl e)) :
    (deleteAddedEdge G u v hne hmiss r).σ.symm d = e := by
  apply (deleteAddedEdge G u v hne hmiss r).σ.injective
  rw [Equiv.apply_symm_apply]
  symm
  apply deleteAddedEdge_sigma
  rw [← h, Equiv.apply_symm_apply]

/-- Every original corner whose two flags survive is still the same corner. -/
theorem deleteAddedEdge_corner (r : SignedRotation (G ⊔ edge u v))
    (d e : G.Dart) (b c : Bool)
    (h : r.cornerFlip (augmentedDart G u v hne (Sum.inl d), b) =
      (augmentedDart G u v hne (Sum.inl e), c)) :
    (deleteAddedEdge G u v hne hmiss r).cornerFlip (d, b) = (e, c) := by
  cases b <;> simp only [cornerFlip, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · have hd := deleteAddedEdge_sigma G u v hne hmiss r d e (congrArg Prod.fst h)
    exact Prod.ext hd (congrArg (fun z : Flag (G ⊔ edge u v) => z.2) h)
  · have hd := deleteAddedEdge_sigma_symm G u v hne hmiss r d e (congrArg Prod.fst h)
    exact Prod.ext hd (congrArg (fun z : Flag (G ⊔ edge u v) => z.2) h)

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.deleteAddedEdge_sigma
#print axioms SimpleGraph.SignedRotation.deleteAddedEdge_sigma_symm
#print axioms SimpleGraph.SignedRotation.deleteAddedEdge_corner
