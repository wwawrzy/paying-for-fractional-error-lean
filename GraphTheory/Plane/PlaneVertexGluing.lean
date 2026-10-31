import GraphTheory.Plane.PlaneVertexGluingGraph
import GraphTheory.Plane.PlaneEdgeGluingPermutation
import GraphTheory.Plane.PlaneLeafInsertion
import GraphTheory.Plane.PlaneGeneralTransport

/-! # Actual connected plane maps glued at one common vertex -/

namespace PlaneTopology.PlaneVertexGluing

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneVertexGluingGraph PlaneTopology.PlanePermutationSurgery PlaneTopology.PlaneChordCountBound
open PlaneTopology.PlaneEdgeGluingPermutation

/-- Opposite summands of a permutation sum cannot share an orbit. -/
theorem not_sameCycle_sumCongr {α β : Type*} [Finite α] [Finite β]
    (p : Perm α) (q : Perm β) (a : α) (b : β) :
    ¬ Equiv.Perm.SameCycle (Equiv.sumCongr p q) (Sum.inl a) (Sum.inr b) := by
  intro h
  have heq := sameCycle_label (Equiv.sumCongr p q) Sum.isLeft
    (fun x => by cases x <;> rfl) h
  cases heq

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (L : SimpleGraph (Option A)) (R : SimpleGraph (Option B))
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

/-- Join the two cycles at the common vertex by one transposition. -/
def splicedVertexPerm (r : L.RotationSystem) (s : R.RotationSystem)
    (d : L.Dart) (e : R.Dart) : Perm (L.Dart ⊕ R.Dart) :=
  swap (Sum.inl d) (Sum.inr e) * Equiv.sumCongr r.σ s.σ

omit [Fintype A] [Fintype B] [DecidableRel L.Adj] [DecidableRel R.Adj] in
/-- The splice preserves every actual source label in the union graph. -/
theorem splicedVertexPerm_source (r : L.RotationSystem) (s : R.RotationSystem)
    (d : L.Dart) (e : R.Dart) (hd : d.fst = none) (he : e.fst = none)
    (x : L.Dart ⊕ R.Dart) :
    (gluedDart L R (splicedVertexPerm L R r s d e x)).fst = (gluedDart L R x).fst := by
  let f := fun z : L.Dart ⊕ R.Dart => (gluedDart L R z).fst
  have hde : f (Sum.inl d) = f (Sum.inr e) := by
    change leftVertex d.fst = rightVertex e.fst
    rw [hd, he]
    rfl
  change f (splicedVertexPerm L R r s d e x) = f x
  rw [splicedVertexPerm, mul_apply, map_swap_eq f _ _ _ hde]
  cases x with
  | inl x => exact congrArg leftVertex (r.σ_source x)
  | inr x => exact congrArg rightVertex (s.σ_source x)

/-- Every actual source still has precisely one vertex cycle after gluing. -/
theorem splicedVertexPerm_sameCycle_at_source
    (P : FaithfulRotationSystem L) (Q : FaithfulRotationSystem R)
    (d : L.Dart) (e : R.Dart) (hd : d.fst = none) (he : e.fst = none)
    (x y : L.Dart ⊕ R.Dart) (hxy : (gluedDart L R x).fst = (gluedDart L R y).fst) :
    (splicedVertexPerm L R P.toRotationSystem Q.toRotationSystem d e).SameCycle x y := by
  let p := Equiv.sumCongr P.toRotationSystem.σ Q.toRotationSystem.σ
  have hnot := not_sameCycle_sumCongr P.toRotationSystem.σ Q.toRotationSystem.σ d e
  have hj : (splicedVertexPerm L R P.toRotationSystem Q.toRotationSystem d e).SameCycle
      (Sum.inl d) (Sum.inr e) := sameCycle_swap_mul_of_not_sameCycle p _ _ hnot
  have hl (a b : L.Dart) (hab : a.fst = b.fst) :
      (splicedVertexPerm L R P.toRotationSystem Q.toRotationSystem d e).SameCycle
        (Sum.inl a) (Sum.inl b) :=
    sameCycle_swap_mul_preserved p _ _ hnot
      (sameCycle_map P.toRotationSystem.σ p Sum.inl (fun _ => rfl) (P.sameCycle_at_source hab))
  have hr (a b : R.Dart) (hab : a.fst = b.fst) :
      (splicedVertexPerm L R P.toRotationSystem Q.toRotationSystem d e).SameCycle
        (Sum.inr a) (Sum.inr b) :=
    sameCycle_swap_mul_preserved p _ _ hnot
      (sameCycle_map Q.toRotationSystem.σ p Sum.inr (fun _ => rfl) (Q.sameCycle_at_source hab))
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hl x y (leftVertex_injective hxy)
    | inr y =>
      have h := (leftVertex_eq_rightVertex_iff x.fst y.fst).mp hxy
      exact (hl x d (h.1.trans hd.symm)).trans (hj.trans (hr e y (he.trans h.2.symm)))
  | inr x =>
    cases y with
    | inl y =>
      have h := (leftVertex_eq_rightVertex_iff y.fst x.fst).mp hxy.symm
      exact (hr x e (h.2.trans he.symm)).trans (hj.symm.trans (hl d y (hd.trans h.1.symm)))
    | inr y => exact hr x y (rightVertex_injective hxy)

/-- Actual source-preserving rotation on the exact union graph. -/
noncomputable def gluedRotation (r : L.RotationSystem) (s : R.RotationSystem)
    (d : L.Dart) (e : R.Dart) (hd : d.fst = none) (he : e.fst = none) :
    (gluedGraph L R).RotationSystem where
  σ := (gluedDartEquiv L R).permCongr (splicedVertexPerm L R r s d e)
  σ_source x := by
    obtain ⟨z, rfl⟩ := (gluedDartEquiv L R).surjective x
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact splicedVertexPerm_source L R r s d e hd he z

/-- Genuine faithful rotation of the point-glued graph. -/
noncomputable def gluedFaithfulRotation (P : FaithfulRotationSystem L) (Q : FaithfulRotationSystem R)
    (d : L.Dart) (e : R.Dart) (hd : d.fst = none) (he : e.fst = none) :
    FaithfulRotationSystem (gluedGraph L R) where
  toRotationSystem := gluedRotation L R P.toRotationSystem Q.toRotationSystem d e hd he
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro w a ha b hb
    obtain ⟨x, rfl⟩ := (gluedDartEquiv L R).surjective a
    obtain ⟨y, rfl⟩ := (gluedDartEquiv L R).surjective b
    apply sameCycle_map (splicedVertexPerm L R P.toRotationSystem Q.toRotationSystem d e)
      _ (gluedDartEquiv L R) (fun z => by simp [gluedRotation])
    exact splicedVertexPerm_sameCycle_at_source L R P Q d e hd he x y (ha.trans hb.symm)

/-- The same splice merges one face from each disjoint original map. -/
def splicedFacePerm (r : L.RotationSystem) (s : R.RotationSystem)
    (d : L.Dart) (e : R.Dart) : Perm (L.Dart ⊕ R.Dart) :=
  swap (Sum.inl d) (Sum.inr e) * Equiv.sumCongr r.facePerm s.facePerm

omit [Fintype A] [Fintype B] [DecidableRel L.Adj] [DecidableRel R.Adj] in
/-- The computed splice is exactly the actual facial permutation. -/
theorem gluedRotation_facePerm (r : L.RotationSystem) (s : R.RotationSystem)
    (d : L.Dart) (e : R.Dart) (hd : d.fst = none) (he : e.fst = none) :
    (gluedRotation L R r s d e hd he).facePerm =
      (gluedDartEquiv L R).permCongr (splicedFacePerm L R r s d e) := by
  apply Equiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (gluedDartEquiv L R).surjective x
  rw [RotationSystem.facePerm_apply]
  have hz : (gluedDartEquiv L R z).symm = gluedDartEquiv L R (gluedReversal L R z) :=
    (gluedDart_reversal L R z).symm
  rw [hz]
  change (gluedDartEquiv L R).permCongr (splicedVertexPerm L R r s d e)
    (gluedDartEquiv L R (gluedReversal L R z)) =
      (gluedDartEquiv L R).permCongr (splicedFacePerm L R r s d e) (gluedDartEquiv L R z)
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  congr 1
  cases z <;> rfl

/-- Point gluing merges exactly two old faces into one new face. -/
theorem gluedRotation_numFaces (r : L.RotationSystem) (s : R.RotationSystem)
    (d : L.Dart) (e : R.Dart) (hd : d.fst = none) (he : e.fst = none) :
    (gluedRotation L R r s d e hd he).numFaces + 1 = r.numFaces + s.numFaces := by
  rw [PlaneTopology.PlaneLeafInsertion.numFaces_eq_cycleType_card,
    PlaneTopology.PlaneLeafInsertion.numFaces_eq_cycleType_card,
    PlaneTopology.PlaneLeafInsertion.numFaces_eq_cycleType_card,
    gluedRotation_facePerm, cycleType_permCongr]
  have h := cycleType_card_swap_mul_of_not_sameCycle
    (Equiv.sumCongr r.facePerm s.facePerm) (Sum.inl d) (Sum.inr e)
    (not_sameCycle_sumCongr r.facePerm s.facePerm d e)
    (by intro h; exact r.facePerm_ne_self d (Sum.inl.inj h))
    (by intro h; exact s.facePerm_ne_self e (Sum.inr.inj h))
  rw [cycleType_sumCongr, Multiset.card_add] at h
  exact h

/-- Actual connected plane map obtained by gluing two maps at chosen common
vertex corners. Every input edge is present exactly once. -/
noncomputable def gluedPlaneMapAt (M : ConnectedPlaneMap L) (N : ConnectedPlaneMap R)
    (d : L.Dart) (e : R.Dart) (hd : d.fst = none) (he : e.fst = none) :
    ConnectedPlaneMap (gluedGraph L R) where
  rotation := gluedFaithfulRotation L R M.rotation N.rotation d e hd he
  connected := gluedGraph_connected L R M.connected N.connected
  dartNonempty := ⟨gluedDart L R (Sum.inl d)⟩
  euler := by
    have hL := M.euler
    have hR := N.euler
    have hV := card_glued_vertices (A := A) (B := B)
    have hE := card_glued_edges L R
    have hF := gluedRotation_numFaces L R M.rawRotation N.rawRotation d e hd he
    change Fintype.card (Option (A ⊕ B)) +
      (gluedRotation L R M.rawRotation N.rawRotation d e hd he).numFaces = _
    change Fintype.card (Option A) + M.rawRotation.numFaces = _ at hL
    change Fintype.card (Option B) + N.rawRotation.numFaces = _ at hR
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hL hR hV hE ⊢
    omega

/-- Glue any two actual connected plane maps at their distinguished vertices. -/
noncomputable def gluedPlaneMap (M : ConnectedPlaneMap L) (N : ConnectedPlaneMap R) :
    ConnectedPlaneMap (gluedGraph L R) :=
  gluedPlaneMapAt L R M N
    (PlaneTopology.PlaneLeafInsertion.exists_dart_at_vertex L none M).choose
    (PlaneTopology.PlaneLeafInsertion.exists_dart_at_vertex R none N).choose
    (PlaneTopology.PlaneLeafInsertion.exists_dart_at_vertex L none M).choose_spec
    (PlaneTopology.PlaneLeafInsertion.exists_dart_at_vertex R none N).choose_spec

/-- A singleton left component requires no impossible empty-dart plane map. -/
noncomputable def rightSingletonPlaneMap [IsEmpty A] (N : ConnectedPlaneMap R) :
    ConnectedPlaneMap (gluedGraph L R) :=
  PlaneTopology.PlaneGeneralTransport.planeMap (rightIsoOfIsEmpty L R) N

/-- The analogous singleton right-component case. -/
noncomputable def leftSingletonPlaneMap [IsEmpty B] (M : ConnectedPlaneMap L) :
    ConnectedPlaneMap (gluedGraph L R) :=
  PlaneTopology.PlaneGeneralTransport.planeMap (leftIsoOfIsEmpty L R) M

end PlaneTopology.PlaneVertexGluing

#print axioms PlaneTopology.PlaneVertexGluing.gluedPlaneMap
#print axioms PlaneTopology.PlaneVertexGluing.rightSingletonPlaneMap
