import GraphTheory.Plane.PlaneMapTransport

/-!
# General transport of connected plane maps

No triangularity assumption is used.  The dart bijection induces an actual
bijection on face-cycle indices, so it preserves the number of faces and the
Euler equation of an arbitrary connected sphere map.
-/

namespace PlaneTopology.PlaneGeneralTransport

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open PlaneTopology.PlaneMapTransport

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Every nonnegative face-permutation power intertwines dart transport. -/
theorem rotationMap_face_pow_apply (e : G ≃g H) (r : G.RotationSystem)
    (d : G.Dart) (n : ℕ) :
    ((rotationMap e r).facePerm ^ n) (dartEquiv e d) =
      dartEquiv e ((r.facePerm ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply,
      rotationMap_face_apply]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableEq W] in
/-- Two darts share a face exactly when their transported darts share a face. -/
theorem rotationMap_sameFace_iff (e : G ≃g H) (r : G.RotationSystem)
    (d f : G.Dart) :
    (rotationMap e r).SameFace (dartEquiv e d) (dartEquiv e f) ↔ r.SameFace d f := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply (dartEquiv e).injective
    rw [← rotationMap_face_pow_apply]
    exact hn
  · intro h
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, rotationMap_face_pow_apply, hn]

/-- Map a face index by transporting a representative dart of that face. -/
noncomputable def faceIndexMap (e : G ≃g H) (r : G.RotationSystem)
    (F : FaceIndex r) : FaceIndex (rotationMap e r) :=
  faceIndex (rotationMap e r) (dartEquiv e (faceRepresentative r F))

/-- Face-index transport agrees with transport of every dart in the face. -/
theorem faceIndexMap_apply (e : G ≃g H) (r : G.RotationSystem) (d : G.Dart) :
    faceIndexMap e r (faceIndex r d) = faceIndex (rotationMap e r) (dartEquiv e d) := by
  apply (faceIndex_eq_iff_sameFace (rotationMap e r) _ _).mpr
  apply (rotationMap_sameFace_iff e r _ _).mpr
  apply (faceIndex_eq_iff_sameFace r _ _).mp
  exact faceIndex_representative r (faceIndex r d)

/-- Distinct original faces cannot be identified by an isomorphism. -/
theorem faceIndexMap_injective (e : G ≃g H) (r : G.RotationSystem) :
    Function.Injective (faceIndexMap e r) := by
  intro F J h
  have hface := (faceIndex_eq_iff_sameFace (rotationMap e r) _ _).mp h
  have hsource := (rotationMap_sameFace_iff e r _ _).mp hface
  have hindex := (faceIndex_eq_iff_sameFace r _ _).mpr hsource
  simpa only [faceIndex_representative] using hindex

/-- Every transported face contains an image of an original dart. -/
theorem faceIndexMap_surjective (e : G ≃g H) (r : G.RotationSystem) :
    Function.Surjective (faceIndexMap e r) := by
  intro F
  refine ⟨faceIndex r ((dartEquiv e).symm (faceRepresentative (rotationMap e r) F)), ?_⟩
  rw [faceIndexMap_apply, Equiv.apply_symm_apply, faceIndex_representative]

/-- An actual equivalence between the face-cycle index types. -/
noncomputable def faceIndexEquiv (e : G ≃g H) (r : G.RotationSystem) :
    FaceIndex r ≃ FaceIndex (rotationMap e r) :=
  Equiv.ofBijective (faceIndexMap e r)
    ⟨faceIndexMap_injective e r, faceIndexMap_surjective e r⟩

/-- Arbitrary rotations preserve their number of faces under graph isomorphism. -/
theorem rotationMap_numFaces (e : G ≃g H) (r : G.RotationSystem) :
    (rotationMap e r).numFaces = r.numFaces := by
  have h := Fintype.card_congr (faceIndexEquiv e r)
  simpa only [card_faceIndex_eq_numFaces] using h.symm

/-- The Euler equality is invariant under arbitrary rotation transport. -/
theorem rotationMap_isPlanarEmbedding_iff (e : G ≃g H) (r : G.RotationSystem) :
    (rotationMap e r).IsPlanarEmbedding ↔ r.IsPlanarEmbedding := by
  unfold SimpleGraph.RotationSystem.IsPlanarEmbedding
  rw [rotationMap_numFaces, ← Fintype.card_congr e.toEquiv, ← card_edges_eq e]

/-- Transport of an arbitrary actual connected sphere map, with no face-size
assumption. -/
def planeMap (e : G ≃g H) (M : ConnectedPlaneMap G) : ConnectedPlaneMap H where
  rotation := faithfulRotationMap e M.rotation
  connected := e.connected_iff.mp M.connected
  dartNonempty := M.dartNonempty.map (dartEquiv e)
  euler := by
    change (rotationMap e M.rawRotation).IsPlanarEmbedding
    exact (rotationMap_isPlanarEmbedding_iff e M.rawRotation).mpr M.euler

/-- The transported map uses exactly the transported raw rotation. -/
theorem planeMap_rawRotation (e : G ≃g H) (M : ConnectedPlaneMap G) :
    (planeMap e M).rawRotation = rotationMap e M.rawRotation := rfl

#print axioms faceIndexEquiv
#print axioms rotationMap_numFaces
#print axioms planeMap

end PlaneTopology.PlaneGeneralTransport
