import GraphTheory.Plane.PlaneSmallBases

/-!
# Transport of actual triangular plane maps along graph isomorphisms

The vertex and face permutations are transported on actual darts.  For
triangular maps, the face count is transported using the exact
three-darts-per-face identity.
-/

namespace PlaneTopology.PlaneMapTransport

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open TriangularFaces

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The bijection on directed edges induced by a graph isomorphism. -/
def dartEquiv (e : G ≃g H) : G.Dart ≃ H.Dart where
  toFun := e.toHom.mapDart
  invFun := e.symm.toHom.mapDart
  left_inv d := by apply Dart.ext; ext <;> simp
  right_inv d := by apply Dart.ext; ext <;> simp

/-- Dart transport commutes with edge reversal. -/
theorem dartEquiv_symm (e : G ≃g H) (d : G.Dart) :
    dartEquiv e d.symm = (dartEquiv e d).symm := rfl

/-- Transport of the raw source-preserving vertex permutation. -/
def rotationMap (e : G ≃g H) (r : G.RotationSystem) : H.RotationSystem where
  σ := (dartEquiv e).permCongr r.σ
  σ_source d := by
    change e (r.σ ((dartEquiv e).symm d)).fst = d.fst
    rw [r.σ_source]
    exact e.apply_symm_apply d.fst

/-- The transported vertex rotation intertwines the dart bijection. -/
theorem rotationMap_apply (e : G ≃g H) (r : G.RotationSystem) (d : G.Dart) :
    (rotationMap e r).σ (dartEquiv e d) = dartEquiv e (r.σ d) := by
  simp [rotationMap]

/-- Every nonnegative power is transported on actual darts. -/
theorem rotationMap_pow_apply (e : G ≃g H) (r : G.RotationSystem)
    (d : G.Dart) (n : ℕ) :
    ((rotationMap e r).σ ^ n) (dartEquiv e d) = dartEquiv e ((r.σ ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply,
      rotationMap_apply]

/-- The face permutation is transported, because dart reversal is natural. -/
theorem rotationMap_face_apply (e : G ≃g H) (r : G.RotationSystem) (d : G.Dart) :
    (rotationMap e r).facePerm (dartEquiv e d) = dartEquiv e (r.facePerm d) := by
  rw [SimpleGraph.RotationSystem.facePerm_apply, ← dartEquiv_symm, rotationMap_apply,
    SimpleGraph.RotationSystem.facePerm_apply]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

/-- Faithfulness is invariant under graph isomorphism. -/
def faithfulRotationMap (e : G ≃g H) (r : FaithfulRotationSystem G) :
    FaithfulRotationSystem H where
  toRotationSystem := rotationMap e r.toRotationSystem
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro v d hd f hf
    obtain ⟨d, rfl⟩ := (dartEquiv e).surjective d
    obtain ⟨f, rfl⟩ := (dartEquiv e).surjective f
    have hsource : d.fst = f.fst := e.injective (hd.trans hf.symm)
    obtain ⟨n, hn⟩ := (r.sameCycle_at_source hsource).exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, rotationMap_pow_apply, hn]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
/-- Triangular faces are invariant under graph isomorphism. -/
theorem rotationMap_triangular (e : G ≃g H) (r : G.RotationSystem)
    (htri : Triangular r) : Triangular (rotationMap e r) := by
  intro d
  obtain ⟨d, rfl⟩ := (dartEquiv e).surjective d
  rw [rotationMap_face_apply, rotationMap_face_apply, rotationMap_face_apply, htri]

omit [DecidableEq V] [DecidableEq W] in
/-- The edge count is invariant under graph isomorphism. -/
theorem card_edges_eq (e : G ≃g H) : G.edgeFinset.card = H.edgeFinset.card := by
  have h := Fintype.card_congr (dartEquiv e)
  rw [G.dart_card_eq_twice_card_edges, H.dart_card_eq_twice_card_edges] at h
  omega

/-- The face count of a triangular rotation is invariant under transport. -/
theorem rotationMap_numFaces (e : G ≃g H) (r : G.RotationSystem)
    (htri : Triangular r) : (rotationMap e r).numFaces = r.numFaces := by
  have hG := TriangularFaces.sum_face_weights_over_darts r htri (fun _ => 1)
  have hH := TriangularFaces.sum_face_weights_over_darts
    (rotationMap e r) (rotationMap_triangular e r htri) (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    card_faceIndex_eq_numFaces] at hG hH
  have hc := Fintype.card_congr (dartEquiv e)
  omega

/-- Transport of a genuine connected triangular sphere map. -/
def triangularPlaneMap (e : G ≃g H) (M : ConnectedPlaneMap G)
    (htri : Triangular M.rawRotation) : ConnectedPlaneMap H where
  rotation := faithfulRotationMap e M.rotation
  connected := e.connected_iff.mp M.connected
  dartNonempty := M.dartNonempty.map (dartEquiv e)
  euler := by
    change Fintype.card W + (rotationMap e M.rawRotation).numFaces = _
    rw [rotationMap_numFaces e M.rawRotation htri, ← Fintype.card_congr e.toEquiv,
      ← card_edges_eq e]
    exact M.euler

/-- The transported sphere map retains its triangular faces. -/
theorem triangularPlaneMap_triangular (e : G ≃g H) (M : ConnectedPlaneMap G)
    (htri : Triangular M.rawRotation) :
    Triangular (triangularPlaneMap e M htri).rawRotation :=
  rotationMap_triangular e M.rawRotation htri

/-- The triangle sphere map transported to any three-element vertex type. -/
noncomputable def completeGraphPlaneMapOfCardThree (h : Fintype.card V = 3) :
    ConnectedPlaneMap (completeGraph V) :=
  triangularPlaneMap (SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq h).symm)
    PlaneTopology.PlaneSmallBases.trianglePlaneMap PlaneTopology.PlaneSmallBases.triangleRotation_triangular

/-- The transported complete graph on three vertices has triangular faces. -/
theorem completeGraphPlaneMapOfCardThree_triangular (h : Fintype.card V = 3) :
    Triangular (completeGraphPlaneMapOfCardThree h).rawRotation :=
  triangularPlaneMap_triangular
    (SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq h).symm)
    PlaneTopology.PlaneSmallBases.trianglePlaneMap PlaneTopology.PlaneSmallBases.triangleRotation_triangular

/-- The tetrahedral sphere map transported to any four-element vertex type. -/
noncomputable def completeGraphPlaneMapOfCardFour (h : Fintype.card V = 4) :
    ConnectedPlaneMap (completeGraph V) :=
  triangularPlaneMap (SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq h).symm)
    PlaneTopology.PlaneSmallBases.tetrahedronPlaneMap PlaneTopology.PlaneSmallBases.tetrahedronRotation_triangular

/-- The transported complete graph on four vertices has triangular faces. -/
theorem completeGraphPlaneMapOfCardFour_triangular (h : Fintype.card V = 4) :
    Triangular (completeGraphPlaneMapOfCardFour h).rawRotation :=
  triangularPlaneMap_triangular
    (SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq h).symm)
    PlaneTopology.PlaneSmallBases.tetrahedronPlaneMap PlaneTopology.PlaneSmallBases.tetrahedronRotation_triangular

#print axioms triangularPlaneMap
#print axioms triangularPlaneMap_triangular
#print axioms completeGraphPlaneMapOfCardThree
#print axioms completeGraphPlaneMapOfCardFour

end PlaneTopology.PlaneMapTransport
