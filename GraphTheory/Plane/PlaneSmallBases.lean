import GraphTheory.Plane.PlaneRotationExists
import GraphTheory.Plane.TriangularFaces

/-!
# Explicit spherical rotations of the triangle and tetrahedron

Only the finite permutation identities below are discharged by kernel `decide`.
Face counts are deduced from the proved triangular face-incidence identity,
not by evaluating a noncomputable face-count definition.
-/

namespace PlaneTopology.PlaneSmallBases

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open TriangularFaces

/-- A concrete dart in a complete graph. -/
def completeDart {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    (completeGraph (Fin n)).Dart := ⟨(a, b), h⟩

/-- The triangle rotates the two outgoing darts at each vertex by a swap. -/
def trianglePermutation : Equiv.Perm (completeGraph (Fin 3)).Dart :=
  Equiv.swap (completeDart 0 1 (by decide)) (completeDart 0 2 (by decide)) *
  Equiv.swap (completeDart 1 0 (by decide)) (completeDart 1 2 (by decide)) *
  Equiv.swap (completeDart 2 0 (by decide)) (completeDart 2 1 (by decide))

/-- This explicit triangle permutation preserves sources. -/
def triangleRotation : (completeGraph (Fin 3)).RotationSystem where
  σ := trianglePermutation
  σ_source := by decide

/-- All darts at one triangle vertex lie in one rotation cycle. -/
theorem triangleRotation_vertexCyclic :
    PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.IsVertexCyclic triangleRotation := by
  apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
  intro v d hd e he
  have hp : ∀ d e : (completeGraph (Fin 3)).Dart, d.fst = e.fst →
      ∃ n : Fin 2, (trianglePermutation ^ n.val) d = e := by decide
  obtain ⟨n, hn⟩ := hp d e (hd.trans he.symm)
  exact ⟨(n.val : ℤ), by simpa only [zpow_natCast] using hn⟩

/-- The two faces of the triangle both have length three. -/
theorem triangleRotation_triangular : Triangular triangleRotation := by
  unfold Triangular
  decide

/-- A triangular rotation on the triangle has precisely two face orbits. -/
theorem triangleRotation_numFaces : triangleRotation.numFaces = 2 := by
  have h := TriangularFaces.sum_face_weights_over_darts
    triangleRotation triangleRotation_triangular (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    card_faceIndex_eq_numFaces] at h
  have hc : Fintype.card (completeGraph (Fin 3)).Dart = 6 := by decide
  omega

/-- The complete graph on three vertices has three edges. -/
theorem triangle_card_edges : (completeGraph (Fin 3)).edgeFinset.card = 3 := by decide

/-- A genuine connected spherical map for the triangle. -/
def trianglePlaneMap : ConnectedPlaneMap (completeGraph (Fin 3)) where
  rotation := ⟨triangleRotation, triangleRotation_vertexCyclic⟩
  connected := connected_top
  dartNonempty := ⟨completeDart 0 1 (by decide)⟩
  euler := by
    change Fintype.card (Fin 3) + triangleRotation.numFaces = _
    rw [triangleRotation_numFaces, triangle_card_edges]
    decide

/-- The tetrahedron uses opposite cyclic orientations at adjacent vertices. -/
def tetrahedronPermutation : Equiv.Perm (completeGraph (Fin 4)).Dart :=
  [completeDart 0 1 (by decide), completeDart 0 2 (by decide),
    completeDart 0 3 (by decide)].formPerm *
  [completeDart 1 0 (by decide), completeDart 1 3 (by decide),
    completeDart 1 2 (by decide)].formPerm *
  [completeDart 2 0 (by decide), completeDart 2 1 (by decide),
    completeDart 2 3 (by decide)].formPerm *
  [completeDart 3 0 (by decide), completeDart 3 2 (by decide),
    completeDart 3 1 (by decide)].formPerm

/-- The explicit tetrahedral permutation preserves sources. -/
def tetrahedronRotation : (completeGraph (Fin 4)).RotationSystem where
  σ := tetrahedronPermutation
  σ_source := by decide

/-- Every tetrahedral vertex has exactly one rotation cycle. -/
theorem tetrahedronRotation_vertexCyclic :
    PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.IsVertexCyclic tetrahedronRotation := by
  apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
  intro v d hd e he
  have hp : ∀ d e : (completeGraph (Fin 4)).Dart, d.fst = e.fst →
      ∃ n : Fin 3, (tetrahedronPermutation ^ n.val) d = e := by decide
  obtain ⟨n, hn⟩ := hp d e (hd.trans he.symm)
  exact ⟨(n.val : ℤ), by simpa only [zpow_natCast] using hn⟩

set_option maxRecDepth 4096 in
/-- The explicit tetrahedral rotation has triangular faces. -/
theorem tetrahedronRotation_triangular : Triangular tetrahedronRotation := by
  unfold Triangular
  decide

/-- The tetrahedral rotation has exactly four face orbits. -/
theorem tetrahedronRotation_numFaces : tetrahedronRotation.numFaces = 4 := by
  have h := TriangularFaces.sum_face_weights_over_darts
    tetrahedronRotation tetrahedronRotation_triangular (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    card_faceIndex_eq_numFaces] at h
  have hc : Fintype.card (completeGraph (Fin 4)).Dart = 12 := by decide
  omega

/-- The tetrahedron has six edges. -/
theorem tetrahedron_card_edges : (completeGraph (Fin 4)).edgeFinset.card = 6 := by decide

/-- A genuine connected spherical map for the tetrahedron. -/
def tetrahedronPlaneMap : ConnectedPlaneMap (completeGraph (Fin 4)) where
  rotation := ⟨tetrahedronRotation, tetrahedronRotation_vertexCyclic⟩
  connected := connected_top
  dartNonempty := ⟨completeDart 0 1 (by decide)⟩
  euler := by
    change Fintype.card (Fin 4) + tetrahedronRotation.numFaces = _
    rw [tetrahedronRotation_numFaces, tetrahedron_card_edges]
    decide

#print axioms trianglePlaneMap
#print axioms tetrahedronPlaneMap

end PlaneTopology.PlaneSmallBases
