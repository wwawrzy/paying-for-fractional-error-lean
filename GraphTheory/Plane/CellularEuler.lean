import GraphTheory.Faces.FaceBoundaryAlgebra

/-!
# Euler inequality for arbitrary faithful cellular maps

No planar embedding is assumed. The face-boundary kernel has dimension one
and its image lies in the cycle space; rank-nullity therefore proves the
Euler inequality. In particular every faithful rotation of an edgeful tree
is already a sphere map, providing an actual base for embedding constructions.
-/

namespace PlaneTopology.CellularEuler

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open PlaneTopology.Faces.FaceBoundaryAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Rank-nullity counts the faces of any connected faithful cellular map,
not only a spherical one. -/
theorem finrank_range_add_one_eq_numFaces (M : ConnectedCellularMap G) :
    Module.finrank (ZMod 2)
      (LinearMap.range (faceBoundary M.rotation.toRotationSystem)) + 1 =
      M.rotation.toRotationSystem.numFaces := by
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (faceBoundary M.rotation.toRotationSystem)
  have hdomain : Module.finrank (ZMod 2)
      (FaceChain M.rotation.toRotationSystem) =
      Fintype.card (FaceIndex M.rotation.toRotationSystem) := Module.finrank_pi (ZMod 2)
  rw [hdomain, finrank_ker_faceBoundary_eq_one M, card_faceIndex_eq_numFaces] at hrank
  exact hrank

/-- Every connected edgeful cellular map has at least one actual face. -/
theorem one_le_numFaces (M : ConnectedCellularMap G) :
    1 ≤ M.rotation.toRotationSystem.numFaces := by
  have h := finrank_range_add_one_eq_numFaces M
  omega

omit [DecidableEq V] in
/-- The graph-theoretic connectedness bound, in the exact finite notation
used by the Euler equation. -/
theorem vertices_le_edges_add_one (M : ConnectedCellularMap G) :
    Fintype.card V ≤ G.edgeFinset.card + 1 := by
  have h := M.connected.card_vert_le_card_edgeSet_add_one
  simpa only [Nat.card_eq_fintype_card, ← G.edgeFinset_card] using h

/-- The Euler characteristic of an arbitrary connected faithful cellular
map is at most two. This is proved, not built into the input structure. -/
theorem euler_le (M : ConnectedCellularMap G) :
    Fintype.card V + M.rotation.toRotationSystem.numFaces ≤ G.edgeFinset.card + 2 := by
  have hrange := finrank_range_add_one_eq_numFaces M
  have hle := Submodule.finrank_mono
    (range_faceBoundary_le_cycleSpace M.rotation.toRotationSystem)
  have hcycle := G.finrank_cycleSpace_eq_edges_add_one_sub_vertices M.connected
  have hcard := vertices_le_edges_add_one M
  omega

/-- Equality in Euler is equivalent to the actual face boundaries spanning
all graph cycles; no sphere map is assumed in this direction. -/
theorem euler_eq_iff_faceBoundary_spans (M : ConnectedCellularMap G) :
    (Fintype.card V + M.rotation.toRotationSystem.numFaces = G.edgeFinset.card + 2) ↔
      LinearMap.range (faceBoundary M.rotation.toRotationSystem) = G.CycleSpace := by
  have hrange := finrank_range_add_one_eq_numFaces M
  have hcycle := G.finrank_cycleSpace_eq_edges_add_one_sub_vertices M.connected
  have hcard := vertices_le_edges_add_one M
  constructor
  · intro heuler
    apply Submodule.eq_of_le_of_finrank_eq
      (range_faceBoundary_le_cycleSpace M.rotation.toRotationSystem)
    omega
  · intro hspan
    rw [hspan] at hrange
    omega

/-- Every faithful cellular embedding of a finite tree has exactly one
face. This is a property of the constructed rotation, not an assumed Euler law. -/
theorem numFaces_eq_one_of_isTree (M : ConnectedCellularMap G) (hG : G.IsTree) :
    M.rotation.toRotationSystem.numFaces = 1 := by
  have hEuler := euler_le M
  have hpos := one_le_numFaces M
  have htree := hG.card_edgeFinset
  have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr M.connected.nonempty
  omega

/-- Constructing a sphere map from ANY faithful rotation of a tree.
The Euler field is now a theorem and requires no planar axiom. -/
def treePlaneMap (M : ConnectedCellularMap G) (hG : G.IsTree) : ConnectedPlaneMap G where
  toConnectedCellularMap := M
  euler := by
    have hfaces := numFaces_eq_one_of_isTree M hG
    have htree := hG.card_edgeFinset
    have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr M.connected.nonempty
    omega

#print axioms euler_le
#print axioms euler_eq_iff_faceBoundary_spans
#print axioms treePlaneMap

end PlaneTopology.CellularEuler
