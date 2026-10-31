import GraphTheory.Plane.PlaneEdgeGluingFaces
import GraphTheory.Plane.CellularEuler

/-! # Actual edge gluing of two connected sphere maps -/

noncomputable section

namespace PlaneTopology.PlaneEdgeGluing

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneEdgeGluingGraph PlaneTopology.PlaneEdgeGluingDarts PlaneTopology.PlaneEdgeGluingRestriction
open PlaneTopology.PlaneEdgeGluingFaces

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (L : SimpleGraph (Fin 2 ⊕ A)) (R : SimpleGraph (Fin 2 ⊕ B))
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

/-- The actual glued graph with its constructed faithful cellular rotation. -/
def gluedCellularMap (l : ConnectedCellularMap L) (r : ConnectedCellularMap R)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    ConnectedCellularMap (gluedGraph L R) where
  rotation := gluedFaithfulRotation L R l.rotation r.rotation hL hR
  connected := gluedGraph_connected L R l.connected r.connected
  dartNonempty := ⟨leftDart L R (rightCommonDart L hL false)⟩

/-- **Actual edge gluing of connected sphere maps.** The output graph is
precisely the union of the two graph images, sharing just their common K₂.
Faithfulness comes from permutation splicing and bypassing the duplicate
edge; the exact Euler equation is proved from the face bound and cellular Euler. -/
def gluedPlaneMap (l : ConnectedPlaneMap L) (r : ConnectedPlaneMap R)
    (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    (by classical exact ConnectedPlaneMap (gluedGraph L R)) := by
  classical
  let M := gluedCellularMap L R l.toConnectedCellularMap r.toConnectedCellularMap hL hR
  refine ⟨M, ?_⟩
  have hupper := PlaneTopology.CellularEuler.euler_le M
  have hl := l.euler
  have hr := r.euler
  change Fintype.card (Fin 2 ⊕ A) + l.rawRotation.numFaces = L.edgeFinset.card + 2 at hl
  change Fintype.card (Fin 2 ⊕ B) + r.rawRotation.numFaces = R.edgeFinset.card + 2 at hr
  have hface := old_numFaces_le_glued_add_one L R l.rawRotation r.rawRotation hL hR
  have hvertex := card_glued_vertices (A := A) (B := B)
  have hedge := card_edges_gluedGraph L R hL hR
  change Fintype.card (Fin 2 ⊕ (A ⊕ B)) +
    (gluedRotation L R l.rawRotation r.rawRotation hL hR).numFaces = _
  change Fintype.card (Fin 2 ⊕ (A ⊕ B)) +
    (gluedRotation L R l.rawRotation r.rawRotation hL hR).numFaces ≤ _ at hupper
  omega

#print axioms gluedPlaneMap

end PlaneTopology.PlaneEdgeGluing
