import GraphTheory.Surfaces.SignedRotation
import GraphTheory.Plane.PlaneEdgeDeletion

/-! Actual edge deletion for signed rotations. Vertex cycles bypass the deleted
edge, and every surviving edge retains its sign. Genus monotonicity is a
separate obligation and is not assumed by this construction. -/

namespace SimpleGraph.SignedRotation

open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion

variable {V : Type*} {G : SimpleGraph V}

/-- Forget edge signs, retaining the single-cycle condition at every vertex. -/
def faithfulRotation (r : SignedRotation G) : FaithfulRotationSystem G where
  toRotationSystem := r.toRotationSystem
  vertexCyclic := by
    apply PlaneTopology.Faces.FaithfulPlaneMap.RotationSystem.isVertexCyclic_of_pairwise_sameCycle
    intro v d hd e he
    exact r.cyclic d e (hd.trans he.symm)

variable (G) (u v : V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- Delete the added edge from the actual signed rotation. -/
noncomputable def deleteAddedEdge (r : SignedRotation (G ⊔ edge u v)) :
    SignedRotation G where
  toRotationSystem := deletedRotation G u v hne hmiss r.toRotationSystem
  cyclic d e h := (deletedFaithfulRotation G u v hne hmiss r.faithfulRotation).sameCycle_at_source h
  twist d := r.twist (augmentedDart G u v hne (Sum.inl d))
  twist_symm d := by
    change r.twist (augmentedDart G u v hne (Sum.inl d)).symm = _
    exact r.twist_symm _

/-- Deletion changes no sign on an edge that survives. -/
theorem deleteAddedEdge_twist (r : SignedRotation (G ⊔ edge u v)) (d : G.Dart) :
    (deleteAddedEdge G u v hne hmiss r).twist d =
      r.twist (augmentedDart G u v hne (Sum.inl d)) := rfl

/-- The inclusion of surviving flags commutes with the signed edge involution. -/
theorem deleteAddedEdge_edgeFlip (r : SignedRotation (G ⊔ edge u v)) (x : Flag G) :
    (augmentedDart G u v hne (Sum.inl ((deleteAddedEdge G u v hne hmiss r).edgeFlip x).1),
      ((deleteAddedEdge G u v hne hmiss r).edgeFlip x).2) =
    r.edgeFlip (augmentedDart G u v hne (Sum.inl x.1), x.2) := by
  rfl

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.faithfulRotation
#print axioms SimpleGraph.SignedRotation.deleteAddedEdge
#print axioms SimpleGraph.SignedRotation.deleteAddedEdge_edgeFlip
