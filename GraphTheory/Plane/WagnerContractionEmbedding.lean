import GraphTheory.Plane.WagnerResidualEmbedding
import GraphTheory.Plane.PlaneVertexDeletion

/-!
# Actual reconstruction across a three-connected edge contraction

Delete the contracted apex from the inductively supplied plane map,
transport the resulting single exposed face through the exact residual
isomorphism, and reconstruct the original two adjacent apices by the
forbidden-minor gap and actual fan surgery.
-/

namespace PlaneTopology.WagnerContractionEmbedding

open SimpleGraph SimpleGraph.EdgeContraction PlaneTopology.Faces.FaithfulPlaneMap
  PlaneTopology.WagnerContractionGraph PlaneTopology.WagnerTwoFanGraph PlaneTopology.WagnerResidualEmbedding
  PlaneTopology.PlaneMapTransport PlaneTopology.PlaneGeneralTransport PlaneTopology.PlaneVertexDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)

/-- Deleting the contracted apex exposes one actual residual face containing
every original neighbor of either endpoint. -/
theorem exists_residual_face_of_contracted_map
    (hcontr : (contrGraph G u v).IsKConnected 3)
    (M : ConnectedPlaneMap (contrGraph G u v)) :
    ∃ N : ConnectedPlaneMap (residualGraph G u v),
      ∃ base : (residualGraph G u v).Dart,
        ∀ w : ResidualVertex u v, G.Adj u w.val ∨ G.Adj v w.val →
          ∃ d : (residualGraph G u v).Dart,
            d.fst = w ∧ N.rawRotation.SameFace base d := by
  classical
  let e := residualIso G u v
  have hR2 := residual_isKConnected_two G u v hcontr
  have hQ2 := (e.isKConnected_iff 2).mp hR2
  let H := (contrGraph G u v).induce {q | q ≠ contrMk u v u}
  haveI : Nontrivial ↥({q : ContrVertex u v | q ≠ contrMk u v u} : Set (ContrVertex u v)) :=
    hQ2.two_nontrivial
  have hQ1 : H.IsKConnected 1 := le_trans (by decide : 1 ≤ 2) hQ2
  have hconn : H.Connected :=
    ((isVertexConnected_one_iff H).mp (hQ1.isVertexConnected H)).2
  have hD : Nonempty H.Dart := by
    let q : ↥({q : ContrVertex u v | q ≠ contrMk u v u} : Set (ContrVertex u v)) :=
      Classical.arbitrary _
    obtain ⟨w, hw⟩ := hconn.preconnected.exists_adj_of_nontrivial q
    exact ⟨⟨⟨q, w⟩, hw⟩⟩
  obtain ⟨N, base, hface⟩ := exists_deleteVertexPlaneMap (contrGraph G u v)
    (contrMk u v u) M hconn hD
  refine ⟨planeMap e.symm N, dartEquiv e.symm base, ?_⟩
  intro w hw
  have hadj : (contrGraph G u v).Adj (contrMk u v u) (e w).val :=
    (contracted_apex_adj_iff G u v w).mpr hw
  obtain ⟨d, hd, hbd⟩ := hface (e w) hadj
  refine ⟨dartEquiv e.symm d, ?_, ?_⟩
  · change e.symm d.fst = w
    rw [hd]
    exact e.symm_apply_apply w
  · exact (rotationMap_sameFace_iff e.symm N.rawRotation base d).mpr hbd

/-- The complete actual reverse-contraction step. The map of the smaller
three-connected contraction is the sole inductive input. -/
theorem exists_planeMap_of_contracted_map (hG : G.IsPlanar) (h3 : G.IsKConnected 3)
    (huv : G.Adj u v) (hcontr : (contrGraph G u v).IsKConnected 3)
    (M : ConnectedPlaneMap (contrGraph G u v)) : Nonempty (ConnectedPlaneMap G) := by
  obtain ⟨N, base, hface⟩ := exists_residual_face_of_contracted_map G u v hcontr M
  apply exists_planeMap_of_residual_face G u v hG h3 huv N
    (residual_isKConnected_two G u v hcontr) base
  · intro w hw
    exact hface w (Or.inl ((mem_firstNeighbors G u v w).mp hw))
  · intro w hw
    exact hface w (Or.inr ((mem_secondNeighbors G u v w).mp hw))

#print axioms exists_residual_face_of_contracted_map
#print axioms exists_planeMap_of_contracted_map

end PlaneTopology.WagnerContractionEmbedding
