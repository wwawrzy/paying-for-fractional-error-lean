import GraphTheory.Plane.WagnerTwoFanGraph
import GraphTheory.Plane.WagnerAttachment
import GraphTheory.Plane.PlaneFacialCycle
import GraphTheory.Plane.PlaneFaceArc
import GraphTheory.Plane.PlaneGeneralTransport

/-!
# Reconstructing the original graph from a common residual face

The forbidden-minor gap theorem is applied to the entire actual simple
facial cycle in G minus u,v. Its cyclic gap supplies actual two-fan surgery;
the exact graph isomorphism then transports this map to the original G.
-/

namespace PlaneTopology.WagnerResidualEmbedding

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.WagnerContractionGraph
  PlaneTopology.WagnerTwoFanGraph PlaneTopology.WagnerAttachment PlaneTopology.PlaneFacialCycle
  PlaneTopology.PlaneFaceArc PlaneTopology.CyclicAttachment PlaneTopology.PlaneTwoFans

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each distinct cofacial attachment has a position on the entire actual
boundary, so the position set has at least as many elements. -/
theorem card_le_facePositions {H : SimpleGraph V} [DecidableRel H.Adj]
    (r : H.RotationSystem) (base : H.Dart) (X : Finset V)
    (hX : ∀ x ∈ X, ∃ e : H.Dart, e.fst = x ∧ r.SameFace base e) :
    X.card ≤ (facePositions r base X).card := by
  apply Finset.card_le_card_of_surjOn (r.faceBoundaryWalk base).getVert
  intro x hx
  obtain ⟨e, he, hface⟩ := hX x hx
  obtain ⟨i, hi, hie⟩ := exists_position_of_sameFace r base e hface
  have hix := hie.trans he
  exact ⟨i, (mem_facePositions r base X i).mpr ⟨hi, hix ▸ hx⟩, hix⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)

/-- The literal inclusion of the residual induced graph into the original graph. -/
def residualHom : residualGraph G u v →g G where
  toFun := Subtype.val
  map_rel' h := h

/-- The whole facial cycle of the residual graph, viewed in the original graph. -/
noncomputable def residualBoundary (M : ConnectedPlaneMap (residualGraph G u v))
    (base : (residualGraph G u v).Dart) : G.Walk base.fst.val base.fst.val :=
  (M.rawRotation.faceBoundaryWalk base).map (residualHom G u v)

/-- Two-connectivity makes the whole residual boundary an actual simple cycle in G. -/
theorem residualBoundary_isCycle (M : ConnectedPlaneMap (residualGraph G u v))
    (htwo : (residualGraph G u v).IsKConnected 2)
    (base : (residualGraph G u v).Dart) : (residualBoundary G u v M base).IsCycle := by
  exact (faceBoundaryWalk_isCycle M htwo base).map Subtype.val_injective

/-- The first deleted endpoint cannot occur on a cycle consisting of residual vertices. -/
theorem first_not_mem_residualBoundary (M : ConnectedPlaneMap (residualGraph G u v))
    (base : (residualGraph G u v).Dart) : u ∉ (residualBoundary G u v M base).support := by
  intro h
  rw [residualBoundary] at h
  erw [Walk.support_map] at h
  obtain ⟨w, _, hw⟩ := List.mem_map.mp h
  exact w.property.1 hw

/-- Nor can the second deleted endpoint occur on the residual boundary. -/
theorem second_not_mem_residualBoundary (M : ConnectedPlaneMap (residualGraph G u v))
    (base : (residualGraph G u v).Dart) : v ∉ (residualBoundary G u v M base).support := by
  intro h
  rw [residualBoundary] at h
  erw [Walk.support_map] at h
  obtain ⟨w, _, hw⟩ := List.mem_map.mp h
  exact w.property.2 hw

/-- Neighbor coordinates in the original graph exactly match the first
residual attachment coordinates used by the geometric constructor. -/
theorem cycleAttachments_first (M : ConnectedPlaneMap (residualGraph G u v))
    (base : (residualGraph G u v).Dart) :
    cycleAttachments (residualBoundary G u v M base) u =
      facePositions M.rawRotation base (firstNeighbors G u v) := by
  ext i
  simp [cycleAttachments, facePositions, residualBoundary, residualHom, firstNeighbors]

/-- The same exact coordinate identification for the second endpoint. -/
theorem cycleAttachments_second (M : ConnectedPlaneMap (residualGraph G u v))
    (base : (residualGraph G u v).Dart) :
    cycleAttachments (residualBoundary G u v M base) v =
      facePositions M.rawRotation base (secondNeighbors G u v) := by
  ext i
  simp [cycleAttachments, facePositions, residualBoundary, residualHom, secondNeighbors]

/-- The genuine forbidden-minor gap in the actual residual face. -/
theorem exists_gap_of_residual_face (hG : G.IsPlanar) (h3 : G.IsKConnected 3)
    (huv : G.Adj u v) (M : ConnectedPlaneMap (residualGraph G u v))
    (htwo : (residualGraph G u v).IsKConnected 2)
    (base : (residualGraph G u v).Dart)
    (hX : ∀ x ∈ firstNeighbors G u v, ∃ e : (residualGraph G u v).Dart,
      e.fst = x ∧ M.rawRotation.SameFace base e)
    (hY : ∀ y ∈ secondNeighbors G u v, ∃ e : (residualGraph G u v).Dart,
      e.fst = y ∧ M.rawRotation.SameFace base e) :
    ∃ a b, Consecutive (facePositions M.rawRotation base (firstNeighbors G u v)) a b ∧
      ∀ j ∈ facePositions M.rawRotation base (secondNeighbors G u v), closedArc a b j := by
  have hXcard : 2 ≤ (cycleAttachments (residualBoundary G u v M base) u).card := by
    rw [cycleAttachments_first]
    exact (two_le_card_firstNeighbors G u v huv h3).trans
      (card_le_facePositions M.rawRotation base _ hX)
  have hYcard : 2 ≤ (cycleAttachments (residualBoundary G u v M base) v).card := by
    rw [cycleAttachments_second]
    exact (two_le_card_secondNeighbors G u v huv h3).trans
      (card_le_facePositions M.rawRotation base _ hY)
  have h := exists_neighbor_gap_of_isPlanar hG (residualBoundary G u v M base)
    (residualBoundary_isCycle G u v M htwo base) u v huv
    (first_not_mem_residualBoundary G u v M base)
    (second_not_mem_residualBoundary G u v M base) hXcard hYcard
  simpa only [cycleAttachments_first, cycleAttachments_second] using h

/-- Actual reconstruction of the original graph from the one common face
exposed by deleting the contracted apex. All subsequent geometry is proved. -/
theorem exists_planeMap_of_residual_face (hG : G.IsPlanar) (h3 : G.IsKConnected 3)
    (huv : G.Adj u v) (M : ConnectedPlaneMap (residualGraph G u v))
    (htwo : (residualGraph G u v).IsKConnected 2)
    (base : (residualGraph G u v).Dart)
    (hX : ∀ x ∈ firstNeighbors G u v, ∃ e : (residualGraph G u v).Dart,
      e.fst = x ∧ M.rawRotation.SameFace base e)
    (hY : ∀ y ∈ secondNeighbors G u v, ∃ e : (residualGraph G u v).Dart,
      e.fst = y ∧ M.rawRotation.SameFace base e) : Nonempty (ConnectedPlaneMap G) := by
  obtain ⟨a, b, hgap, hclosed⟩ := exists_gap_of_residual_face G u v hG h3 huv M htwo base hX hY
  obtain ⟨N⟩ := exists_twoFanPlaneMap_of_gap M base _ _ hX hY a b hgap hclosed
  exact ⟨PlaneTopology.PlaneGeneralTransport.planeMap (twoFanIso G u v huv) N⟩

#print axioms residualBoundary_isCycle
#print axioms exists_gap_of_residual_face
#print axioms exists_planeMap_of_residual_face

end PlaneTopology.WagnerResidualEmbedding
