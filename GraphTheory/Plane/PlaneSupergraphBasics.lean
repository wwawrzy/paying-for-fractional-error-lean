import GraphTheory.Plane.TreePlaneMap
import GraphTheory.Plane.WagnerThreeEmbedding

/-!
# Small bases and the connected-supergraph induction target

Allowing a same-vertex connected supergraph handles disconnected inputs:
bridges can be added between their separately embedded parts. Every
witness is still an actual faithful plane map, not a geometric provider.
-/

namespace PlaneTopology.PlaneSupergraphBasics

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneTriangulationMaximal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical map-existence predicate can be unpacked at any specified
decidable adjacency instance, by proof irrelevance of the decisions. -/
theorem hasPlaneMap_iff_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasPlaneMap G ↔ Nonempty (ConnectedPlaneMap G) := by
  unfold HasPlaneMap
  have hdec : (fun a b : V => Classical.propDecidable (G.Adj a b)) =
      (inferInstance : DecidableRel G.Adj) := Subsingleton.elim _ _
  rw [hdec]

/-- There is an actual connected plane-map supergraph on exactly the old vertices. -/
def HasPlaneSupergraph (G : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph V, G ≤ H ∧ HasPlaneMap H

/-- A plane map is already a witness to the same-vertex supergraph predicate. -/
theorem hasPlaneSupergraph_of_map {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : ConnectedPlaneMap G) : HasPlaneSupergraph G :=
  ⟨G, le_rfl, hasPlaneMap_of_map M⟩

/-- The complete graph on any two-element vertex type has a genuine tree map. -/
noncomputable def completePlaneMapOfCardTwo (hcard : Fintype.card V = 2) :
    ConnectedPlaneMap (⊤ : SimpleGraph V) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have ht : (⊤ : SimpleGraph V).IsTree := {
    connected := connected_top
    isAcyclic := IsAcyclic.of_card_le_two (by simp [ENat.card_eq_coe_fintype_card, hcard]) }
  exact PlaneTopology.TreePlaneMap.planeMapOfTree (⊤ : SimpleGraph V) ht (by omega)

/-- The complete graph on any three-element vertex type has the transported
explicit triangular sphere map. -/
noncomputable def completePlaneMapOfCardThree (hcard : Fintype.card V = 3) :
    ConnectedPlaneMap (⊤ : SimpleGraph V) :=
  PlaneTopology.PlaneGeneralTransport.planeMap
    (Iso.completeGraph (Fintype.equivFinOfCardEq hcard).symm)
    PlaneTopology.PlaneSmallBases.trianglePlaneMap

/-- Every graph on two or three vertices admits a same-vertex connected
plane supergraph; no planarity premise is needed for these bases. -/
theorem hasPlaneSupergraph_of_small (G : SimpleGraph V)
    (hlo : 2 ≤ Fintype.card V) (hhi : Fintype.card V ≤ 3) : HasPlaneSupergraph G := by
  refine ⟨⊤, le_top, ?_⟩
  by_cases htwo : Fintype.card V = 2
  · exact hasPlaneMap_of_map (completePlaneMapOfCardTwo htwo)
  · exact hasPlaneMap_of_map (completePlaneMapOfCardThree (by omega))

/-- A connected plane supergraph on at least three vertices admits a
triangular plane supergraph on the same vertex type. -/
theorem hasTriangulatedSupergraph_of_hasPlaneSupergraph (G : SimpleGraph V)
    (hG : HasPlaneSupergraph G) (hcard : 3 ≤ Fintype.card V) :
    TriangularFaces.HasTriangulatedSupergraph G := by
  classical
  obtain ⟨H, hGH, hH⟩ := hG
  obtain ⟨M⟩ := (hasPlaneMap_iff_nonempty H).mp hH
  obtain ⟨T, hHT, N, htri⟩ :=
    PlaneTopology.PlaneTriangulation.hasTriangulatedSupergraph_of_connectedPlaneMap M hcard
  exact ⟨T, hGH.trans hHT, N, htri⟩

#print axioms completePlaneMapOfCardTwo
#print axioms hasPlaneSupergraph_of_small
#print axioms hasTriangulatedSupergraph_of_hasPlaneSupergraph

end PlaneTopology.PlaneSupergraphBasics
