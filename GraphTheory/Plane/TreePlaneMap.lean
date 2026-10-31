import GraphTheory.Plane.CellularEuler
import GraphTheory.Plane.PlaneRotationExists

/-!
# Actual sphere embeddings of all finite edgeful trees

The rotation is constructed from vertex-local cycles. Euler is then proved
using the general cellular inequality and the tree edge count. No IsPlanar
axiom, supplied embedding, or geometric-existence provider is used.
-/

namespace PlaneTopology.TreePlaneMap

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaceBoundaryAlgebra PlaneTopology.CellularEuler

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All finite connected edgeful graphs have an actual faithful cellular
map; only its genus remains undetermined for general graphs. -/
noncomputable def cellularMap (hG : G.Connected) (hD : Nonempty G.Dart) :
    ConnectedCellularMap G where
  rotation := PlaneTopology.PlaneRotationExists.faithfulRotationSystem G
  connected := hG
  dartNonempty := hD

omit [DecidableEq V] in
/-- Trees with at least two vertices have actual darts. -/
theorem dartNonempty_of_isTree (hG : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    Nonempty G.Dart := by
  have htree := hG.card_edgeFinset
  have hpos : 0 < G.edgeFinset.card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact ⟨dartOfEdge ⟨e, he⟩⟩

/-- A genuine sphere-map constructor for every finite tree on at least two
vertices. The map is produced, rather than assumed as a certificate. -/
noncomputable def planeMapOfTree (hG : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    ConnectedPlaneMap G :=
  treePlaneMap (cellularMap G hG.connected (dartNonempty_of_isTree G hG hcard)) hG

/-- Existence form of the unconditional tree embedding theorem. -/
theorem nonempty_planeMap_of_isTree (hG : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    Nonempty (ConnectedPlaneMap G) :=
  ⟨planeMapOfTree G hG hcard⟩

/-- The constructed tree embedding has exactly one actual face orbit. -/
theorem planeMapOfTree_numFaces (hG : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    (planeMapOfTree G hG hcard).rawRotation.numFaces = 1 :=
  numFaces_eq_one_of_isTree _ hG

#print axioms nonempty_planeMap_of_isTree
#print axioms planeMapOfTree_numFaces

end PlaneTopology.TreePlaneMap
