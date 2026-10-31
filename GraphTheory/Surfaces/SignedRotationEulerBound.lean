import GraphTheory.Surfaces.SignedRotationFaceFlags
import GraphTheory.Surfaces.SignedRotationGeneralFaces
import GraphTheory.Surfaces.SignedRotationComponents
import GraphTheory.Surfaces.SignedRotationEdges

/-! Euler's edge bounds for connected signed rotations, including graphs with leaves.
Establishing minor closure is a separate step toward the surface application. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem vertex_card_le : Nat.card r.Vertex ≤ Fintype.card V := by
  rw [r.vertex_card]
  simpa only [Nat.card_eq_fintype_card] using
    (Nat.card_le_card_of_injective (Subtype.val : G.support → V) Subtype.val_injective)

theorem euler_edge_bound (hG : G.Connected) [Nonempty G.Dart]
    (hdeg : ∀ v, 2 ≤ G.degree v) :
    (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6 + 3 * r.eulerGenus := by
  have hf : 3 * (Nat.card r.Face : ℤ) ≤ 2 * G.edgeFinset.card := by
    exact_mod_cast r.face_edge_bound hdeg
  have hv : (Nat.card r.Vertex : ℤ) ≤ Fintype.card V := by
    exact_mod_cast r.vertex_card_le
  have hg : r.eulerGenus = 2 -
      ((Nat.card r.Vertex : ℤ) - G.edgeFinset.card + Nat.card r.Face) := by
    simp only [eulerGenus, eulerCharacteristic, r.component_card_of_connected hG,
      r.edge_card, Nat.cast_one, mul_one]
  omega

theorem edge_bound_of_genus_le_two (hG : G.Connected) [Nonempty G.Dart]
    (hdeg : ∀ v, 2 ≤ G.degree v) (hg : r.eulerGenus ≤ 2) :
    G.edgeFinset.card ≤ 3 * Fintype.card V := by
  have h := r.euler_edge_bound hG hdeg
  omega

theorem euler_edge_bound_of_card (hG : G.Connected) [Nonempty G.Dart]
    (hn : 3 ≤ Fintype.card V) :
    (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6 + 3 * r.eulerGenus := by
  have hf : 3 * (Nat.card r.Face : ℤ) ≤ 2 * G.edgeFinset.card := by
    exact_mod_cast r.face_edge_bound_of_connected hG hn
  have hv : (Nat.card r.Vertex : ℤ) ≤ Fintype.card V := by
    exact_mod_cast r.vertex_card_le
  have hg : r.eulerGenus = 2 -
      ((Nat.card r.Vertex : ℤ) - G.edgeFinset.card + Nat.card r.Face) := by
    simp only [eulerGenus, eulerCharacteristic, r.component_card_of_connected hG,
      r.edge_card, Nat.cast_one, mul_one]
  omega

theorem edge_bound_of_card_genus_le_two (hG : G.Connected) [Nonempty G.Dart]
    (hn : 3 ≤ Fintype.card V) (hg : r.eulerGenus ≤ 2) :
    G.edgeFinset.card ≤ 3 * Fintype.card V := by
  have h := r.euler_edge_bound_of_card hG hn
  omega

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.vertex_card_le
#print axioms SimpleGraph.SignedRotation.euler_edge_bound
#print axioms SimpleGraph.SignedRotation.edge_bound_of_genus_le_two
#print axioms SimpleGraph.SignedRotation.euler_edge_bound_of_card
#print axioms SimpleGraph.SignedRotation.edge_bound_of_card_genus_le_two
