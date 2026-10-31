import GraphTheory.Surfaces.SignedRotationFourFlags
import GraphTheory.Surfaces.SignedRotationConnectedDensity

/-! Small connected graphs have nonnegative signed Euler genus.
This suffices for summing the density bound; general genus nonnegativity
is not assumed. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)

theorem eulerGenus_eq_zero_of_no_darts [IsEmpty G.Dart] : r.eulerGenus = 0 := by
  have hz (s : Setoid (Flag G)) : Nat.card (Quotient s) = 0 := by
    letI : IsEmpty (Quotient s) := ⟨fun q => Quotient.inductionOn q (fun x => isEmptyElim x.1)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
  simp only [eulerGenus, eulerCharacteristic, Component, Vertex, Edge, Face, hz]
  norm_num

theorem small_connected_genus_nonneg (hG : G.Connected)
    (hn : Fintype.card V ≤ 2) : 0 ≤ r.eulerGenus := by
  classical
  by_cases hd : Nonempty G.Dart
  · letI := hd
    have hf : (Nat.card r.Face : ℤ) ≤ G.edgeFinset.card := by
      exact_mod_cast r.face_card_le_edge_card
    have hv : (Nat.card r.Vertex : ℤ) ≤ Fintype.card V := by
      exact_mod_cast r.vertex_card_le
    unfold eulerGenus eulerCharacteristic
    rw [r.component_card_of_connected hG, r.edge_card]
    omega
  · letI : IsEmpty G.Dart := not_nonempty_iff.mp hd
    rw [r.eulerGenus_eq_zero_of_no_darts]

theorem connected_edge_genus_bound (hG : G.Connected) :
    (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V + 3 * r.eulerGenus := by
  by_cases hn : 3 ≤ Fintype.card V
  · have h := r.connected_euler_edge_bound hG hn
    omega
  · have hg := r.small_connected_genus_nonneg hG (by omega)
    have hsmall : ∀ n : ℕ, n ≤ 2 → n.choose 2 ≤ 3 * n := by
      intro n hn
      interval_cases n <;> decide
    have he := G.card_edgeFinset_le_card_choose_two.trans (hsmall _ (by omega))
    have he' : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V := by exact_mod_cast he
    omega

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.eulerGenus_eq_zero_of_no_darts
#print axioms SimpleGraph.SignedRotation.small_connected_genus_nonneg
#print axioms SimpleGraph.SignedRotation.connected_edge_genus_bound
