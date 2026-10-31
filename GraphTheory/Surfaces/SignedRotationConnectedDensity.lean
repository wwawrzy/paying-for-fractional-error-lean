import GraphTheory.Surfaces.SignedRotationEulerBound

/-! Edge density of connected graphs with a signed rotation of Euler genus at most two.
Small graphs are handled separately; no minimum-degree or dart-existence premise
is required by the density endpoint. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)

theorem nonempty_dart_of_connected (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) : Nonempty G.Dart := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let v : V := Classical.arbitrary V
  obtain ⟨w, hw⟩ := hG.preconnected.exists_adj_of_nontrivial v
  exact ⟨⟨(v, w), hw⟩⟩

theorem connected_euler_edge_bound (hG : G.Connected)
    (hn : 3 ≤ Fintype.card V) :
    (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6 + 3 * r.eulerGenus := by
  letI := nonempty_dart_of_connected hG (by omega)
  exact r.euler_edge_bound_of_card hG hn

theorem connected_edge_bound (hG : G.Connected) (hg : r.eulerGenus ≤ 2) :
    G.edgeFinset.card ≤ 3 * Fintype.card V := by
  by_cases hn : 3 ≤ Fintype.card V
  · have h := r.connected_euler_edge_bound hG hn
    omega
  · have hsmall : ∀ n : ℕ, n ≤ 2 → n.choose 2 ≤ 3 * n := by
      intro n hn
      interval_cases n <;> decide
    exact G.card_edgeFinset_le_card_choose_two.trans (hsmall _ (by omega))

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.nonempty_dart_of_connected
#print axioms SimpleGraph.SignedRotation.connected_euler_edge_bound
#print axioms SimpleGraph.SignedRotation.connected_edge_bound
