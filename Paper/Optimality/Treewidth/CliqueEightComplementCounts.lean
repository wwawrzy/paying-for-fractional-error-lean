import Paper.Optimality.Treewidth.SevenCliqueTwentySixFivePattern
namespace Paper.CliqueEightComplementCounts
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem degree_le_two (hcard : Fintype.card V = 8)
    (hmin : ∀ v, 5 ≤ G.degree v) (v : V) : Gᶜ.degree v ≤ 2 := by
  classical
  rw [G.degree_compl, hcard]
  have := hmin v
  omega

theorem edge_count (hcard : Fintype.card V = 8)
    (hedges : G.edgeFinset.card = 22) : Gᶜ.edgeFinset.card = 6 := by
  classical
  have hsum : (∑ v : V, G.degree v) + (∑ v : V, Gᶜ.degree v) = 56 := by
    rw [← Finset.sum_add_distrib]
    have hp : ∀ v : V, G.degree v + Gᶜ.degree v = 7 := by
      intro v
      have hb := G.degree_lt_card_verts v
      rw [G.degree_compl, hcard]
      rw [hcard] at hb
      omega
    simp_rw [hp]
    simp [hcard]
  have hG := G.sum_degrees_eq_twice_card_edges
  have hc := Gᶜ.sum_degrees_eq_twice_card_edges
  rw [hedges] at hG
  omega
theorem two_nonneighbors (hcard : Fintype.card V = 8) (u : V) (hu : G.degree u = 5) :
    ∃ a b : V, a ≠ b ∧ ∀ x, (x ≠ u ∧ ¬G.Adj u x) ↔ x = a ∨ x = b := by
  classical
  let R := (insert u (G.neighborFinset u))ᶜ
  have hR : R.card = 2 := by
    dsimp [R]
    rw [Finset.card_compl,Finset.card_insert_of_notMem (G.notMem_neighborFinset_self u),
      G.card_neighborFinset_eq_degree,hu,hcard]
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp hR
  refine ⟨a,b,hab,?_⟩
  intro x
  have hm : x ∈ R ↔ x ≠ u ∧ ¬G.Adj u x := by
    simp [R,SimpleGraph.mem_neighborFinset]
  rw [← hm,he]
  simp
end Paper.CliqueEightComplementCounts
