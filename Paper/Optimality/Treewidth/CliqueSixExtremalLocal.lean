import Paper.Optimality.Treewidth.SixCliqueSharp
import Paper.Optimality.Treewidth.CliqueEightSixFreeDegree
import Paper.Optimality.Treewidth.CliqueAffineCore
namespace Paper.CliqueSixExtremalLocal
open SimpleGraph
macro "contractMinorExisting%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `GraphTheory.SimpleGraph.Minor.AverageDegree
    `SimpleGraph.contractAdj_isMinor))
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem common_three (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (he : G.edgeFinset.card = 22) (u w : V) (huw : G.Adj u w) :
    3 ≤ Fintype.card (G.commonNeighbors u w) := by
  classical
  have hf := IsHMinorFree.minor hG (contractMinorExisting% G u w huw)
  have hcard : Fintype.card ({u}ᶜ : Set V) = 7 := by simp [Fintype.card_compl_set,hV]
  have hb := SixCliqueSharp.edge_bound (G.contractAdj u w huw) hf (by omega)
  rw [hcard] at hb
  have hc := existingContractEdgeCountProof% G u w huw huw.ne
  omega

theorem four_clique (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (he : G.edgeFinset.card = 22) (u : V) (hu : G.degree u = 4) :
    G.IsClique (G.neighborSet u) := by
  classical
  intro a ha b hb hab
  let N := G.neighborFinset u
  let C := (G.commonNeighbors u a).toFinset
  have haN : a ∈ N := (G.mem_neighborFinset u a).mpr ha
  have hN : N.card = 4 := (G.card_neighborFinset_eq_degree u).trans hu
  have hc : 3 ≤ C.card := by
    simpa only [C,Set.toFinset_card] using common_three G hG hV he u a ha
  have hs : C ⊆ N.erase a := by
    intro z hz
    have hh := Set.mem_toFinset.mp hz
    exact Finset.mem_erase.mpr ⟨hh.2.ne.symm,(G.mem_neighborFinset u z).mpr hh.1⟩
  have heq : C = N.erase a := Finset.eq_of_subset_of_card_le hs (by
    rw [Finset.card_erase_of_mem haN,hN]; exact hc)
  have hbC : b ∈ C := by rw [heq]; exact Finset.mem_erase.mpr ⟨hab.symm,(G.mem_neighborFinset u b).mpr hb⟩
  exact (Set.mem_toFinset.mp hbC).2

theorem five_complement (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (he : G.edgeFinset.card = 22) (u : V) (hu : G.degree u = 5) :
    ∀ w : G.neighborSet u, ((G.induce (G.neighborSet u))ᶜ).degree w ≤ 1 := by
  classical
  have hcard : Fintype.card (G.neighborSet u) = 5 := by rw [G.card_neighborSet_eq_degree,hu]
  intro w
  have hd := commonNeighbors_implies_induced_degree G u 3 w
    (common_three G hG hV he u w.val w.property)
  rw [SimpleGraph.degree_compl,hcard]
  omega


theorem dichotomy (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (he : G.edgeFinset.card = 22) :
    ∃ u : V,
      (G.degree u = 4 ∧ G.IsClique (G.neighborSet u)) ∨
      (G.degree u = 5 ∧ ∀ w : G.neighborSet u,
        ((G.induce (G.neighborSet u))ᶜ).degree w ≤ 1) := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u,hu⟩ := G.exists_minimal_degree_vertex
  have hs := G.minDegree_mul_card_le_two_mul_card_edges
  rw [hV,he] at hs
  have hlo := CliqueEightSixFreeDegree.four_le G hG hV he u
  have hh : G.degree u = 4 ∨ G.degree u = 5 := by omega
  refine ⟨u,?_⟩
  rcases hh with h4 | h5
  · exact Or.inl ⟨h4,four_clique G hG hV he u h4⟩
  · exact Or.inr ⟨h5,five_complement G hG hV he u h5⟩

end Paper.CliqueSixExtremalLocal


