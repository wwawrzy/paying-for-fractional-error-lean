import Paper.Optimality.Treewidth.CliqueSixExtremalLocal
import Paper.Optimality.Treewidth.CliqueEightSixFreeDegree
import Paper.Optimality.Treewidth.CliqueAffineCore
namespace Paper.CliqueSixExtremalGeneral
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem common_three (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (he : G.edgeFinset.card+10 = 4*Fintype.card V) (u w : V) (huw : G.Adj u w) :
    3 ≤ Fintype.card (G.commonNeighbors u w) := by
  classical
  have hf := IsHMinorFree.minor hG (contractMinorExisting% G u w huw)
  have hcard : Fintype.card ({u}ᶜ : Set V) = Fintype.card V-1 := by simp [Fintype.card_compl_set]
  have hb := SixCliqueSharp.edge_bound (G.contractAdj u w huw) hf (by omega)
  rw [hcard] at hb
  have hc := existingContractEdgeCountProof% G u w huw huw.ne
  omega

theorem four_clique (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (he : G.edgeFinset.card+10 = 4*Fintype.card V) (u : V) (hu : G.degree u = 4) :
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

theorem five_complement (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (he : G.edgeFinset.card+10 = 4*Fintype.card V) (u : V) (hu : G.degree u = 5) :
    ∀ w : G.neighborSet u, ((G.induce (G.neighborSet u))ᶜ).degree w ≤ 1 := by
  classical
  have hcard : Fintype.card (G.neighborSet u) = 5 := by rw [G.card_neighborSet_eq_degree,hu]
  intro w
  have hd := commonNeighbors_implies_induced_degree G u 3 w
    (common_three G hG hV he u w.val w.property)
  rw [SimpleGraph.degree_compl,hcard]
  omega


theorem four_le (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (he : G.edgeFinset.card+10 = 4*Fintype.card V) (v : V) : 4 ≤ G.degree v := by
  classical
  let T : Set V := {v}ᶜ
  let H := G.induce T
  have hcard : Fintype.card T = Fintype.card V-1 := by simp [T,Fintype.card_compl_set]
  have hf : H.IsKMinorFree 6 := IsHMinorFree.minor hG (IsMinor.of_induce G T)
  have hb := SixCliqueSharp.edge_bound H hf (by omega)
  rw [hcard] at hb
  have hs : H.edgeFinset.card = G.edgeFinset.card-G.degree v :=
    (G.card_edgeFinset_induce_compl_singleton v).trans (G.card_edgeFinset_deleteIncidenceSet v)
  have hd := G.degree_le_card_edgeFinset (v := v)
  omega

theorem small_dichotomy (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (hupper : Fintype.card V ≤ 9) (he : G.edgeFinset.card+10 = 4*Fintype.card V) :
    ∃ u : V,
      (G.degree u = 4 ∧ G.IsClique (G.neighborSet u)) ∨
      (G.degree u = 5 ∧ ∀ w : G.neighborSet u,
        ((G.induce (G.neighborSet u))ᶜ).degree w ≤ 1) := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u,hu⟩ := G.exists_minimal_degree_vertex
  have hs := G.minDegree_mul_card_le_two_mul_card_edges
  have hlo := four_le G hG hV he u
  have hh : G.degree u = 4 ∨ G.degree u = 5 := by
    by_contra hn
    have hm : 6 ≤ G.minDegree := by omega
    have hmul := Nat.mul_le_mul_right (Fintype.card V) hm
    omega
  refine ⟨u,?_⟩
  rcases hh with h4 | h5
  · exact Or.inl ⟨h4,four_clique G hG hV he u h4⟩
  · exact Or.inr ⟨h5,five_complement G hG hV he u h5⟩
theorem common_deficit (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (b : ℕ) (he : G.edgeFinset.card+b = 4*Fintype.card V) (u w : V) (huw : G.Adj u w) :
    13 ≤ Fintype.card (G.commonNeighbors u w)+b := by
  classical
  have hf := IsHMinorFree.minor hG (contractMinorExisting% G u w huw)
  have hcard : Fintype.card ({u}ᶜ : Set V) = Fintype.card V-1 := by simp [Fintype.card_compl_set]
  have hb := SixCliqueSharp.edge_bound (G.contractAdj u w huw) hf (by omega)
  rw [hcard] at hb
  have hc := existingContractEdgeCountProof% G u w huw huw.ne
  omega

theorem degree_deficit (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (b : ℕ) (he : G.edgeFinset.card+b = 4*Fintype.card V) (v : V) : 14 ≤ G.degree v+b := by
  classical
  let T : Set V := {v}ᶜ
  let H := G.induce T
  have hcard : Fintype.card T = Fintype.card V-1 := by simp [T,Fintype.card_compl_set]
  have hf : H.IsKMinorFree 6 := IsHMinorFree.minor hG (IsMinor.of_induce G T)
  have hb := SixCliqueSharp.edge_bound H hf (by omega)
  rw [hcard] at hb
  have hs : H.edgeFinset.card = G.edgeFinset.card-G.degree v :=
    (G.card_edgeFinset_induce_compl_singleton v).trans (G.card_edgeFinset_deleteIncidenceSet v)
  have hd := G.degree_le_card_edgeFinset (v := v)
  omega

theorem neighborhood_deficit (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (b : ℕ) (he : G.edgeFinset.card+b = 4*Fintype.card V) (u : V) (w : G.neighborSet u) :
    ((G.induce (G.neighborSet u))ᶜ).degree w + 14 ≤ G.degree u+b := by
  classical
  have hcard : Fintype.card (G.neighborSet u) = G.degree u := G.card_neighborSet_eq_degree u
  have hc := common_deficit G hG hV b he u w.val w.property
  have hd := commonNeighbors_implies_induced_degree G u (Fintype.card (G.commonNeighbors u w.val)) w (by rfl)
  have hl := (G.induce (G.neighborSet u)).degree_lt_card_verts w
  rw [hcard] at hl
  rw [SimpleGraph.degree_compl,hcard]
  omega

theorem near_three_clique (hG : G.IsKMinorFree 6) (hV : 5 ≤ Fintype.card V)
    (he : G.edgeFinset.card+11 = 4*Fintype.card V) (u : V) (hu : G.degree u = 3) :
    G.IsClique (G.neighborSet u) := by
  classical
  intro a ha b hb hab
  let N := G.neighborFinset u
  let C := (G.commonNeighbors u a).toFinset
  have haN : a ∈ N := (G.mem_neighborFinset u a).mpr ha
  have hN : N.card = 3 := (G.card_neighborFinset_eq_degree u).trans hu
  have hc : 2 ≤ C.card := by
    simpa only [C,Set.toFinset_card] using (show 2 ≤ Fintype.card (G.commonNeighbors u a) from by have hh := common_deficit G hG hV 11 he u a ha; omega)
  have hs : C ⊆ N.erase a := by
    intro z hz
    have hh := Set.mem_toFinset.mp hz
    exact Finset.mem_erase.mpr ⟨hh.2.ne.symm,(G.mem_neighborFinset u z).mpr hh.1⟩
  have heq : C = N.erase a := Finset.eq_of_subset_of_card_le hs (by
    rw [Finset.card_erase_of_mem haN,hN]; exact hc)
  have hbC : b ∈ C := by rw [heq]; exact Finset.mem_erase.mpr ⟨hab.symm,(G.mem_neighborFinset u b).mpr hb⟩
  exact (Set.mem_toFinset.mp hbC).2

end Paper.CliqueSixExtremalGeneral

