import Paper.Optimality.Treewidth.TreeDecompositionLeaf

/-! A finite graph of treewidth t has a vertex of degree at most t.
Minimize the number of bags of a finite decomposition and prune a redundant
leaf. A nonredundant leaf contains a vertex occurring in no other bag. -/
namespace Paper.TreewidthLowDegree
open SimpleGraph
universe u
variable {V I : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {T : SimpleGraph I}

theorem of_decomposition [Nonempty V] (D : G.TreeDecomposition T) (t : ℕ) (hD : D.IsWidthLE t) :
    ∃ v : V, G.degree v ≤ t := by
  classical
  let P : ℕ → Prop := fun n => ∃ (J : Type u) (fin : Fintype J) (U : SimpleGraph J)
    (E : G.TreeDecomposition U), E.IsWidthLE t ∧ @Fintype.card J fin = n
  obtain ⟨J₀, fin₀, U₀, E₀, hE₀⟩ := TreeDecompositionFinite.exists_finite D t hD
  have hP : ∃ n, P n := ⟨@Fintype.card J₀ fin₀, J₀, fin₀, U₀, E₀, hE₀, rfl⟩
  let n := Nat.find hP
  obtain ⟨J, fin, U, E, hE, hcard⟩ := Nat.find_spec hP
  letI : Fintype J := fin
  letI : DecidableRel U.Adj := fun _ _ => Classical.propDecidable _
  have hmin : ∀ m, P m → n ≤ m := fun _ hm => Nat.find_min' hP hm
  by_cases hs : Subsingleton J
  · letI := hs
    let v : V := Classical.arbitrary V
    obtain ⟨i, hvi⟩ := E.cover v
    exact ⟨v, TreeDecompositionLeaf.degree_le E t hE v i hvi (fun j _ => Subsingleton.elim j i)⟩
  · haveI : Nontrivial J := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨i, hi⟩ := E.isTree.exists_vert_degree_one_of_nontrivial
    obtain ⟨j, hij, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hi
    by_cases hsub : E.bag i ⊆ E.bag j
    · have hm : P (Fintype.card ↥({i}ᶜ : Set J)) :=
        ⟨↥({i}ᶜ : Set J), inferInstance, U.induce ({i}ᶜ : Set J),
          TreeDecompositionLeaf.prune E i j hi hij hsub,
          TreeDecompositionLeaf.prune_width E i j hi hij hsub t hE, rfl⟩
      have hc : Fintype.card ↥({i}ᶜ : Set J) = Fintype.card J - 1 := by
        rw [Fintype.card_compl_set]
        simp
      have hp : 0 < Fintype.card J := Fintype.card_pos_iff.mpr E.isTree.connected.nonempty
      have hsmall := hmin _ hm
      omega
    · obtain ⟨v, hvi, hvj⟩ := Set.not_subset.mp hsub
      exact ⟨v, TreeDecompositionLeaf.degree_le E t hE v i hvi
        (TreeDecompositionLeaf.only_leaf E i j hi hij hvi hvj)⟩

theorem of_treeWidth [Nonempty V] (t : ℕ) (ht : G.treeWidth ≤ t) : ∃ v : V, G.degree v ≤ t := by
  obtain ⟨I, T, D, hD⟩ := G.exists_treeDecomposition_isWidthLE_treeWidth
  exact of_decomposition D t (hD.mono ht)

end Paper.TreewidthLowDegree
