import Paper.Optimality.Treewidth.TreeDecompositionFinite

namespace Paper.TreeDecompositionLeaf
open SimpleGraph
universe u
variable {V I : Type u} {G : SimpleGraph V} {T : SimpleGraph I}
variable (D : G.TreeDecomposition T)

theorem only_leaf [Fintype I] [DecidableRel T.Adj] (i j : I) (hi : T.degree i = 1)
    (hij : T.Adj i j) {v : V} (hv : v ∈ D.bag i) (hn : v ∉ D.bag j) :
    ∀ r, v ∈ D.bag r → r = i := by
  classical
  intro r hvr
  by_contra hr
  obtain ⟨p, hp, _⟩ := D.isTree.existsUnique_path i r
  have hnil : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hr)
  obtain ⟨s, hs, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hi
  have he : p.snd = j := (huniq p.snd (p.adj_snd hnil)).trans (huniq j hij).symm
  have hm : p.snd ∈ p.support := List.mem_of_mem_tail (p.snd_mem_tail_support hnil)
  exact hn (he ▸ D.bag_connected v p hp hv hvr hm)

theorem degree_le [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (t : ℕ) (hD : D.IsWidthLE t)
    (v : V) (i : I) (hv : v ∈ D.bag i) (honly : ∀ j, v ∈ D.bag j → j = i) : G.degree v ≤ t := by
  classical
  have hsub : (↑(insert v (G.neighborFinset v)) : Set V) ⊆ D.bag i := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hv
    · obtain ⟨j, hvj, hwj⟩ := D.edge_mem ((SimpleGraph.mem_neighborFinset G v w).mp hw)
      exact honly j hvj ▸ hwj
  have hc := Set.ncard_le_ncard hsub (hD i).1
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp)] at hc
  change G.degree v + 1 ≤ (D.bag i).ncard at hc
  have hh := (hD i).2
  omega

noncomputable def prune [Fintype I] [DecidableRel T.Adj] (i j : I) (hi : T.degree i = 1)
    (hij : T.Adj i j) (hsub : D.bag i ⊆ D.bag j) :
    G.TreeDecomposition (T.induce ({i}ᶜ : Set I)) := by
  classical
  have hj : j ∈ ({i}ᶜ : Set I) := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hij.ne.symm
  refine {
    bag := fun r => D.bag r.val
    isTree := ⟨D.isTree.connected.induce_compl_singleton_of_degree_eq_one hi, D.isTree.isAcyclic.induce _⟩
    cover := ?_
    edge_mem := ?_
    bag_connected := ?_ }
  · intro v
    obtain ⟨r, hr⟩ := D.cover v
    by_cases he : r = i
    · exact ⟨⟨j, hj⟩, hsub (he ▸ hr)⟩
    · exact ⟨⟨r, he⟩, hr⟩
  · intro v w hvw
    obtain ⟨r, hvr, hwr⟩ := D.edge_mem hvw
    by_cases he : r = i
    · exact ⟨⟨j, hj⟩, hsub (he ▸ hvr), hsub (he ▸ hwr)⟩
    · exact ⟨⟨r, he⟩, hvr, hwr⟩
  · intro v r s p hp hvr hvs z hz
    let e : T.induce ({i}ᶜ : Set I) →g T := (Embedding.induce ({i}ᶜ : Set I)).toHom
    have hpath : (p.map e).IsPath := p.map_isPath_of_injective Subtype.val_injective hp
    apply D.bag_connected v (p.map e) hpath hvr hvs
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩

theorem prune_width [Fintype I] [DecidableRel T.Adj] (i j : I) (hi : T.degree i = 1)
    (hij : T.Adj i j) (hsub : D.bag i ⊆ D.bag j) (t : ℕ) (hD : D.IsWidthLE t) :
    (prune D i j hi hij hsub).IsWidthLE t := fun r => hD r.val

end Paper.TreeDecompositionLeaf
