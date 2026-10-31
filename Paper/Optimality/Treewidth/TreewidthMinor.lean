import Paper.Optimality.Treewidth.TreeDecompositionRoutes

/-! Actual minor branch sets induce a tree decomposition of the minor.
Disjointness injects each minor bag into its original physical bag. -/
namespace Paper.TreewidthMinor
open SimpleGraph
universe u
variable {V A I : Type u} {G : SimpleGraph V} {J : SimpleGraph A} {T : SimpleGraph I}

noncomputable def map (D : G.TreeDecomposition T) (M : MinorModel J G) : J.TreeDecomposition T where
  bag i := {a | ∃ v ∈ M.branchSet a, v ∈ D.bag i}
  isTree := D.isTree
  cover a := by
    obtain ⟨v, hv⟩ := M.nonempty a
    obtain ⟨i, hi⟩ := D.cover v
    exact ⟨i, v, hv, hi⟩
  edge_mem a b hab := by
    obtain ⟨v, hv, w, hw, hvw⟩ := M.adjacent a b hab
    obtain ⟨i, hvi, hwi⟩ := D.edge_mem hvw
    exact ⟨i, ⟨v, hv, hvi⟩, ⟨w, hw, hwi⟩⟩
  bag_connected a _ _ p hp hi hj _ hr :=
    TreeDecompositionRoutes.connected_bag_union D (M.branchSet a) (M.connected a) hi hj p hp hr

theorem width [Finite A] (D : G.TreeDecomposition T) (M : MinorModel J G) (t : ℕ)
    (hD : D.IsWidthLE t) : (map D M).IsWidthLE t := by
  classical
  intro i
  refine ⟨Set.toFinite _, ?_⟩
  let f : (map D M).bag i → D.bag i := fun a => ⟨a.property.choose, a.property.choose_spec.2⟩
  have hf : ∀ a, (f a).val ∈ M.branchSet a.val := fun a => a.property.choose_spec.1
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    by_contra hn
    have hv := congrArg Subtype.val he
    exact Set.disjoint_left.mp (M.disjoint a.val b.val hn) (hf a) (hv.symm ▸ hf b)
  letI : Fintype ↥(D.bag i) := (hD i).1.fintype
  have hc := Nat.card_le_card_of_injective f hinj
  have hcard : ((map D M).bag i).ncard ≤ (D.bag i).ncard := by
    simpa only [Nat.card_coe_set_eq] using hc
  exact hcard.trans (hD i).2

theorem treeWidth_mono [Finite V] [Finite A] (hm : J.IsMinor G) : J.treeWidth ≤ G.treeWidth := by
  obtain ⟨I, T, D, hD⟩ := G.exists_treeDecomposition_isWidthLE_treeWidth
  obtain ⟨M⟩ := hm
  exact treeWidth_le_of_isWidthLE (map D M) (width D M G.treeWidth hD)

end Paper.TreewidthMinor
