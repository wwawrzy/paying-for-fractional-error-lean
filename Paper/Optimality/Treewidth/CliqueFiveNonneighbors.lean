import Paper.Optimality.Treewidth.CliqueEightComplement

/-! In a graph with no independent triple, the nonneighbors of any
vertex form a clique. This controls low-degree vertices on five vertices. -/
namespace Paper.CliqueFiveNonneighbors
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

theorem adjacent (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 2)
    (v x y : V) (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (hnx : ¬H.Adj v x) (hny : ¬H.Adj v y) : H.Adj x y := by
  by_contra hnxy
  have hind : H.IsIndepSet (({v, x, y} : Finset V) : Set V) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact False.elim (hab rfl)
      | exact hnx
      | exact hny
      | exact hnxy
      | exact fun h => hnx h.symm
      | exact fun h => hny h.symm
      | exact fun h => hnxy h.symm
  have hb := hsmall {v, x, y} hind
  simp [hvx, hvy, hxy] at hb

theorem clique (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 2)
    (v : V) : H.IsClique (((insert v (H.neighborFinset v))ᶜ : Finset V) : Set V) := by
  intro x hx y hy hxy
  have hx' := Finset.mem_compl.mp hx
  have hy' := Finset.mem_compl.mp hy
  apply adjacent H hsmall v x y
  · exact fun h => hx' (Finset.mem_insert.mpr (Or.inl h.symm))
  · exact fun h => hy' (Finset.mem_insert.mpr (Or.inl h.symm))
  · exact hxy
  · exact fun h => hx' (Finset.mem_insert_of_mem ((H.mem_neighborFinset v x).mpr h))
  · exact fun h => hy' (Finset.mem_insert_of_mem ((H.mem_neighborFinset v y).mpr h))

theorem clique_card_le_three (hd : ∀ x, H.degree x ≤ 2)
    (S : Finset V) (hc : H.IsClique (S : Set V)) : S.card ≤ 3 := by
  by_cases hn : S.Nonempty
  · obtain ⟨x, hx⟩ := hn
    have hs : S.erase x ⊆ H.neighborFinset x := by
      intro y hy
      obtain ⟨hyx, hyS⟩ := Finset.mem_erase.mp hy
      exact (H.mem_neighborFinset x y).mpr (hc hx hyS hyx.symm)
    have hb := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hx, H.card_neighborFinset_eq_degree] at hb
    have := hd x
    omega
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [this]

theorem low_degree_triangle (hV : Fintype.card V = 5) (hd : ∀ x, H.degree x ≤ 2)
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 2)
    (v : V) (hv : H.degree v ≤ 1) :
    ∃ S : Finset V, S.card = 3 ∧ H.IsClique (S : Set V) := by
  let S := (insert v (H.neighborFinset v))ᶜ
  have hc : H.IsClique (S : Set V) := clique H hsmall v
  have hs : S.card = 5 - (H.degree v + 1) := by
    dsimp only [S]
    rw [Finset.card_compl, Finset.card_insert_of_notMem (H.notMem_neighborFinset_self v),
      H.card_neighborFinset_eq_degree, hV]
  have hb := clique_card_le_three H hd S hc
  exact ⟨S, by omega, hc⟩

end Paper.CliqueFiveNonneighbors
#print axioms Paper.CliqueFiveNonneighbors.adjacent
#print axioms Paper.CliqueFiveNonneighbors.clique
#print axioms Paper.CliqueFiveNonneighbors.clique_card_le_three
#print axioms Paper.CliqueFiveNonneighbors.low_degree_triangle
