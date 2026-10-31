import Paper.Optimality.Treewidth.CliqueTwoContractions

/-! A six-vertex graph with at least fourteen actual edges contains a
spanning K6 minus one edge. The missing unordered edge is selected from
the genuine difference of edge sets; no minor certificate is assumed. -/
namespace Paper.CliqueNearComplete

open SimpleGraph CliqueTwoContractions

theorem punctured_subgraph (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj]
    (hcard : 14 ≤ H.edgeFinset.card) :
    ∃ p q : Fin 6, p ≠ q ∧ punctured p q ≤ H := by
  classical
  let M : Finset (Sym2 (Fin 6)) := (⊤ : SimpleGraph (Fin 6)).edgeFinset \ H.edgeFinset
  have hsub : H.edgeFinset ⊆ (⊤ : SimpleGraph (Fin 6)).edgeFinset := edgeFinset_mono le_top
  have htop : (⊤ : SimpleGraph (Fin 6)).edgeFinset.card = 15 := by
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    decide
  have hM : M.card ≤ 1 := by
    dsimp only [M]
    rw [Finset.card_sdiff_of_subset hsub, htop]
    omega
  have memM (a b : Fin 6) (hne : a ≠ b) (hnot : ¬H.Adj a b) : s(a, b) ∈ M := by
    apply Finset.mem_sdiff.mpr
    constructor
    · exact mem_edgeFinset.mpr hne
    · simpa only [mem_edgeFinset, mem_edgeSet] using hnot
  by_cases hne : M.Nonempty
  · obtain ⟨e, he⟩ := hne
    obtain ⟨p, q, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
    have hpq : p ≠ q := by
      have hh := (Finset.mem_sdiff.mp he).1
      exact mem_edgeFinset.mp hh
    refine ⟨p, q, hpq, ?_⟩
    intro a b hab
    by_contra hn
    have heq := Finset.card_le_one_iff.mp hM (memM a b hab.1 hn) he
    exact hab.2 (Sym2.eq_iff.mp heq)
  · refine ⟨0, 1, by decide, ?_⟩
    intro a b hab
    by_contra hn
    exact hne ⟨s(a, b), memM a b hab.1 hn⟩

end Paper.CliqueNearComplete

#print axioms Paper.CliqueNearComplete.punctured_subgraph
