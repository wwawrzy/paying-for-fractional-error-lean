import Paper.Optimality.Treewidth.CliqueFiveRegular

/-! The crossing edges between the two pairs in the regular five-vertex
case contain a perfect matching. -/
namespace Paper.CliqueFiveCrossMatching
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

theorem two_neighbors (v a b : V) (hd : H.degree v ≤ 2)
    (ha : H.Adj v a) (hb : H.Adj v b) (hab : a ≠ b) :
    H.neighborFinset v = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hx
    · rw [hxa]
      exact (H.mem_neighborFinset v a).mpr ha
    · have := Finset.mem_singleton.mp hx
      subst x
      exact (H.mem_neighborFinset v b).mpr hb
  · rw [H.card_neighborFinset_eq_degree, Finset.card_pair hab]
    exact hd

private theorem other_pair (v a b c d : V) (hd : 2 ≤ H.degree a)
    (hcover : ∀ z, z = v ∨ z = a ∨ z = b ∨ z = c ∨ z = d)
    (hn : ¬H.Adj a b) : H.Adj a c ∨ H.Adj a d := by
  by_contra hh
  have hsub : H.neighborFinset a ⊆ {v} := by
    intro z hz
    have haz := (H.mem_neighborFinset a z).mp hz
    rcases hcover z with hz | hz | hz | hz | hz
    · exact Finset.mem_singleton.mpr hz
    · exact False.elim (H.loopless.irrefl a (hz ▸ haz))
    · exact False.elim (hn (hz ▸ haz))
    · exact False.elim (hh (Or.inl (hz ▸ haz)))
    · exact False.elim (hh (Or.inr (hz ▸ haz)))
  have hb := Finset.card_le_card hsub
  rw [H.card_neighborFinset_eq_degree, Finset.card_singleton] at hb
  omega

theorem matching (e : Fin 5 ≃ V) (hd : ∀ x, H.degree x = 2)
    (h34 : H.Adj (e 3) (e 4)) (hn12 : ¬H.Adj (e 1) (e 2)) :
    (H.Adj (e 1) (e 3) ∧ H.Adj (e 2) (e 4)) ∨
      (H.Adj (e 1) (e 4) ∧ H.Adj (e 2) (e 3)) := by
  have hcover : ∀ z, z = e 0 ∨ z = e 1 ∨ z = e 2 ∨ z = e 3 ∨ z = e 4 := by
    intro z
    obtain ⟨i, rfl⟩ := e.surjective z
    fin_cases i <;> simp
  have h1 := other_pair H (e 0) (e 1) (e 2) (e 3) (e 4) (hd _).ge hcover hn12
  have h2 := other_pair H (e 0) (e 2) (e 1) (e 3) (e 4) (hd _).ge
    (fun z => by rcases hcover z with h | h | h | h | h <;> tauto)
    (fun h => hn12 h.symm)
  have ne (i j : Fin 5) (hij : i ≠ j) : e i ≠ e j := fun h => hij (e.injective h)
  rcases h1 with h13 | h14
  · have hN := two_neighbors H (e 3) (e 1) (e 4) (hd _).le h13.symm h34 (ne 1 4 (by decide))
    have hn23 : ¬H.Adj (e 2) (e 3) := by
      intro h
      have hm := (H.mem_neighborFinset (e 3) (e 2)).mpr h.symm
      rw [hN] at hm
      simpa [ne 2 1 (by decide), ne 2 4 (by decide)] using hm
    exact Or.inl ⟨h13, h2.resolve_left hn23⟩
  · have hN := two_neighbors H (e 4) (e 1) (e 3) (hd _).le h14.symm h34.symm (ne 1 3 (by decide))
    have hn24 : ¬H.Adj (e 2) (e 4) := by
      intro h
      have hm := (H.mem_neighborFinset (e 4) (e 2)).mpr h.symm
      rw [hN] at hm
      simpa [ne 2 1 (by decide), ne 2 3 (by decide)] using hm
    exact Or.inr ⟨h14, h2.resolve_right hn24⟩

end Paper.CliqueFiveCrossMatching
#print axioms Paper.CliqueFiveCrossMatching.two_neighbors
#print axioms Paper.CliqueFiveCrossMatching.matching
