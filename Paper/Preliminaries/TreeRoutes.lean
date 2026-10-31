import Paper.Preliminaries.LeaderTreeCorrect

/-! Physical root routes follow from the specification already proved
for actual tree execution; no diameter or path oracle is supplied here. -/
namespace Paper.TreeRoutes
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}
variable {active : V → Bool} {D : ℕ} {root : V} {nodes : V → ParentElection.Node V D}

theorem routes (h : LeaderTreeCorrect.Spec G active D root nodes) {v : V}
    (ha : active v = true) :
    ∃ p : G.Walk v root, p.length ≤ D ∧ ∀ z ∈ p.support, active z = true := by
  have go : ∀ n, ∀ v, (nodes v).rank.val = n → active v = true →
      ∃ p : G.Walk v root, p.length ≤ n ∧ ∀ z ∈ p.support, active z = true := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hva
      by_cases hr : v = root
      · subst v
        exact ⟨.nil, Nat.zero_le _, by simpa using hva⟩
      · obtain ⟨u, hu⟩ := h.parent_exists v hva hr
        have hsmall : (nodes u).rank.val < n := by rw [← hv]; exact h.parent_rank v u hu
        obtain ⟨p, hp, hpa⟩ := ih _ hsmall u rfl (h.parent_active v u hu).2
        refine ⟨.cons (h.parent_edge v u hu) p, ?_, ?_⟩
        · simp only [SimpleGraph.Walk.length_cons]
          omega
        · intro z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hva
          · exact hpa z hz
  obtain ⟨p, hp, hpa⟩ := go _ v rfl ha
  exact ⟨p, hp.trans (h.rank_bound v ha), hpa⟩
end Paper.TreeRoutes
