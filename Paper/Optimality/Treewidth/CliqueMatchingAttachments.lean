import Paper.Optimality.Treewidth.CliqueFourMatchingChoice

/-! Turn a matching with one deficient attachment row into a single
possible missing branch pair. Both endpoints of that possible missing
edge are explicit; every other required attachment has a real witness. -/
namespace Paper.CliqueMatchingAttachments

open CliqueFourMatchings CliqueFourMatchingChoice

private theorem part_complement : ∀ k side, (part k side)ᶜ = part k (!side) := by decide

theorem touch (T : Finset (Fin 4)) (hT : 2 ≤ T.card) (k : Fin 3) (side : Bool)
    (hne : T ≠ part k (!side)) : (T ∩ part k side).Nonempty := by
  by_contra hn
  have hsub : T ⊆ part k (!side) := by
    intro x hx
    have hnot : x ∉ part k side := fun hh => hn ⟨x, Finset.mem_inter.mpr ⟨hx, hh⟩⟩
    have hc : x ∈ (part k side)ᶜ := Finset.mem_compl.mpr hnot
    rw [part_complement] at hc
    exact hc
  apply hne
  exact Finset.eq_of_subset_of_card_le hsub (by rw [part_card]; exact hT)

theorem touch_of_not_bad (N : Fin 4 → Finset (Fin 4)) (hN : ∀ a, 2 ≤ (N a).card)
    (k : Fin 3) (a : Fin 4) (ha : a ∉ bad N k) (side : Bool) :
    (N a ∩ part k side).Nonempty := by
  have hn : ¬(N a = part k false ∨ N a = part k true) := by
    intro hh
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
  apply touch (N a) (hN a) k side
  intro hh
  cases side with
  | false => exact hn (Or.inr hh)
  | true => exact hn (Or.inl hh)

theorem single_missing (N : Fin 4 → Finset (Fin 4)) (hN : ∀ a, 2 ≤ (N a).card)
    (k : Fin 3) (hbad : (bad N k).card ≤ 1) :
    ∃ a : Fin 4, ∃ missing : Bool, ∀ b : Fin 4, ∀ side : Bool,
      b ≠ a ∨ side ≠ missing → (N b ∩ part k side).Nonempty := by
  classical
  by_cases hn : (bad N k).Nonempty
  · obtain ⟨a, ha⟩ := hn
    have hother : ∀ b, b ≠ a → b ∉ bad N k := by
      intro b hba hb
      exact hba (Finset.card_le_one_iff.mp hbad hb ha)
    have hrow := (Finset.mem_filter.mp ha).2
    rcases hrow with hleft | hright
    · refine ⟨a, true, ?_⟩
      intro b side hgood
      by_cases hba : b = a
      · subst b
        cases side with
        | false =>
          rw [hleft, Finset.inter_self]
          exact Finset.card_pos.mp (by rw [part_card]; decide)
        | true => exact False.elim ((hgood.resolve_left (fun hh => hh rfl)) rfl)
      · exact touch_of_not_bad N hN k b (hother b hba) side
    · refine ⟨a, false, ?_⟩
      intro b side hgood
      by_cases hba : b = a
      · subst b
        cases side with
        | false => exact False.elim ((hgood.resolve_left (fun hh => hh rfl)) rfl)
        | true =>
          rw [hright, Finset.inter_self]
          exact Finset.card_pos.mp (by rw [part_card]; decide)
      · exact touch_of_not_bad N hN k b (hother b hba) side
  · refine ⟨0, false, ?_⟩
    intro b side _
    exact touch_of_not_bad N hN k b (fun hb => hn ⟨b, hb⟩) side

end Paper.CliqueMatchingAttachments

#print axioms Paper.CliqueMatchingAttachments.touch
#print axioms Paper.CliqueMatchingAttachments.touch_of_not_bad
#print axioms Paper.CliqueMatchingAttachments.single_missing
