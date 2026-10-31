import Paper.Optimality.Treewidth.CliqueThreeAttachment

/-! All connected attachments of at most three vertices to a five-clique. -/
namespace Paper.CliqueFiveAttachmentCases
open SimpleGraph CliqueTwoContractions
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem minor (e : Fin 5 ↪ V) (C : Finset V)
    (hC : (G.induce (C : Set V)).Connected) (hsmall : C.card ≤ 3)
    (houtside : ∀ a, e a ∉ C)
    (hclique : ∀ a b, a ≠ b → G.Adj (e a) (e b))
    (hd : ∀ x ∈ C, 5 ≤ G.degree x)
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ ∃ a, y = e a) :
    ∃ p q : Fin 6, p ≠ q ∧ (punctured p q).IsMinor G := by
  classical
  by_cases htwo : C.card ≤ 2
  · exact CliqueFiveConnectedAttachment.minor_of_small_attachment
      G e C hC htwo houtside hclique hd hclosed
  have hthree : C.card = 3 := by omega
  let T : Finset (Fin 5) := Finset.univ.filter (fun a => ∃ x ∈ C, G.Adj x (e a))
  by_cases hfour : 4 ≤ T.card
  · apply CliqueFiveConnectedAttachment.minor_of_four_contacts
      G e (C : Set V) T hfour hC houtside hclique
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  refine ⟨0, 1, by decide,
    CliqueThreeAttachment.punctured_minor G C (T.image e) hthree ?_ ?_ hd ?_⟩
  · have := Finset.card_image_le (s := T) (f := e)
    omega
  · intro x hx y hy hne
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    exact hclique a b (fun heq => hne (congrArg e heq))
  · intro x hx y hxy
    rcases hclosed x hx y hxy with hyC | ⟨a, rfl⟩
    · exact Finset.mem_union_left _ hyC
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hxy⟩, rfl⟩)

end Paper.CliqueFiveAttachmentCases
#print axioms Paper.CliqueFiveAttachmentCases.minor
