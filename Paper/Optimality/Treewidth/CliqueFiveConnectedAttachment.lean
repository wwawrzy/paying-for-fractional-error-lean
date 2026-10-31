import Paper.Optimality.Treewidth.CliqueTwoContractions

/-! A connected branch disjoint from a five-clique and touching all but
at most one of its vertices gives an actual punctured six-clique minor. -/
namespace Paper.CliqueFiveConnectedAttachment
open SimpleGraph CliqueTwoContractions
variable {V : Type} (G : SimpleGraph V) (e : Fin 5 ↪ V) (X : Set V)

def blocks : Fin 6 → Set V := Fin.cases X (fun a => {e a})

theorem minor (missing : Fin 5) (hX : (G.induce X).Connected)
    (houtside : ∀ a, e a ∉ X)
    (hclique : ∀ a b, a ≠ b → G.Adj (e a) (e b))
    (htouch : ∀ a, a ≠ missing → ∃ x ∈ X, G.Adj x (e a)) :
    (punctured 0 missing.succ).IsMinor G := by
  classical
  refine ⟨{
    branchSet := blocks e X
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    adjacent := ?_
  }⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
    · obtain ⟨⟨x, hx⟩⟩ := hX.nonempty
      exact ⟨x, hx⟩
    · exact ⟨e a, rfl⟩
  · intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
    · exact False.elim (hij rfl)
    · change Disjoint X {e b}
      exact Set.disjoint_singleton_right.mpr (houtside b)
    · change Disjoint {e a} X
      exact Set.disjoint_singleton_left.mpr (houtside a)
    · change Disjoint {e a} {e b}
      simp only [Set.disjoint_singleton]
      exact fun h => hij (congrArg Fin.succ (e.injective h))
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
    · exact hX
    · exact (MinorModel.refl G).connected (e a)
  · intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
    · exact False.elim (hij.1 rfl)
    · have hb : b ≠ missing := fun h => hij.2 (Or.inl ⟨rfl, congrArg Fin.succ h⟩)
      obtain ⟨x, hx, hxb⟩ := htouch b hb
      exact ⟨x, hx, e b, rfl, hxb⟩
    · have ha : a ≠ missing := fun h => hij.2 (Or.inr ⟨congrArg Fin.succ h, rfl⟩)
      obtain ⟨x, hx, hxa⟩ := htouch a ha
      exact ⟨e a, rfl, x, hx, hxa.symm⟩
    · exact ⟨e a, rfl, e b, rfl,
        hclique a b (fun h => hij.1 (congrArg Fin.succ h))⟩

theorem minor_of_four_contacts (T : Finset (Fin 5)) (hT : 4 ≤ T.card)
    (hX : (G.induce X).Connected) (houtside : ∀ a, e a ∉ X)
    (hclique : ∀ a b, a ≠ b → G.Adj (e a) (e b))
    (htouch : ∀ a ∈ T, ∃ x ∈ X, G.Adj x (e a)) :
    ∃ p q : Fin 6, p ≠ q ∧ (punctured p q).IsMinor G := by
  classical
  have hc : Tᶜ.card ≤ 1 := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  have hm : ∃ missing : Fin 5, ∀ a, a ≠ missing → a ∈ T := by
    by_cases hn : Tᶜ.Nonempty
    · obtain ⟨missing, hmissing⟩ := hn
      refine ⟨missing, fun a ha => ?_⟩
      by_contra hnot
      exact ha (Finset.card_le_one_iff.mp hc (Finset.mem_compl.mpr hnot) hmissing)
    · exact ⟨0, fun a _ => by
        by_contra hnot
        exact hn ⟨a, Finset.mem_compl.mpr hnot⟩⟩
  obtain ⟨missing, hm⟩ := hm
  refine ⟨0, missing.succ, ?_, minor G e X missing hX houtside hclique ?_⟩
  · exact Fin.succ_ne_zero missing |>.symm
  · intro a ha
    exact htouch a (hm a ha)

theorem minor_of_small_attachment [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : Finset V) (hC : (G.induce (C : Set V)).Connected) (hsmall : C.card ≤ 2)
    (houtside : ∀ a, e a ∉ C)
    (hclique : ∀ a b, a ≠ b → G.Adj (e a) (e b))
    (hd : ∀ x ∈ C, 5 ≤ G.degree x)
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ ∃ a, y = e a) :
    ∃ p q : Fin 6, p ≠ q ∧ (punctured p q).IsMinor G := by
  classical
  obtain ⟨⟨x, hx⟩⟩ := hC.nonempty
  let T : Finset (Fin 5) := Finset.univ.filter (fun a => G.Adj x (e a))
  have hsub : G.neighborFinset x ⊆ T.image e ∪ C.erase x := by
    intro y hy
    have hxy : G.Adj x y := by simpa only [mem_neighborFinset] using hy
    rcases hclosed x hx y hxy with hyC | ⟨a, rfl⟩
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxy.ne.symm, hyC⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩)
  have hbound : G.degree x ≤ T.card + (C.card - 1) := by
    calc
      G.degree x = (G.neighborFinset x).card := rfl
      _ ≤ (T.image e ∪ C.erase x).card := Finset.card_le_card hsub
      _ ≤ (T.image e).card + (C.erase x).card := Finset.card_union_le _ _
      _ ≤ T.card + (C.card - 1) := by
        rw [Finset.card_erase_of_mem hx]
        exact Nat.add_le_add_right (Finset.card_image_le) _
  have hT : 4 ≤ T.card := by
    have := hd x hx
    omega
  apply minor_of_four_contacts G e (C : Set V) T hT hC houtside hclique
  intro a ha
  exact ⟨x, hx, (Finset.mem_filter.mp ha).2⟩

end Paper.CliqueFiveConnectedAttachment
#print axioms Paper.CliqueFiveConnectedAttachment.minor
#print axioms Paper.CliqueFiveConnectedAttachment.minor_of_four_contacts
#print axioms Paper.CliqueFiveConnectedAttachment.minor_of_small_attachment
