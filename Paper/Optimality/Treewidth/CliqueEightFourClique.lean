import Paper.Optimality.Treewidth.CliqueEightBranchEdges
import Paper.Optimality.Treewidth.CliqueEightAttachments
import Paper.Optimality.Treewidth.CliqueEightFiveClique

/-! An actual punctured-K6 minor when an eight-vertex graph of minimum
 degree five has a four-clique and no outside vertex complete to it. -/
namespace Paper.CliqueEightFourClique
open SimpleGraph CliqueFourMatchings CliqueEightLabels CliqueTwoContractions
  CliqueEightBranchSets CliqueEightBranchEdges

private theorem index_cases : ∀ i : Fin 6,
    (∃ s : Bool, i = pairIndex s) ∨ ∃ a : Fin 4, i = rowIndex a := by decide

private theorem allowed (a b : Fin 4) (missing side : Bool)
    (h : (punctured (rowIndex a) (pairIndex missing)).Adj (rowIndex b) (pairIndex side)) :
    b ≠ a ∨ side ≠ missing := by
  by_cases hb : b = a
  · exact Or.inr (fun hs => h.2 (Or.inl ⟨congrArg rowIndex hb, congrArg pairIndex hs⟩))
  · exact Or.inl hb

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (S : Finset V) (eS : Fin 4 ≃ (S : Set V))
  (eR : Fin 4 ≃ ((Sᶜ : Finset V) : Set V))

include eS eR in
theorem minor (hV : Fintype.card V = 8) (hcard : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x) (hclique : G.IsClique (S : Set V))
    (hno : ∀ x ∈ Sᶜ, ¬∀ y ∈ S, G.Adj x y) :
    ∃ a : Fin 4, ∃ missing : Bool,
      (punctured (rowIndex a) (pairIndex missing)).IsMinor G := by
  classical
  obtain ⟨k, h06, h17, hcross, a, missing, hatt⟩ :=
    CliqueEightAttachments.choose_edges G S eS eR hV hcard hd hno
  refine ⟨a, missing, CliqueTwoContractions.minor G (labeling S eS eR k)
    (rowIndex a) (pairIndex missing) ?_ ?_ ?_⟩
  · simpa only [zero, six] using h06
  · simpa only [CliqueEightLabels.one, seven] using h17
  · intro i j hij
    change Linked G S eS eR k i j
    rcases index_cases i with ⟨s, rfl⟩ | ⟨b, rfl⟩ <;>
      rcases index_cases j with ⟨t, rfl⟩ | ⟨c, rfl⟩
    · cases s <;> cases t
      · exact False.elim (hij.1 rfl)
      · exact pairs G S eS eR k hcross
      · exact linked_symm G S eS eR (pairs G S eS eR k hcross)
      · exact False.elim (hij.1 rfl)
    · exact linked_symm G S eS eR
        (row_pair G S eS eR k c s (hatt c s (allowed a c missing s hij.symm)))
    · exact row_pair G S eS eR k b t (hatt b t (allowed a b missing t hij))
    · exact rows G S eS eR k b c (fun hbc => hij.1 (congrArg rowIndex hbc)) hclique

/-- The graph-theoretic form needs no supplied enumeration of either side. -/
theorem exists_minor (hV : Fintype.card V = 8) (hcard : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x) (hclique : G.IsClique (S : Set V))
    (hno : ∀ x ∈ Sᶜ, ¬∀ y ∈ S, G.Adj x y) :
    ∃ p q : Fin 6, p ≠ q ∧ (punctured p q).IsMinor G := by
  classical
  have enum (T : Finset V) (hT : T.card = 4) : Nonempty (Fin 4 ≃ (T : Set V)) := by
    have htype : Fintype.card (T : Set V) = 4 := by
      simpa only [Fintype.card_eq_nat_card, Finset.coe_sort_coe,
        Nat.card_eq_finsetCard] using hT
    exact ⟨Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using htype.symm)⟩
  obtain ⟨fS⟩ := enum S hcard
  obtain ⟨fR⟩ := enum Sᶜ (by simp only [Finset.card_compl, hV, hcard])
  obtain ⟨a, missing, hm⟩ := minor G S fS fR hV hcard hd hclique hno
  refine ⟨rowIndex a, pairIndex missing, ?_, hm⟩
  cases missing <;> simp only [rowIndex, pairIndex, Bool.false_eq_true, if_false, if_true]
  all_goals intro heq; have he := congrArg Fin.val heq; simp only at he; omega

/-- Every four-clique suffices, including those extending to five-cliques. -/
theorem unrestricted (hV : Fintype.card V = 8) (hcard : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x) (hclique : G.IsClique (S : Set V)) :
    ∃ p q : Fin 6, p ≠ q ∧ (punctured p q).IsMinor G := by
  classical
  by_cases hno : ∀ x ∈ Sᶜ, ¬∀ y ∈ S, G.Adj x y
  · exact exists_minor G S hV hcard hd hclique hno
  push Not at hno
  obtain ⟨x, hx, hcomplete⟩ := hno
  have hxS : x ∉ S := Finset.mem_compl.mp hx
  apply CliqueEightFiveClique.minor G hV (insert x S)
  · rw [Finset.card_insert_of_notMem hxS, hcard]
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | haS
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact False.elim (hab rfl)
      · exact hcomplete b hbS
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact (hcomplete a haS).symm
      · exact hclique haS hbS hab
  · exact hd

end Paper.CliqueEightFourClique
#print axioms Paper.CliqueEightFourClique.minor
#print axioms Paper.CliqueEightFourClique.exists_minor
#print axioms Paper.CliqueEightFourClique.unrestricted
