import Paper.Optimality.Treewidth.CliqueFiveAttachmentCases
import Paper.Optimality.Treewidth.CliqueComponentBoundary

/-! The five-clique case for eight vertices of minimum degree five. -/
namespace Paper.CliqueEightFiveClique
open SimpleGraph CliqueTwoContractions CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem minor (hV : Fintype.card V = 8) (S : Finset V) (hS : S.card = 5)
    (hclique : G.IsClique (S : Set V)) (hd : ∀ x, 5 ≤ G.degree x) :
    ∃ p q : Fin 6, p ≠ q ∧ (punctured p q).IsMinor G := by
  classical
  have hR : Sᶜ.card = 3 := by rw [Finset.card_compl, hV, hS]
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < Sᶜ.card by omega)
  have hzS : z ∉ (S : Set V) := Finset.mem_compl.mp hz
  let K := (G.induce (S : Set V)ᶜ).connectedComponentMk ⟨z, hzS⟩
  let X := outside G (S : Set V) K
  let C : Finset V := X.toFinset
  have hCX : (C : Set V) = X := Set.coe_toFinset X
  have hconn : (G.induce (C : Set V)).Connected := by
    rw [hCX]
    exact outside_connected G (S : Set V) K
  have hsub : C ⊆ Sᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr
      (outside_subset G (S : Set V) K (Set.mem_toFinset.mp hx))
  have hsmall : C.card ≤ 3 := by
    have := Finset.card_le_card hsub
    omega
  have htype : Fintype.card (S : Set V) = 5 := by
    simpa only [Fintype.card_eq_nat_card, Finset.coe_sort_coe,
      Nat.card_eq_finsetCard] using hS
  let f : Fin 5 ≃ (S : Set V) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using htype.symm)
  let e : Fin 5 ↪ V := ⟨fun a => (f a).val, fun _ _ h => f.injective (Subtype.ext h)⟩
  apply CliqueFiveAttachmentCases.minor G e C hconn hsmall
  · intro a ha
    exact (Finset.mem_compl.mp (hsub ha)) (f a).property
  · intro a b hab
    exact hclique (f a).property (f b).property (fun heq => hab (e.injective heq))
  · intro x _
    exact hd x
  · intro x hx y hxy
    by_cases hy : y ∈ C
    · exact Or.inl hy
    · have hyS : y ∈ (S : Set V) := outside_boundary G (S : Set V) K x
        (Set.mem_toFinset.mp hx) y (fun hh => hy (Set.mem_toFinset.mpr hh)) hxy
      exact Or.inr ⟨f.symm ⟨y, hyS⟩,
        (congrArg Subtype.val (f.apply_symm_apply ⟨y, hyS⟩)).symm⟩

end Paper.CliqueEightFiveClique
#print axioms Paper.CliqueEightFiveClique.minor
