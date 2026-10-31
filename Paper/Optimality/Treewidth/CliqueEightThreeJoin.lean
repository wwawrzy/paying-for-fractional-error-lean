import Paper.Optimality.Treewidth.CliqueEightCanonicalTransfer
namespace Paper.CliqueEightThreeJoin
open SimpleGraph CliqueTwoContractions
def template : SimpleGraph (Fin 8) where
  Adj u v := (u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val) ∨
    (u=3 ∧ (v=4 ∨ v=5)) ∨ (v=3 ∧ (u=4 ∨ u=5))
  symm := by intro u v h; aesop
  loopless := ⟨by intro u h; rcases h with h | h | h | h <;> rcases h with ⟨h1,h2⟩ <;> omega⟩
instance : DecidableRel template.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
theorem template_minor : (punctured 4 5).IsMinor template := by
  apply CliqueTwoContractions.minor template (Equiv.refl (Fin 8)) 4 5
  · decide
  · decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [punctured,blocks,template] at hij ⊢

theorem transfer {V : Type} (G : SimpleGraph V) (e : Fin 8 ↪ V)
    (hcross : ∀ i j : Fin 8, i.val < 3 → 3 ≤ j.val → G.Adj (e i) (e j))
    (h34 : G.Adj (e 3) (e 4)) (h35 : G.Adj (e 3) (e 5)) :
    (punctured 4 5).IsMinor G := by
  have hcopy : template.IsMinor G := by
    refine ⟨{
      branchSet := fun i => {e i}
      nonempty := fun _ => Set.singleton_nonempty _
      disjoint := fun i j hij => by
        rw [Set.disjoint_singleton]
        exact fun hh => hij (e.injective hh)
      connected := fun i => (MinorModel.refl G).connected (e i)
      adjacent := ?_ }⟩
    intro i j hij
    refine ⟨e i,rfl,e j,rfl,?_⟩
    rcases hij with ⟨hi,hj⟩ | ⟨hj,hi⟩ | ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl | rfl⟩
    · exact hcross i j hi hj
    · exact (hcross j i hj hi).symm
    · exact h34
    · exact h35
    · exact h34.symm
    · exact h35.symm
  exact template_minor.trans hcopy
end Paper.CliqueEightThreeJoin
#print axioms Paper.CliqueEightThreeJoin.template_minor
#print axioms Paper.CliqueEightThreeJoin.transfer
