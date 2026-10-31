import Paper.Optimality.Treewidth.CliqueTwoContractions

/-! Explicit punctured-six-clique minors for the complements of
C3 + C3 + P2 and C3 + C5. Classification is a separate obligation. -/
namespace Paper.CliqueEightCanonical
open SimpleGraph CliqueTwoContractions

def missing (five : Bool) : Finset (Sym2 (Fin 8)) :=
  if five then {s(0, 1), s(0, 2), s(1, 2), s(3, 4), s(4, 5), s(5, 6), s(6, 7), s(3, 7)}
  else {s(0, 1), s(0, 2), s(1, 2), s(3, 4), s(3, 5), s(4, 5), s(6, 7)}

def graph (five : Bool) : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ s(u, v) ∉ missing five
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    intro hn
    apply h.2
    rw [Sym2.eq_swap] at hn
    exact hn
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (five : Bool) : DecidableRel (graph five).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ ∉ missing five))

def labels (five : Bool) : Fin 8 ≃ Fin 8 where
  toFun := if five then ![0, 1, 2, 4, 6, 7, 3, 5] else ![0, 1, 2, 5, 6, 7, 3, 4]
  invFun := if five then ![0, 1, 2, 6, 3, 7, 4, 5] else ![0, 1, 2, 6, 7, 3, 4, 5]
  left_inv := by cases five <;> decide
  right_inv := by cases five <;> decide

set_option maxHeartbeats 1600000 in
theorem minor (five : Bool) : (punctured 4 5).IsMinor (graph five) := by
  apply CliqueTwoContractions.minor (graph five) (labels five) 4 5
  · cases five <;> decide
  · cases five <;> decide
  · cases five <;> intro i j hij <;> fin_cases i <;> fin_cases j <;>
      simp [punctured, blocks, labels, graph, missing, Sym2.eq_iff] at hij ⊢

end Paper.CliqueEightCanonical
#print axioms Paper.CliqueEightCanonical.minor
