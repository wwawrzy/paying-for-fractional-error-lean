import Paper.Optimality.Treewidth.CliqueTwoContractions
namespace Paper.CliqueCompleteTwoContractions
open SimpleGraph CliqueTwoContractions
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private theorem pair_connected (a b : V) (hab : G.Adj a b) :
    (G.induce ({a, b} : Set V)).Connected := by
  have hh := connected_induce_union ((MinorModel.refl G).connected a).preconnected
    ((MinorModel.refl G).connected b).preconnected
    (Set.mem_singleton a) (Set.mem_singleton b) hab
  simpa only [Set.singleton_union] using hh

private theorem singleton_connected (a : V) : (G.induce ({a} : Set V)).Connected :=
  (MinorModel.refl G).connected a

theorem complete_minor (e : Fin 8 ≃ V)
    (h06 : G.Adj (e 0) (e 6)) (h17 : G.Adj (e 1) (e 7))
    (hcross : ∀ i j, (completeGraph (Fin 6)).Adj i j →
      ∃ a ∈ blocks e i, ∃ b ∈ blocks e j, G.Adj a b) :
    (completeGraph (Fin 6)).IsMinor G := by
  classical
  refine ⟨{
    branchSet := blocks e
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    adjacent := hcross
  }⟩
  · intro i
    fin_cases i <;> simp [blocks]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [blocks, Set.disjoint_left, Equiv.apply_eq_iff_eq] at hij ⊢
  · intro i
    fin_cases i
    · simpa [blocks] using pair_connected G (e 0) (e 6) h06
    · simpa [blocks] using pair_connected G (e 1) (e 7) h17
    · simpa [blocks] using singleton_connected G (e 2)
    · simpa [blocks] using singleton_connected G (e 3)
    · simpa [blocks] using singleton_connected G (e 4)
    · simpa [blocks] using singleton_connected G (e 5)

end Paper.CliqueCompleteTwoContractions
