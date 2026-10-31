import Paper.Optimality.Treewidth.CliqueStarProjection
import Mathlib.Tactic.FinCases

/-! A concrete six-branch minor certificate on eight vertices. Two actual
disjoint edges are contracted and four vertices are retained. This fixes
the witness shape for the bounded minimum-degree-five structural problem;
no assertion that every graph admits the certificate is made here. -/
namespace Paper.CliqueTwoContractions

open SimpleGraph

def punctured (p q : Fin 6) : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ ¬(i = p ∧ j = q ∨ i = q ∧ j = p)
  symm := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    rintro (⟨hj, hi⟩ | ⟨hj, hi⟩)
    · exact hij.2 (Or.inr ⟨hi, hj⟩)
    · exact hij.2 (Or.inl ⟨hi, hj⟩)
  loopless := ⟨fun _ h => h.1 rfl⟩

def blocks {V : Type} (e : Fin 8 ≃ V) (i : Fin 6) : Set V :=
  if i = 0 then {e 0, e 6} else if i = 1 then {e 1, e 7} else {e (i.castLE (by decide))}

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem pair_connected (a b : V) (hab : G.Adj a b) :
    (G.induce ({a, b} : Set V)).Connected := by
  have hh := connected_induce_union ((MinorModel.refl G).connected a).preconnected
    ((MinorModel.refl G).connected b).preconnected
    (Set.mem_singleton a) (Set.mem_singleton b) hab
  simpa only [Set.singleton_union] using hh

private theorem singleton_connected (a : V) : (G.induce ({a} : Set V)).Connected :=
  (MinorModel.refl G).connected a

theorem minor (e : Fin 8 ≃ V) (p q : Fin 6)
    (h06 : G.Adj (e 0) (e 6)) (h17 : G.Adj (e 1) (e 7))
    (hcross : ∀ i j, (punctured p q).Adj i j →
      ∃ a ∈ blocks e i, ∃ b ∈ blocks e j, G.Adj a b) :
    (punctured p q).IsMinor G := by
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

end Paper.CliqueTwoContractions

#print axioms Paper.CliqueTwoContractions.minor
