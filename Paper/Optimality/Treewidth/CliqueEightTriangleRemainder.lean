import Paper.Optimality.Treewidth.CliqueEightComplementTriangle

/-! Removing a closed triangle reduces the eight-vertex classification
to five vertices with independence number at most two. -/
namespace Paper.CliqueEightTriangleRemainder
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

theorem independent_bound (hd : ∀ x, H.degree x ≤ 2)
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 3)
    (S : Finset V) (hS : S.card = 3) (hclique : H.IsClique (S : Set V))
    (I : Finset V) (hI : I ⊆ Sᶜ) (hind : H.IsIndepSet (I : Set V)) :
    I.card ≤ 2 := by
  classical
  obtain ⟨d, hdS⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hdI : d ∉ I := fun hh => (Finset.mem_compl.mp (hI hh)) hdS
  have hno : ∀ w ∈ I, ¬H.Adj d w := by
    intro w hw hadj
    exact (Finset.mem_compl.mp (hI hw))
      (CliqueEightComplement.triangle_closed H hd S hS hclique d hdS w hadj)
  have hinsert : H.IsIndepSet ((insert d I : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact hind.insert_of_symmetric (fun _ _ hn h => hn h.symm) (fun w hw _ => hno w hw)
  have hb := hsmall (insert d I) hinsert
  rw [Finset.card_insert_of_notMem hdI] at hb
  omega

theorem partition (hV : Fintype.card V = 8) (hd : ∀ x, H.degree x ≤ 2)
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 3) :
    ∃ S : Finset V, S.card = 3 ∧ H.IsClique (S : Set V) ∧ Sᶜ.card = 5 ∧
      (∀ x ∈ S, ∀ y ∈ Sᶜ, ¬H.Adj x y) ∧
      (∀ I : Finset V, I ⊆ Sᶜ → H.IsIndepSet (I : Set V) → I.card ≤ 2) := by
  obtain ⟨S, hS, hclique⟩ := CliqueEightComplementTriangle.exists_triangle H hV hd hsmall
  refine ⟨S, hS, hclique, ?_, ?_, independent_bound H hd hsmall S hS hclique⟩
  · rw [Finset.card_compl, hV, hS]
  · intro x hx y hy hadj
    exact (Finset.mem_compl.mp hy)
      (CliqueEightComplement.triangle_closed H hd S hS hclique x hx y hadj)

end Paper.CliqueEightTriangleRemainder
#print axioms Paper.CliqueEightTriangleRemainder.independent_bound
#print axioms Paper.CliqueEightTriangleRemainder.partition
