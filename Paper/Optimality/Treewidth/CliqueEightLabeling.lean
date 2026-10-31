import Paper.Optimality.Treewidth.CliqueFiveMissingMatching
import Paper.Optimality.Treewidth.CliqueEightComplementCounts
namespace Paper.CliqueEightLabeling
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem labels (hcard : Fintype.card V = 8) (u : V) (hu : G.degree u = 5)
    (hd : ∀ z, ((G.induce (G.neighborSet u))ᶜ).degree z ≤ 1)
    (he : ((G.induce (G.neighborSet u))ᶜ).edgeFinset.card = 2) :
    ∃ e : Fin 8 ≃ V, e 0 = u ∧
      (∀ x, (x ≠ u ∧ ¬G.Adj u x) ↔ x = e 1 ∨ x = e 2) ∧
      (∀ i : Fin 5, G.Adj u (e ⟨i.val+3,by omega⟩)) ∧
      (∀ i j : Fin 5, (i ≠ j ∧ ¬G.Adj (e ⟨i.val+3,by omega⟩) (e ⟨j.val+3,by omega⟩)) ↔
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
  classical
  have hn : Fintype.card (G.neighborSet u) = 5 := by rw [G.card_neighborSet_eq_degree,hu]
  obtain ⟨n,hnedges⟩ := CliqueFiveMissingMatching.five_normal_form ((G.induce (G.neighborSet u))ᶜ) hn hd he
  obtain ⟨a,b,hab,houtside⟩ := CliqueEightComplementCounts.two_nonneighbors G hcard u hu
  have ha := (houtside a).mpr (Or.inl rfl)
  have hb := (houtside b).mpr (Or.inr rfl)
  let q : Fin 5 → V := fun i => (n i).val
  have hq : Function.Injective q := Subtype.val_injective.comp n.injective
  have hqu : ∀ i, q i ≠ u := by
    intro i hi
    have hh := (n i).property
    change G.Adj u (q i) at hh
    rw [hi] at hh
    exact G.irrefl hh
  have hqa : ∀ i, q i ≠ a := by
    intro i hi
    have hh := (n i).property
    change G.Adj u (q i) at hh
    exact ha.2 (hi ▸ hh)
  have hqb : ∀ i, q i ≠ b := by
    intro i hi
    have hh := (n i).property
    change G.Adj u (q i) at hh
    exact hb.2 (hi ▸ hh)
  let f : Fin 8 → V := ![u,a,b,q 0,q 1,q 2,q 3,q 4]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij
    all_goals first
      | rfl
      | exact (ha.1 hij).elim
      | exact (ha.1 hij.symm).elim
      | exact (hb.1 hij).elim
      | exact (hb.1 hij.symm).elim
      | exact (hab hij).elim
      | exact (hab hij.symm).elim
      | exact (hqu _ hij).elim
      | exact (hqu _ hij.symm).elim
      | exact (hqa _ hij).elim
      | exact (hqa _ hij.symm).elim
      | exact (hqb _ hij).elim
      | exact (hqb _ hij.symm).elim
      | have hh := hq hij; contradiction
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simpa using hcard.symm⟩)
  refine ⟨e,by rfl,?_,?_,?_⟩
  · simpa [e,f] using houtside
  · intro i
    fin_cases i <;> change G.Adj u (q _) <;> exact (n _).property
  · intro i j
    have hval : ∀ k : Fin 5, e ⟨k.val+3,by omega⟩ = (n k).val := by
      intro k
      fin_cases k <;> rfl
    rw [hval,hval]
    have hh := hnedges i j
    simpa only [SimpleGraph.compl_adj,SimpleGraph.induce_adj,n.injective.ne_iff] using hh
end Paper.CliqueEightLabeling
