import Paper.Optimality.Treewidth.CliqueEightResidualRows
namespace Paper.CliqueEightActualTemplate
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem exists_template (hcard : Fintype.card V = 8) (hedges : G.edgeFinset.card = 22)
    (hmin : ∀ v, 5 ≤ G.degree v) (u : V) (hu : G.degree u = 5)
    (hd : ∀ z, ((G.induce (G.neighborSet u))ᶜ).degree z ≤ 1)
    (he : ((G.induce (G.neighborSet u))ᶜ).edgeFinset.card = 2) :
    ∃ a b : Fin 5, Nonempty (G ≃g CliqueEightResidualTemplates.graph a b) := by
  classical
  obtain ⟨e,he0,hnon,hn,hpattern⟩ := CliqueEightLabeling.labels G hcard u hu hd he
  let H := Gᶜ.comap e.toEmbedding
  let iso : H ≃g Gᶜ := Iso.comap e Gᶜ
  have hdeg : ∀ i, H.degree i ≤ 2 := by
    intro i
    rw [← iso.degree_eq i]
    exact CliqueEightComplementCounts.degree_le_two G hcard hmin (iso i)
  have hcount : H.edgeFinset.card = 6 := by
    rw [iso.card_edgeFinset_eq]
    exact CliqueEightComplementCounts.edge_count G hcard hedges
  have hroot : ∀ j, H.Adj 0 j ↔ j = 1 ∨ j = 2 := by
    intro j
    change (e 0 ≠ e j ∧ ¬G.Adj (e 0) (e j)) ↔ _
    simpa only [he0,ne_comm,e.injective.eq_iff] using hnon (e j)
  have hN : ∀ i j : Fin 8, 3 ≤ i.val → 3 ≤ j.val →
      (H.Adj i j ↔ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5)) := by
    intro i j hi hj
    let k : Fin 5 := ⟨i.val-3,by omega⟩
    let l : Fin 5 := ⟨j.val-3,by omega⟩
    have hk : (⟨k.val+3,by omega⟩ : Fin 8) = i := by apply Fin.ext; dsimp [k]; omega
    have hl : (⟨l.val+3,by omega⟩ : Fin 8) = j := by apply Fin.ext; dsimp [l]; omega
    have hh := hpattern k l
    rw [hk,hl] at hh
    change (e i ≠ e j ∧ ¬G.Adj (e i) (e j)) ↔ _
    rw [e.injective.ne_iff]
    simp only [Fin.ext_iff,ne_eq] at hh ⊢
    dsimp [k,l] at hh
    fin_cases i <;> (try fin_cases j) <;> (try norm_num at hi hj hh ⊢) <;> tauto
  obtain ⟨a,b,hab⟩ := CliqueEightResidualRows.template H hdeg hcount hroot hN
  refine ⟨a,b,⟨{ toEquiv := e.symm, map_rel_iff' := ?_ }⟩⟩
  intro x y
  have hxy := congrArg (fun K : SimpleGraph (Fin 8) => K.Adj (e.symm x) (e.symm y)) hab
  change ((CliqueEightResidualTemplates.graph a b).Adj (e.symm x) (e.symm y) ↔ G.Adj x y)
  have hx : e (e.symm x) = x := e.apply_symm_apply x
  have hy : e (e.symm y) = y := e.apply_symm_apply y
  change (Gᶜ.Adj (e (e.symm x)) (e (e.symm y))) = _ at hxy
  rw [hx,hy] at hxy
  simp only [compl_adj] at hxy
  by_cases h : x = y
  · subst y
    simp
  · have h' : e.symm x ≠ e.symm y := e.symm.injective.ne h
    tauto
private theorem minor_of_iso {W : Type} {F : SimpleGraph W} (e : F ≃g G) : F.IsMinor G := by
  refine ⟨{
    branchSet := fun x => {e x}
    nonempty := fun x => ⟨e x,rfl⟩
    disjoint := ?_
    connected := ?_
    adjacent := ?_ }⟩
  · intro x y hxy
    rw [Set.disjoint_singleton]
    exact e.injective.ne hxy
  · intro x
    rw [connected_iff_exists_forall_reachable]
    exact ⟨⟨e x,rfl⟩,fun ⟨z,hz⟩ => by
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact Reachable.refl _⟩
  · intro x y hxy
    exact ⟨e x,rfl,e y,rfl,e.map_rel_iff.mpr hxy⟩

theorem surviving (hcard : Fintype.card V = 8) (hedges : G.edgeFinset.card = 22)
    (hmin : ∀ v, 5 ≤ G.degree v) (u : V) (hu : G.degree u = 5)
    (hd : ∀ z, ((G.induce (G.neighborSet u))ᶜ).degree z ≤ 1)
    (he : ((G.induce (G.neighborSet u))ᶜ).edgeFinset.card = 2)
    (hfree : G.IsKMinorFree 6) :
    ∃ a b : Fin 5, Nonempty (G ≃g CliqueEightResidualTemplates.graph a b) ∧
      ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) := by
  classical
  obtain ⟨a,b,⟨e⟩⟩ := exists_template G hcard hedges hmin u hu hd he
  have hf : (CliqueEightResidualTemplates.graph a b).IsKMinorFree 6 :=
    IsHMinorFree.minor hfree (minor_of_iso G e.symm)
  let ec : Gᶜ ≃g (CliqueEightResidualTemplates.graph a b)ᶜ := {
    toEquiv := e.toEquiv
    map_rel_iff' := by
      intro x y
      change (e x ≠ e y ∧ ¬(CliqueEightResidualTemplates.graph a b).Adj (e x) (e y)) ↔ (x ≠ y ∧ ¬G.Adj x y)
      simp only [e.injective.ne_iff,e.map_rel_iff] }
  have hc : ∀ v, ((CliqueEightResidualTemplates.graph a b)ᶜ).degree v ≤ 2 := by
    intro v
    obtain ⟨x,rfl⟩ := ec.surjective v
    rw [ec.degree_eq]
    exact CliqueEightComplementCounts.degree_le_two G hcard hmin x
  exact ⟨a,b,⟨e⟩,CliqueEightResidualTemplates.surviving a b hf hc⟩
end Paper.CliqueEightActualTemplate
