import Paper.Optimality.Treewidth.CliqueEightActualTemplate
namespace Paper.CliqueResidualCanonical
open SimpleGraph
noncomputable def iso_0_1 : CliqueEightResidualTemplates.graph 0 1 ≃g CliqueEightResidualTemplates.graph 0 1 := by
  let f : Fin 8 → Fin 8 := ![0,1,2,3,4,5,6,7]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact { toEquiv := e, map_rel_iff' := by decide }
noncomputable def iso_1_0 : CliqueEightResidualTemplates.graph 1 0 ≃g CliqueEightResidualTemplates.graph 0 1 := by
  let f : Fin 8 → Fin 8 := ![0,1,2,4,3,5,6,7]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact { toEquiv := e, map_rel_iff' := by decide }
noncomputable def iso_2_3 : CliqueEightResidualTemplates.graph 2 3 ≃g CliqueEightResidualTemplates.graph 0 1 := by
  let f : Fin 8 → Fin 8 := ![0,1,2,5,6,3,4,7]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact { toEquiv := e, map_rel_iff' := by decide }
noncomputable def iso_3_2 : CliqueEightResidualTemplates.graph 3 2 ≃g CliqueEightResidualTemplates.graph 0 1 := by
  let f : Fin 8 → Fin 8 := ![0,1,2,5,6,4,3,7]
  let e : Fin 8 ≃ Fin 8 := Equiv.ofBijective f (by decide)
  exact { toEquiv := e, map_rel_iff' := by decide }
theorem canonical (a b : Fin 5)
    (hp : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) :
    Nonempty (CliqueEightResidualTemplates.graph a b ≃g CliqueEightResidualTemplates.graph 0 1) := by
  rcases hp with h | h | h | h
  · rcases h with ⟨rfl,rfl⟩; exact ⟨iso_0_1⟩
  · rcases h with ⟨rfl,rfl⟩; exact ⟨iso_1_0⟩
  · rcases h with ⟨rfl,rfl⟩; exact ⟨iso_2_3⟩
  · rcases h with ⟨rfl,rfl⟩; exact ⟨iso_3_2⟩
theorem cycle_data : ∀ z : Fin 8, z.val < 5 →
    (CliqueEightResidualTemplates.graph 0 1).degree z = 5 ∧
    (CliqueEightResidualTemplates.graph 0 1).Adj 5 z ∧
    (CliqueEightResidualTemplates.graph 0 1).Adj 6 z ∧
    Fintype.card ((CliqueEightResidualTemplates.graph 0 1).commonNeighbors 5 z) = 3 ∧
    Fintype.card ((CliqueEightResidualTemplates.graph 0 1).commonNeighbors 6 z) = 3 := by decide

theorem apex_data :
    (CliqueEightResidualTemplates.graph 0 1).degree 5 = 6 ∧
    (CliqueEightResidualTemplates.graph 0 1).degree 6 = 6 ∧
    (CliqueEightResidualTemplates.graph 0 1).degree 7 = 7 ∧
    ¬(CliqueEightResidualTemplates.graph 0 1).Adj 5 6 := by decide
end Paper.CliqueResidualCanonical

