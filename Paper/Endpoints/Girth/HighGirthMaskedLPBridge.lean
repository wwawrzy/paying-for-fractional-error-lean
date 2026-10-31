import Paper.Endpoints.Girth.HighGirthMaskedCap

/-! Exact feasibility and objective correspondence for the original
high-girth auxiliary LP and its masked solver instance. -/
namespace Paper.HighGirthMaskedLPBridge
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem auxiliary_to_masked (x : V → Real) (hx : feasible (HighGirthAuxiliary.auxiliary G) x) :
    PartialOptimum.Feasible (HighGirthMaskedInput.graph G) (HighGirthTransformation.demands G) x := by
  refine ⟨hx.1, ?_⟩
  intro r hr
  rw [HighGirthMaskedInput.closed_at_demand G r hr]
  exact hx.2.2 r hr

theorem auxiliary_objective (x : V → Real) (hx : feasible (HighGirthAuxiliary.auxiliary G) x) :
    PartialOptimum.objective (HighGirthMaskedInput.weights G) x =
      cost (HighGirthAuxiliary.auxiliary G) x := by
  classical
  apply Finset.sum_congr rfl
  intro v _
  by_cases hz : v ∈ HighGirthTransformation.zone G
  · rw [HighGirthMaskedInput.weight_at G v hz]
    simp [HighGirthAuxiliary.auxiliary, hz]
  · have hzero : x v = 0 := hx.2.1 v hz
    simp [hzero]

theorem auxiliary_costs_nonempty : (HighGirthAuxiliary.feasibleCosts G).Nonempty := by
  have hone : PartialOptimum.Feasible (HighGirthMaskedInput.graph G)
      (HighGirthTransformation.demands G) (fun _ => 1) := by
    refine ⟨fun _ => zero_le_one, ?_⟩
    intro r _
    exact Finset.single_le_sum (fun v (_ : v ∈ closed (HighGirthMaskedInput.graph G) r) =>
      (zero_le_one : (0 : Real) ≤ 1)) (self_mem_closed (HighGirthMaskedInput.graph G) r)
  have hc := HighGirthMaskedCap.masked_capped_solver_input G (fun _ => 1) hone
  exact ⟨cost (HighGirthAuxiliary.auxiliary G) (HighGirthMaskedInput.capped G (fun _ => 1)),
    HighGirthMaskedInput.capped G (fun _ => 1), hc.1, rfl⟩

theorem auxiliary_costs_bddBelow : BddBelow (HighGirthAuxiliary.feasibleCosts G) := by
  refine ⟨0, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  exact cost_nonneg_of_feasible _ _ hx

end Paper.HighGirthMaskedLPBridge
#print axioms Paper.HighGirthMaskedLPBridge.auxiliary_to_masked
#print axioms Paper.HighGirthMaskedLPBridge.auxiliary_objective
#print axioms Paper.HighGirthMaskedLPBridge.auxiliary_costs_nonempty
#print axioms Paper.HighGirthMaskedLPBridge.auxiliary_costs_bddBelow
