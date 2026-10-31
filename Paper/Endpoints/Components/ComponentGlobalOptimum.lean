import Paper.Endpoints.Components.ComponentOptimumCost

/-! Compare actual local and global benchmarks through a true optimal cover.
All witnesses are proof-side; no global optimum is supplied to a program. -/
namespace Paper.ComponentGlobalOptimum

theorem component_optimum_le_global
    {V : Type} [Fintype V] [LinearOrder V]
    (cover : V → Finset V) (R : Finset V) (c : V → Nat)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hrows : ∀ r ∈ R, (cover r).Nonempty) :
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    Paper.IntegralCoverOptimum.optimum cover (R ∩ H) c ≤
      Paper.IntegralCoverOptimum.optimum cover R c := by
  classical
  obtain ⟨D, hD, hEq⟩ := Paper.IntegralCoverOptimum.exists_optimal cover R c hrows
  have hlocal := Paper.ComponentOptimumCost.component_optimum_le_cover_cost cover R D c X hD.2
  apply hlocal.trans
  apply le_trans _ hEq.le
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
    (by intros; exact Nat.zero_le _)

end Paper.ComponentGlobalOptimum

#print axioms Paper.ComponentGlobalOptimum.component_optimum_le_global
