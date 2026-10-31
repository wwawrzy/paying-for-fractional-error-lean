import Paper.Endpoints.Components.OptimumCertificate
import Paper.Endpoints.Components.ComponentContext
set_option maxHeartbeats 200000
namespace Paper.ComponentOptimumCost

theorem component_optimum_le_cover_cost
    {V : Type} [Fintype V] [LinearOrder V]
    (cover : V → Finset V) (R D0 : Finset V) (c : V → Nat)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hcover0 : Paper.GeneralCoveringIntegral.Covers cover R D0) :
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    Paper.IntegralCoverOptimum.optimum cover (R ∩ H) c ≤
      (D0 ∩ H).sum c := by
  classical
  let I := Paper.CoveringIncidence.graph cover R
  let H := Paper.IncidenceComponent.vertices I X
  let L := R ∩ H
  let D := D0 ∩ Paper.CoveringSupport.admissible cover L
  have hfeas : Paper.IntegralCoverOptimum.Feasible cover L D := by
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro r hr
    obtain ⟨u, hu0, hur⟩ := hcover0 r (Finset.mem_inter.mp hr).1
    have huadm : u ∈ Paper.CoveringSupport.admissible cover L :=
      Finset.mem_biUnion.mpr ⟨r, hr, hur⟩
    exact ⟨u, Finset.mem_inter.mpr ⟨hu0, huadm⟩, hur⟩
  have hsubset : D ⊆ D0 ∩ H := by
    intro u hu
    obtain ⟨hu0, huadm⟩ := Finset.mem_inter.mp hu
    obtain ⟨r, hr, hur⟩ := Finset.mem_biUnion.mp huadm
    exact Finset.mem_inter.mpr ⟨hu0, Paper.IncidenceComponent.rows_stay cover R X r hr hur⟩
  change Paper.IntegralCoverOptimum.optimum cover L c ≤ (D0 ∩ H).sum c
  apply (Paper.IntegralCoverOptimum.optimum_le_cost cover L c hfeas).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intros; exact Nat.zero_le _)

end Paper.ComponentOptimumCost

#print axioms Paper.ComponentOptimumCost.component_optimum_le_cover_cost
