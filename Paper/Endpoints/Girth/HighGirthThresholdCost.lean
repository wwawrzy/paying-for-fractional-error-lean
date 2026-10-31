import Paper.Endpoints.Girth.HighGirthCostDecomposition
set_option maxHeartbeats 200000
namespace Paper.HighGirthThresholdCost

theorem threshold_cost_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x) :
    (3 : Real) / 2 * (Paper.HighGirthRounding.first G x).card +
      (Paper.HighGirthRounding.residual G x).card + Paper.HighGirthRounding.oversupply G x +
        Paper.HighGirthRounding.penalty G x - Paper.HighGirthRounding.excess G x / 2 ≤
          Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x := by
  classical
    have hfirst : (1 : Real) / 2 * (Paper.HighGirthRounding.first G x).card ≤
        ∑ v ∈ Paper.HighGirthRounding.first G x, x v := by
      calc
        _ = ∑ _v ∈ Paper.HighGirthRounding.first G x, ((1 : Real) / 2) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.2.le)
    have hweighted : (∑ v ∈ Paper.HighGirthRounding.high G x,
        ((Paper.HighGirthRounding.hits G x v : Real) - 3) * x v) ≤
        (1 : Real) / 2 * Paper.HighGirthRounding.excess G x := by
      unfold Paper.HighGirthRounding.excess
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v hv
      have hcap := (Paper.HighGirthHighGeometry.high_vertex_geometry G x v hv).2.2.2
      have hn := (Finset.mem_filter.mp hv).2
      have hh : (4 : Real) ≤ (Paper.HighGirthRounding.hits G x v : Real) := by exact_mod_cast hn
      have hcoef : 0 ≤ (Paper.HighGirthRounding.hits G x v : Real) - 3 := by linarith
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcap hcoef
    have hcost := Paper.HighGirthCostDecomposition.cost_decomposition G x hx
    nlinarith only [hfirst, hweighted, hcost]

end Paper.HighGirthThresholdCost

#print axioms Paper.HighGirthThresholdCost.threshold_cost_bound
