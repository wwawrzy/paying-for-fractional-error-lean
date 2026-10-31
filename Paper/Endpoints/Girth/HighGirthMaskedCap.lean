import Paper.Endpoints.Girth.HighGirthMaskedInput
set_option maxHeartbeats 200000
namespace Paper.HighGirthMaskedCap

theorem masked_capped_solver_input
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (y : V → Real)
    (hy : Paper.PartialOptimum.Feasible (Paper.HighGirthMaskedInput.graph G)
      (Paper.HighGirthTransformation.demands G) y) :
    Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G)
      (Paper.HighGirthMaskedInput.capped G y) ∧
    (∀ v ∈ Paper.HighGirthTransformation.zone G, Paper.HighGirthMaskedInput.capped G y v ≤ 1) ∧
    Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G)
      (Paper.HighGirthMaskedInput.capped G y) ≤
      Paper.PartialOptimum.objective (Paper.HighGirthMaskedInput.weights G) y := by
  classical
    have hc := Paper.PartialOptimum.cap_feasible (Paper.HighGirthMaskedInput.graph G) (Paper.HighGirthTransformation.demands G) y hy
    have hnon : ∀ v, 0 ≤ Paper.HighGirthMaskedInput.capped G y v := by
      intro v
      unfold Paper.HighGirthMaskedInput.capped Paper.HighGirthAuxiliary.restrict
      split_ifs
      · exact hc.1 v
      · exact le_rfl
    refine ⟨⟨hnon, ?_, ?_⟩, ?_, ?_⟩
    · intro v hv
      change (if v ∈ Paper.HighGirthTransformation.zone G then Paper.PartialOptimum.cap y v else 0) = 0
      exact if_neg hv
    · intro r hr
      have hrow := hc.2 r hr
      rw [Paper.HighGirthMaskedInput.closed_at_demand G r hr] at hrow
      change 1 ≤ ∑ v ∈ Paper.SevenFoundation.closed G r ∩ Paper.HighGirthTransformation.zone G, Paper.HighGirthMaskedInput.capped G y v
      have he : (∑ v ∈ Paper.SevenFoundation.closed G r ∩ Paper.HighGirthTransformation.zone G, Paper.HighGirthMaskedInput.capped G y v) =
          ∑ v ∈ Paper.SevenFoundation.closed G r ∩ Paper.HighGirthTransformation.zone G, Paper.PartialOptimum.cap y v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact if_pos (Finset.mem_inter.mp hv).2
      rw [he]
      exact hrow
    · intro v hv
      change (if v ∈ Paper.HighGirthTransformation.zone G then min 1 (y v) else 0) ≤ 1
      rw [if_pos hv]
      exact min_le_left _ _
    · change (∑ v, (Paper.HighGirthAuxiliary.auxiliary G).cost v * Paper.HighGirthMaskedInput.capped G y v) ≤ ∑ v, Paper.HighGirthMaskedInput.weights G v * y v
      apply Finset.sum_le_sum
      intro v hv
      by_cases hz : v ∈ Paper.HighGirthTransformation.zone G
      · rw [Paper.HighGirthMaskedInput.weight_at G v hz]
        change (if v ∈ Paper.HighGirthTransformation.zone G then (Paper.HighGirthTransformation.candidateCost G v : Real) else 0) *
          (if v ∈ Paper.HighGirthTransformation.zone G then min 1 (y v) else 0) ≤ _
        rw [if_pos hz, if_pos hz]
        exact mul_le_mul_of_nonneg_left (min_le_right 1 (y v)) (Nat.cast_nonneg _)
      · have hp : 0 ≤ Paper.HighGirthMaskedInput.weights G v := Nat.cast_nonneg _
        change (if v ∈ Paper.HighGirthTransformation.zone G then (Paper.HighGirthTransformation.candidateCost G v : Real) else 0) * _ ≤ _
        rw [if_neg hz, zero_mul]
        exact mul_nonneg hp (hy.1 v)

end Paper.HighGirthMaskedCap

#print axioms Paper.HighGirthMaskedCap.masked_capped_solver_input
