import Paper.Endpoints.Girth.HighGirthResidualMass
set_option maxHeartbeats 200000
namespace Paper.HighGirthCostDecomposition

theorem cost_decomposition
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x) :
    Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x =
      3 * (∑ v ∈ Paper.HighGirthRounding.first G x, x v) +
        (Paper.HighGirthRounding.residual G x).card + Paper.HighGirthRounding.oversupply G x +
          Paper.HighGirthRounding.penalty G x -
            (∑ v ∈ Paper.HighGirthRounding.high G x,
              ((Paper.HighGirthRounding.hits G x v : Real) - 3) * x v) := by
  classical
    let c : V → Real := fun v => (Paper.HighGirthTransformation.candidateCost G v : Real)
    have hsupport : ∀ v ∉ Paper.HighGirthTransformation.zone G, x v = 0 :=
      fun v hv => hx.2.1 v hv
    have hcost : Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x = ∑ v, c v * x v := by
      unfold Paper.SevenFoundation.cost
      apply Finset.sum_congr rfl
      intro v _
      change (if v ∈ Paper.HighGirthTransformation.zone G then
        (Paper.HighGirthTransformation.candidateCost G v : Real) else 0) * x v = c v * x v
      by_cases hv : v ∈ Paper.HighGirthTransformation.zone G
      · simp [hv, c]
      · simp [hv, hsupport v hv]
    have hpoint : (∑ v, c v * x v) = ∑ v,
        ((if v ∈ Paper.HighGirthRounding.first G x then 3 * x v else 0) +
          (Paper.HighGirthRounding.hits G x v : Real) * x v +
          (if v ∈ Paper.HighGirthRounding.other G x then
            (c v - (Paper.HighGirthRounding.hits G x v : Real)) * x v else 0) -
          (if v ∈ Paper.HighGirthRounding.high G x then
            ((Paper.HighGirthRounding.hits G x v : Real) - 3) * x v else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hw : v ∈ Paper.HighGirthRounding.first G x
      · have hnH : v ∉ Paper.HighGirthRounding.high G x :=
          fun hh => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hh).1).2 hw
        have hnO : v ∉ Paper.HighGirthRounding.other G x :=
          fun ho => (Finset.mem_sdiff.mp ho).2 (Finset.mem_union_left _ hw)
        have hcW : c v = 3 := by
          have hn := (Finset.mem_filter.mp hw).2.1
          dsimp only [c]
          exact_mod_cast hn
        simp only [if_pos hw, if_neg hnH, if_neg hnO, hcW,
          (Paper.HighGirthResidualMass.residual_mass_identity G x).1 v hw,
          Nat.cast_zero, zero_mul, add_zero, sub_zero]
      · by_cases hh : v ∈ Paper.HighGirthRounding.high G x
        · have hnO : v ∉ Paper.HighGirthRounding.other G x :=
            fun ho => (Finset.mem_sdiff.mp ho).2 (Finset.mem_union_right _ hh)
          have hcH : c v = 3 := by
            have hn := (Paper.HighGirthHighGeometry.high_vertex_geometry G x v hh).2.2.1
            dsimp only [c]
            exact_mod_cast hn
          rw [if_neg hw, if_neg hnO, if_pos hh, hcH]
          ring
        · by_cases hv : v ∈ Paper.HighGirthTransformation.zone G
          · have ho : v ∈ Paper.HighGirthRounding.other G x :=
              Finset.mem_sdiff.mpr ⟨hv, by simpa only [Finset.mem_union, not_or] using ⟨hw, hh⟩⟩
            rw [if_neg hw, if_pos ho, if_neg hh]
            ring
          · simp [hsupport v hv]
    rw [hcost, hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_mem_eq]
    rw [← Finset.mul_sum, (Paper.HighGirthResidualMass.residual_mass_identity G x).2]
    dsimp only [c]
    unfold Paper.HighGirthRounding.penalty
    ring

end Paper.HighGirthCostDecomposition

#print axioms Paper.HighGirthCostDecomposition.cost_decomposition
