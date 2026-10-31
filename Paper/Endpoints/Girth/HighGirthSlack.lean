import Paper.Endpoints.Girth.HighGirthOtherGeometry
set_option maxHeartbeats 200000
namespace Paper.HighGirthSlack

theorem slack_nonnegative
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x) :
    0 ≤ Paper.HighGirthRounding.penalty G x ∧
      0 ≤ Paper.HighGirthRounding.oversupply G x ∧
      (∀ v ∈ Paper.HighGirthRounding.positive G x,
        1 ≤ (Paper.HighGirthTransformation.candidateCost G v : Real) -
          (Paper.HighGirthRounding.hits G x v : Real) ∧
        Paper.HighGirthRounding.hits G x v ≤ 2) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold Paper.HighGirthRounding.penalty
    apply Finset.sum_nonneg
    intro v hv
    have hnat := (Paper.HighGirthOtherGeometry.remaining_candidate_geometry G x v hv).1
    have hreal : (Paper.HighGirthRounding.hits G x v : Real) ≤
        (Paper.HighGirthTransformation.candidateCost G v : Real) := by exact_mod_cast hnat
    exact mul_nonneg (sub_nonneg.mpr hreal) (hx.1 v)
  · unfold Paper.HighGirthRounding.oversupply
    apply Finset.sum_nonneg
    intro r hr
    have hr0 : r ∈ Paper.HighGirthTransformation.demands G := (Finset.mem_sdiff.mp hr).1
    have hrow := hx.2.2 r hr0
    change 1 ≤ ∑ v ∈ Paper.SevenFoundation.closed G r ∩ Paper.HighGirthTransformation.zone G, x v at hrow
    rw [Finset.inter_eq_left.mpr ((Paper.HighGirthRestriction.restriction_feasible G).1 r hr0)] at hrow
    exact sub_nonneg.mpr hrow
  · intro v hv
    obtain ⟨hvO, hlt⟩ := Finset.mem_filter.mp hv
    have hvZ : v ∈ Paper.HighGirthTransformation.zone G := (Finset.mem_sdiff.mp hvO).1
    have hb := (Paper.HighGirthCostBounds.candidate_cost_bounds G v hvZ).2.1
    have hn : Paper.HighGirthRounding.hits G x v + 1 ≤
        Paper.HighGirthTransformation.candidateCost G v := by omega
    have hd : (Paper.HighGirthRounding.hits G x v : Real) + 1 ≤
        (Paper.HighGirthTransformation.candidateCost G v : Real) := by exact_mod_cast hn
    constructor
    · linarith
    · omega

end Paper.HighGirthSlack

#print axioms Paper.HighGirthSlack.slack_nonnegative
