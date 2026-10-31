import Paper.Endpoints.Girth.HighGirthSlackParameter
set_option maxHeartbeats 400000
namespace Paper.HighGirthStaticThree
theorem coefficient_three_static
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (a : Rat) (ha : 1 ≤ a) (ha_upper : a < 8/7)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (hcap : ∀ v ∈ Paper.HighGirthTransformation.zone G, x v ≤ 1)
    (hden : Paper.Incidence.InducedDensityBound G (a : Real))
    (hsolver : Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x ≤
      (1 + (Paper.HighGirthSlackParameter.delta a : Real)) * Paper.HighGirthAuxiliary.number G) :
    0 < Paper.HighGirthSlackParameter.delta a ∧
    Paper.HighGirthSlackParameter.delta (17/15) = 5/8482 ∧
    ((Paper.HighGirthRounding.output G x).card : Real) ≤ Paper.HighGirthAuxiliary.number G ∧
    Paper.SevenFoundation.dominates G (Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x) ∧
    ((Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x).card : Real) ≤
      3 * Paper.SevenFoundation.fractionalNumber G := by
  classical
  have haR : (1 : Real) ≤ (a : Real) := by exact_mod_cast ha
  have huR : (a : Real) < (8 : Real)/7 := by
    have hh : (a : Real) < ((8/7 : Rat) : Real) := Rat.cast_lt.mpr ha_upper
    norm_num at hh
    exact hh
  have hr := Paper.HighGirthRoundingSlack.actual_rounding_slack G x hx hcap (a : Real) haR huR hden
  have hcast := Paper.HighGirthSlackParameter.delta_cast a
  dsimp only at hcast hr
  rw [←hcast] at hr
  have hdelta : 0 < Paper.HighGirthSlackParameter.delta a := by exact_mod_cast hr.2.1
  have hfactor : (0 : Real) < 1+(Paper.HighGirthSlackParameter.delta a : Real) := by linarith [hr.2.1]
  have hD : ((Paper.HighGirthRounding.output G x).card : Real) ≤ Paper.HighGirthAuxiliary.number G :=
    (mul_le_mul_iff_right₀ hfactor).mp (hr.2.2.trans hsolver)
  have hdom : Paper.SevenFoundation.dominates G (Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x) := by
    intro v
    by_cases hvF : v ∈ Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.far G)
    · exact Paper.SevenFoundation.covered_mono G Finset.subset_union_left hvF
    · have hvZ : v ∈ Paper.HighGirthTransformation.zone G := by
        by_contra hn
        have hvfar : v ∈ Paper.HighGirthTransformation.far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩
        exact hvF (Paper.SevenFoundation.subset_covered G _ hvfar)
      have hvR : v ∈ Paper.HighGirthTransformation.demands G := Finset.mem_sdiff.mpr ⟨hvZ,hvF⟩
      exact Paper.SevenFoundation.covered_mono G Finset.subset_union_right (hr.1 v hvR)
  have hcard : ((Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x).card : Real) ≤
      (Paper.HighGirthTransformation.far G).card + (Paper.HighGirthRounding.output G x).card := by
    exact_mod_cast Finset.card_union_le (Paper.HighGirthTransformation.far G) (Paper.HighGirthRounding.output G x)
  refine ⟨hdelta,Paper.HighGirthSlackParameter.at_seventeen_fifteenths,hD,hdom,?_⟩
  exact (hcard.trans (add_le_add le_rfl hD)).trans (Paper.HighGirthFractionalBudget.fractional_budget G)
end Paper.HighGirthStaticThree
#print axioms Paper.HighGirthStaticThree.coefficient_three_static
