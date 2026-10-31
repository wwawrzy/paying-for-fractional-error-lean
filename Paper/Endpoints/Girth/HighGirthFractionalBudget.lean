import Paper.Endpoints.Girth.HighGirthWeightedBudget
set_option maxHeartbeats 200000
namespace Paper.HighGirthFractionalBudget

theorem fractional_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Paper.HighGirthTransformation.far G).card : Real) + Paper.HighGirthAuxiliary.number G ≤
      3 * Paper.SevenFoundation.fractionalNumber G := by
  have hbelow : BddBelow (Paper.HighGirthAuxiliary.feasibleCosts G) := by
    refine ⟨0, ?_⟩
    rintro a ⟨x, hx, rfl⟩
    exact Paper.SevenFoundation.cost_nonneg_of_feasible _ _ hx
  have haux : ∀ y : V → Real,
      Paper.SevenFoundation.feasible (Paper.SevenFoundation.ordinary G) y →
      Paper.HighGirthAuxiliary.number G ≤ Paper.SevenFoundation.cost
        (Paper.HighGirthAuxiliary.auxiliary G) (Paper.HighGirthAuxiliary.restrict G y) := by
    intro y hy
    apply csInf_le hbelow
    exact ⟨Paper.HighGirthAuxiliary.restrict G y,
      (Paper.HighGirthRestriction.restriction_feasible G).2 y hy, rfl⟩
  have hbudget : ∀ y : V → Real,
      Paper.SevenFoundation.feasible (Paper.SevenFoundation.ordinary G) y →
      ((Paper.HighGirthTransformation.far G).card : Real) + Paper.HighGirthAuxiliary.number G ≤
        3 * ∑ v, y v := by
    intro y hy
    exact (add_le_add le_rfl (haux y hy)).trans
      (Paper.HighGirthWeightedBudget.weighted_budget G y hy)
  have hlow : (((Paper.HighGirthTransformation.far G).card : Real) +
      Paper.HighGirthAuxiliary.number G) / 3 ≤ Paper.SevenFoundation.fractionalNumber G := by
    apply le_csInf (Paper.SevenFoundation.feasibleCosts_nonempty G)
    rintro a ⟨y, hy, rfl⟩
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 3)).mpr
    simpa only [Paper.SevenFoundation.ordinary_cost, mul_comm] using hbudget y hy
  exact (div_le_iff₀ (by norm_num : (0 : Real) < 3)).mp hlow |>.trans_eq (mul_comm _ _)

end Paper.HighGirthFractionalBudget

#print axioms Paper.HighGirthFractionalBudget.fractional_budget
