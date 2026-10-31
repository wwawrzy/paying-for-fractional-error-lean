import Paper.Endpoints.Girth.HighGirthFractionalBudget

/-! All three parts of the named assertion fv:hg:budget, using the original
branch-based transformation and the actual auxiliary/global LP infima.
This is a graph/LP budget lemma, not the later rounding algorithm theorem. -/
namespace Paper.HighGirthBudget
open HighGirthTransformation

/-- The first selection and its budget, exactly at named-assertion scope. -/
theorem endpoint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((∀ v ∈ far G, G.degree v ≤ 2) ∧
      SevenFoundation.covered G (branches G) ⊆ demands G) ∧
    (∀ v ∈ zone G,
      (1 ≤ candidateCost G v ∧ candidateCost G v ≤ 3) ∧
      (candidateCost G v = 3 ↔ v ∈ demands G) ∧
      (candidateCost G v < 3 → G.degree v ≤ 2 ∧
        (SevenFoundation.closed G v ∩ demands G).card ≤ candidateCost G v - 1)) ∧
    ((far G).card : Real) + HighGirthAuxiliary.number G ≤
      3 * SevenFoundation.fractionalNumber G := by
  refine ⟨HighGirthFirstSelection.first_selection_geometry G, ?_,
    HighGirthFractionalBudget.fractional_budget G⟩
  intro v hv
  have hb := HighGirthCostBounds.candidate_cost_bounds G v hv
  refine ⟨⟨hb.1, hb.2.1⟩, HighGirthCostThree.cost_three_iff_demand G v hv, ?_⟩
  intro hc
  exact ⟨hb.2.2 hc, HighGirthCheapDemands.cheap_candidate_demands G v hv hc⟩

end Paper.HighGirthBudget

#print axioms Paper.HighGirthBudget.endpoint
