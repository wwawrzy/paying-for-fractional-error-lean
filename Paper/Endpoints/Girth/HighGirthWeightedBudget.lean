import Paper.Endpoints.Girth.HighGirthRestriction
set_option maxHeartbeats 200000
namespace Paper.HighGirthWeightedBudget

theorem weighted_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → Real)
    (hy : Paper.SevenFoundation.feasible (Paper.SevenFoundation.ordinary G) y) :
    ((Paper.HighGirthTransformation.far G).card : Real) +
      Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G)
        (Paper.HighGirthAuxiliary.restrict G y) ≤ 3 * ∑ v, y v := by
  classical
    have hcost : Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G)
        (Paper.HighGirthAuxiliary.restrict G y) =
        ∑ v ∈ Paper.HighGirthTransformation.zone G,
          (Paper.HighGirthTransformation.candidateCost G v : Real) * y v := by
      simp [Paper.SevenFoundation.cost, Paper.HighGirthAuxiliary.auxiliary, Paper.HighGirthAuxiliary.restrict]
    rw [hcost]
    have hZ : (∑ v ∈ Paper.HighGirthTransformation.zone G,
        (Paper.HighGirthTransformation.candidateCost G v : Real) * y v) =
        ∑ v, if v ∈ Paper.HighGirthTransformation.zone G then
          (Paper.HighGirthTransformation.candidateCost G v : Real) * y v else 0 := by simp
    calc
      _ ≤ (∑ v, ((Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.far G).card : Real) * y v) +
          ∑ v ∈ Paper.HighGirthTransformation.zone G,
            (Paper.HighGirthTransformation.candidateCost G v : Real) * y v :=
        add_le_add (Paper.WeightedBudget.coverage_sum G (Paper.HighGirthTransformation.far G) y hy) le_rfl
      _ = ∑ v, (((Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.far G).card : Real) * y v +
          if v ∈ Paper.HighGirthTransformation.zone G then
            (Paper.HighGirthTransformation.candidateCost G v : Real) * y v else 0) := by
        rw [hZ, Finset.sum_add_distrib]
      _ ≤ ∑ v, 3 * y v := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v ∈ Paper.HighGirthTransformation.zone G
        · simp only [if_pos hv]
          have hvF : v ∉ Paper.HighGirthTransformation.far G := fun h => (Finset.mem_sdiff.mp h).2 hv
          have hinter : Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.far G =
              G.neighborFinset v ∩ Paper.HighGirthTransformation.far G := by
            ext u
            constructor
            · intro hu
              obtain ⟨huv, huF⟩ := Finset.mem_inter.mp hu
              have hne : u ≠ v := by
                intro heq
                subst u
                exact hvF huF
              exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr
                (((Paper.SevenFoundation.mem_closed G u v).mp huv).resolve_left hne), huF⟩
            · intro hu
              obtain ⟨huv, huF⟩ := Finset.mem_inter.mp hu
              exact Finset.mem_inter.mpr ⟨(Paper.SevenFoundation.mem_closed G u v).mpr
                (Or.inr ((G.mem_neighborFinset v u).mp huv)), huF⟩
          rw [hinter]
          have hpos := (Paper.HighGirthCostBounds.candidate_cost_bounds G v hv).1
          have hsum : Paper.HighGirthTransformation.candidateCost G v +
              (G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).card = 3 := by
            dsimp only [Paper.HighGirthTransformation.candidateCost] at hpos ⊢
            omega
          have hreal : (Paper.HighGirthTransformation.candidateCost G v : Real) +
              ((G.neighborFinset v ∩ Paper.HighGirthTransformation.far G).card : Real) = 3 := by exact_mod_cast hsum
          have hmul := congrArg (fun z : Real => z * y v) hreal
          nlinarith only [hmul]
        · simp only [if_neg hv, add_zero]
          apply mul_le_mul_of_nonneg_right _ (hy.1 v)
          have hvF : v ∈ Paper.HighGirthTransformation.far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
          have hdeg := (Paper.HighGirthFirstSelection.first_selection_geometry G).1 v hvF
          have hcard := Finset.card_le_card (Finset.inter_subset_left :
            Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.far G ⊆ Paper.SevenFoundation.closed G v)
          rw [Paper.WeightedBudget.closed_card G v] at hcard
          have hn : (Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.far G).card ≤ 3 := by omega
          exact_mod_cast hn
      _ = 3 * ∑ v, y v := (Finset.mul_sum _ _ _).symm

end Paper.HighGirthWeightedBudget

#print axioms Paper.HighGirthWeightedBudget.weighted_budget
