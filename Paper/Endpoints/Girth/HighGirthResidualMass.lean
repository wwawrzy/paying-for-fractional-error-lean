import Paper.Endpoints.Girth.HighGirthDensityExcess
set_option maxHeartbeats 200000
namespace Paper.HighGirthResidualMass

theorem residual_mass_identity
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (∀ v ∈ Paper.HighGirthRounding.first G x, Paper.HighGirthRounding.hits G x v = 0) ∧
      (∑ v, (Paper.HighGirthRounding.hits G x v : Real) * x v) =
        (Paper.HighGirthRounding.residual G x).card + Paper.HighGirthRounding.oversupply G x := by
  classical
  constructor
  · intro v hv
    change (Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.residual G x).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hrv, hrR⟩ := Finset.mem_inter.mp hr
    exact (Finset.mem_sdiff.mp hrR).2 (Finset.mem_biUnion.mpr ⟨v, hv, hrv⟩)
  · simp only [Paper.HighGirthRounding.hits]
    rw [← Paper.WeightedBudget.incidence_sum G (Paper.HighGirthRounding.residual G x) x]
    simp [Paper.HighGirthRounding.oversupply, Finset.sum_sub_distrib] <;> ring

end Paper.HighGirthResidualMass

#print axioms Paper.HighGirthResidualMass.residual_mass_identity
