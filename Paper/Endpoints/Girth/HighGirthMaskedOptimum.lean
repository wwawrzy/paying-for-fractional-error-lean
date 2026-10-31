import Paper.Endpoints.Girth.HighGirthMaskedLPBridge
set_option maxHeartbeats 200000
namespace Paper.HighGirthMaskedOptimum

theorem masked_number_eq_auxiliary
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Paper.PartialOptimum.number (Paper.HighGirthMaskedInput.graph G)
      (Paper.HighGirthTransformation.demands G) (Paper.HighGirthMaskedInput.weights G) =
      Paper.HighGirthAuxiliary.number G := by
  classical
    have hn : ∀ v, 0 ≤ Paper.HighGirthMaskedInput.weights G v := fun v => Nat.cast_nonneg _
    apply le_antisymm
    · apply le_csInf (Paper.HighGirthMaskedLPBridge.auxiliary_costs_nonempty G)
      rintro a ⟨x, hx, rfl⟩
      rw [← Paper.HighGirthMaskedLPBridge.auxiliary_objective G x hx]
      exact Paper.MaskedLPOptimum.number_le_feasible (Paper.HighGirthMaskedInput.graph G) (Paper.HighGirthTransformation.demands G) (Paper.HighGirthMaskedInput.weights G) hn x (Paper.HighGirthMaskedLPBridge.auxiliary_to_masked G x hx)
    · obtain ⟨y, hy, he⟩ := Paper.PartialOptimum.exists_optimum_eq_number (Paper.HighGirthMaskedInput.graph G) (Paper.HighGirthTransformation.demands G) (Paper.HighGirthMaskedInput.weights G) hn
      have hc := Paper.HighGirthMaskedCap.masked_capped_solver_input G y hy
      have hnum : Paper.HighGirthAuxiliary.number G ≤ Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) (Paper.HighGirthMaskedInput.capped G y) := by
        apply csInf_le (Paper.HighGirthMaskedLPBridge.auxiliary_costs_bddBelow G)
        exact ⟨Paper.HighGirthMaskedInput.capped G y, hc.1, rfl⟩
      exact hnum.trans (hc.2.2.trans_eq he)

end Paper.HighGirthMaskedOptimum

#print axioms Paper.HighGirthMaskedOptimum.masked_number_eq_auxiliary
