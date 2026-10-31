import Paper.Endpoints.Girth.HighGirthMaskedOptimum
import Paper.Solver.LocalSearch.GeneralFractionalBroadcast
import Paper.Preliminaries.PlanarDensity

/-! Transfer the actual solver's LP guarantee to the original high-girth
auxiliary problem after the local cap and support restriction. -/
namespace Paper.HighGirthNearOptimalInput
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem transfer (y : V → Real) (δ : Real)
    (hy : PartialOptimum.Feasible (HighGirthMaskedInput.graph G)
      (HighGirthTransformation.demands G) y)
    (hcost : PartialOptimum.objective (HighGirthMaskedInput.weights G) y ≤
      (1 + δ) * PartialOptimum.number (HighGirthMaskedInput.graph G)
        (HighGirthTransformation.demands G) (HighGirthMaskedInput.weights G)) :
    SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) (HighGirthMaskedInput.capped G y) ∧
    (∀ v ∈ HighGirthTransformation.zone G, HighGirthMaskedInput.capped G y v ≤ 1) ∧
    SevenFoundation.cost (HighGirthAuxiliary.auxiliary G) (HighGirthMaskedInput.capped G y) ≤
      (1 + δ) * HighGirthAuxiliary.number G := by
  have hc := HighGirthMaskedCap.masked_capped_solver_input G y hy
  rw [HighGirthMaskedOptimum.masked_number_eq_auxiliary G] at hcost
  exact ⟨hc.1, hc.2.1, hc.2.2.trans hcost⟩

theorem masked_planar_density (hplanar : G.IsPlanar) :
    MinorDensity.Bound (HighGirthMaskedInput.graph G) 3 :=
  MaskedTaskGraph.density G _ (PlanarDensity.minor_density G hplanar)

theorem weighted_solver_guarantee :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (3 : Real) → ∀ {idBits : ℕ} (C : BroadcastModel.BitCode V idBits) (R : Finset V)
          (c : V → Fin (3 + 1)), (∀ v, 1 ≤ (c v).val) →
        let y := fun v => (((GeneralFractionalBroadcast.program C A L Δ r k t Q T s 3 q M hQ).runEncoded G
          (fun u => (decide (u ∈ R), c u)) v).val : ℝ) /
            PartialFractionalProgram.denominator Δ k Q T s q
        PartialOptimum.Feasible G R y ∧
          PartialOptimum.objective (fun v => ((c v).val : ℝ)) y ≤
            (1 + ((5 : Real)/8482)) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by
  exact GeneralFractionalBroadcast.parameters (3 : Real) (by norm_num) 3 ((5 : Real)/8482) (by norm_num)

end Paper.HighGirthNearOptimalInput
#print axioms Paper.HighGirthNearOptimalInput.transfer
#print axioms Paper.HighGirthNearOptimalInput.masked_planar_density

#print axioms Paper.HighGirthNearOptimalInput.weighted_solver_guarantee
