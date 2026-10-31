import Paper.Communication.SurfaceResidualRounding
import Paper.Endpoints.Rounding.SurfaceSolverDensity
namespace Paper.SurfaceResidualSolver
open BroadcastModel SevenFoundation

theorem parameters (e : ℝ) (he : 0 ≤ e) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SurfaceRounding.MinorBound G e → ∀ {b : ℕ} (C : BitCode V b),
        let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 7 q M hQ
        let D := PartialFractionalProgram.denominator Δ k Q T s q
        GeneralCoveringIntegral.Covers (SurfaceResidual.cover G 6) (CurrentBudget.demands G 6)
          (Finset.univ.filter (fun v => (SurfaceResidualRounding.withSolver 6 D P).runEncoded G (fun _ => ()) v = true)) ∧
        cost (CurrentBudget.auxiliary G 6)
          (fun v => ((CurrentCriticalProgram.numerators G 6 D P v).val : ℝ) / D) ≤
          (1 + 1 / 588 : ℝ) * CurrentBudget.auxiliaryNumber G 6 := by
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
    GeneralFractionalBroadcast.parameters (3 + 3 * e) (by linarith) 7 (1 / 588) (by norm_num)
  refine ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hden b C
  let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 7 q M hQ
  let D := PartialFractionalProgram.denominator Δ k Q T s q
  have hD : 0 < D := PartialFractionalProgram.denominator_pos Δ k Q T s q hQ hq
  have hr := hrun G (SurfaceRounding.solver_density G e he hden) C
    (CurrentBudget.demands G 6) (fun v => (CurrentZoneProgram.expected G 6 v).cost)
    (CurrentZoneProgram.cost_positive G 6)
  dsimp only at hr ⊢
  simp only [Program.runEncoded_eq_run] at hr
  exact SurfaceResidualRounding.from_partial_spec G 6 D hD 3 (1 / 588) (by norm_num) P hr.1 hr.2
end Paper.SurfaceResidualSolver
