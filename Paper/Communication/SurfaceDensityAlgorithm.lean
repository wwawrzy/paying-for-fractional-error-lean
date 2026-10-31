import Paper.Communication.SurfaceFinalProgram
import Paper.Endpoints.Components.SurfacePublicParameters
import Paper.Endpoints.Rounding.SurfaceProgramBound
import Paper.Endpoints.Rounding.SurfaceSolverDensity
namespace Paper.SurfaceDensityAlgorithm
open BroadcastModel SevenFoundation

theorem parameters (e : ℝ) (he : 0 ≤ e) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SurfaceRounding.MinorBound G e → ∀ {b : ℕ} (C : BitCode V b),
        let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 7 q M hQ
        let D := PartialFractionalProgram.denominator Δ k Q T s q
        let Z := Finset.univ.filter (fun v =>
          (SurfaceFinalProgram.program 6 D (SurfacePublicParameters.density e)
            (SurfacePublicParameters.budget e) C P).runEncoded G (fun _ => ()) v = true)
        dominates G Z ∧ ∀ Y : Finset V, dominates G Y → Z.card ≤ 7 * Y.card := by
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
  have hc := (SurfaceResidualRounding.from_partial_spec G 6 D hD 3 (1 / 588)
    (by norm_num) P hr.1 hr.2).1
  have hb := SurfaceResidualRounding.withSolver_bound G D hD P (1 / 588) e he hden hr.1 hr.2
  have hi := SurfacePublicParameters.incidence G 6 e he hden
  have ha := SurfacePublicParameters.density_pos e he
  have hK := SurfacePublicParameters.budget_pos e
  refine ⟨SurfaceFinalProgram.dominates G 6 D _ _ C P ha hK hi hc, ?_⟩
  intro Y hY
  exact SurfaceFinalProgram.card_bound G D _ _ C P ha hK e
    (SurfacePublicParameters.budget_large e) hi hc hb Y hY
end Paper.SurfaceDensityAlgorithm
