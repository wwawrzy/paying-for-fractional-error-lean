import Paper.Communication.SurfaceResidualRounding
import Paper.Endpoints.Rounding.SurfaceCount
namespace Paper.SurfaceResidualRounding
open Paper.BroadcastModel Paper.SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem withSolver_bound {N : ℕ} (D : ℕ) (hD : 0 < D)
    (P : Program V (Bool × Fin 8) (Fin N)) (δ e : ℝ) (he : 0 ≤ e)
    (hden : SurfaceRounding.MinorBound G e)
    (hraw : PartialOptimum.Feasible G (CurrentBudget.demands G 6)
      (fun v => ((CurrentCriticalProgram.raw G 6 P v).val : ℝ) / D))
    (hcost : PartialOptimum.objective (CurrentCriticalProgram.weights G 6)
      (fun v => ((CurrentCriticalProgram.raw G 6 P v).val : ℝ) / D) ≤
      (1 + δ) * PartialOptimum.number G (CurrentBudget.demands G 6)
        (CurrentCriticalProgram.weights G 6)) :
    (1 + 1/294 : ℝ) * (Finset.univ.filter (fun v =>
      (withSolver 6 D P).runEncoded G (fun _ => ()) v = true)).card ≤
      (1 + δ) * CurrentBudget.auxiliaryNumber G 6 + 2 * e := by
  classical
  have hs := CurrentCriticalProgram.cap_restrict_spec G 6 _ hraw δ hcost
  have hv := CurrentCriticalProgram.project_value G 6 D hD (CurrentCriticalProgram.raw G 6 P)
  change (fun v => ((CurrentCriticalProgram.numerators G 6 D P v).val : ℝ) / D) = _ at hv
  rw [← hv] at hs
  let x := fun v => ((CurrentCriticalProgram.numerators G 6 D P v).val : ℝ) / D
  have hc : ∀ v ∈ CurrentBudget.candidates G 6, x v ≤ 1 := fun v _ => hs.2.1 v
  have hb := (SurfaceRounding.actual_bounds G x hs.1 hc e he hden).2.2
  have ho : CurrentRounding.objective G 3
      (CurrentCounting.input G 3 6 (by norm_num) x hs.1 hc) =
      cost (CurrentBudget.auxiliary G 6) x := by
    simp [CurrentRounding.objective, CurrentCounting.input, cost,
      CurrentBudget.auxiliary, ite_mul, Finset.sum_filter]
  rw [ho] at hb
  simp only [Program.runEncoded_eq_run, withSolver, Program.run,
    CurrentCriticalProgram.auxiliary_run]
  rw [correct G 6 D (D + 1) hD 3 (by norm_num) _ hs.1 hc]
  have hf : Finset.univ.filter (fun v => decide (v ∈ CurrentRounding.output G 3
      (CurrentCounting.input G 3 6 (by norm_num) x hs.1 hc)) = true) =
      CurrentRounding.output G 3 (CurrentCounting.input G 3 6 (by norm_num) x hs.1 hc) := by
    ext v
    simp
  rw [hf]
  linarith [hs.2.2]
end Paper.SurfaceResidualRounding
