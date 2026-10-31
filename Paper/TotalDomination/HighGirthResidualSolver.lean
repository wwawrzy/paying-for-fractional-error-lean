import Paper.TotalDomination.HighGirthStartup
import Paper.TotalDomination.HighGirthMathematicalEndpoint

/-! The actual residual fractional solver, with the five-bit startup and
private startup state preserved through the solver. -/
namespace Paper.TotalDomination.HighGirthResidualSolver
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

noncomputable def runtime {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) :=
  Program.seq (HighGirthStartup.program)
    (.seq (.local fun _ _ s => (s.solver,s))
      (ProgramMemory.carry (X := HighGirthStartup.Output V)
        (GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def solution {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) (v : V) : ℝ :=
  ((((runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) v).1.1.val : ℝ) /
    GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)

theorem run_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) :
    (runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) = fun v =>
      ((GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd).runEncoded G
        (HighGirthStartup.input G) v,
        ⟨HighGirthStartup.input G v,decide (v ∈ HighGirthSetup.F G),decide (v ∈ HighGirthStartup.linked G)⟩) := by
  simp only [runtime,Program.runEncoded_eq_run,Program.run]
  rw [HighGirthStartup.correct]
  exact ProgramMemory.run G _ _ _

theorem solution_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} 
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε) (t k b n : ℕ) (hd : 1 ≤ 2) :
    solution G codec p t k b n hd =
      GeneralCoveringFractionalEndpoint.solution G codec p t k b n hd (HighGirthStartup.input G) := by
  funext v
  simp only [solution,run_eq,GeneralCoveringFractionalEndpoint.solution]

theorem parameters_general (rho : ℝ) (hrho : 1 ≤ rho)  (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters rho 2 ε,
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G rho → (∀ v, (G.neighborFinset v).Nonempty) →
        ∀ {ids : ℕ} (codec : BitCode V ids),
        let x := CoveringOptimum.cap (solution G codec p t k b n (by omega))
        CoveringOptimum.Feasible (fun r => G.neighborFinset r) (HighGirthSetup.Z G) x ∧
        (∀ v, x v ≤ 1) ∧ (∀ v ∉ HighGirthSetup.K G, x v = 0) ∧
        (∑ v, (HighGirthSetup.c G v : ℝ)*x v) ≤
          (1+ε)*HighGirthSelection.residualOptimum G := by
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := GeneralCoveringFractionalEndpoint.parameters
    rho hrho 2 (by omega) ε hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hden hfree ids codec
  let rows := fun r => G.neighborFinset r ∩ HighGirthSetup.K G
  let y := solution G codec p t k b n (by omega : 1 ≤ 2)
  let x := CoveringOptimum.cap y
  have hs := hp G hden codec (HighGirthStartup.input G)
    (HighGirthStartup.original G hfree) (HighGirthStartup.positive_cost G)
  rw [← solution_eq] at hs
  have hy : CoveringOptimum.Feasible rows (HighGirthSetup.Z G) y := ⟨hs.1.1,hs.1.2.2⟩
  have hxc := CoveringOptimum.cap_feasible rows (HighGirthSetup.Z G) y hy
  have hsupport : ∀ v ∉ HighGirthSetup.K G, x v = 0 := by
    intro v hv
    have hz : y v = 0 := hs.1.2.1 v (fun hm => hv (HighGirthStartup.admissible_subset G hm))
    simp only [x,CoveringOptimum.cap,hz,min_eq_right zero_le_one]
  refine ⟨⟨hxc.1,?_⟩,fun v => min_le_left _ _,hsupport,?_⟩
  · intro r hr
    have hc := hxc.2 r hr
    dsimp only [rows] at hc
    rw [HighGirthSelection.demand_rows G hr] at hc
    exact hc
  · have hc := hs.2.1
    have hnumber : GeneralCoveringNormalizedFractional.supportedNumber rows (HighGirthSetup.Z G)
        (fun v => (HighGirthSetup.c G v : ℝ)) = HighGirthSelection.residualOptimum G := by
      apply GeneralCoveringNormalizedFractional.supportedNumber_eq_number rows (HighGirthSetup.Z G)
        (fun v => (HighGirthSetup.c G v : ℝ))
        (fun r hr => by dsimp only [rows];rw [HighGirthSelection.demand_rows G hr];exact hfree r)
        (fun _ => Nat.cast_nonneg _)
    change (∑ v, (HighGirthSetup.c G v : ℝ)*y v) ≤
      (1+ε)*GeneralCoveringNormalizedFractional.supportedNumber rows (HighGirthSetup.Z G)
        (fun v => (HighGirthSetup.c G v : ℝ)) at hc
    rw [hnumber] at hc
    exact (CoveringOptimum.cap_cost_le (fun v => (HighGirthSetup.c G v : ℝ)) y
      (fun _ => Nat.cast_nonneg _)).trans hc

end Paper.TotalDomination.HighGirthResidualSolver
#print axioms Paper.TotalDomination.HighGirthResidualSolver.parameters_general
