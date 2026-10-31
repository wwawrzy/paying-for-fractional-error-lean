import Paper.TotalDomination.IntegerStartup
import Paper.TotalDomination.IntegerMathematicalEndpoint

/-! The actual residual fractional solver, with the five-bit startup and
private startup state preserved through the solver. -/
namespace Paper.TotalDomination.IntegerResidualSolver
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

noncomputable def runtime {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) :=
  Program.seq (IntegerStartup.program d)
    (.seq (.local fun _ _ s => (s.solver,s))
      (ProgramMemory.carry (X := IntegerStartup.Output V d)
        (GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def solution {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) (v : V) : ℝ :=
  ((((runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) v).1.1.val : ℝ) /
    GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)

theorem run_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) :
    (runtime codec p t k b n hd).runEncoded G (fun _ => PUnit.unit) = fun v =>
      ((GeneralCoveringFractionalEndpoint.runtime codec p t k b n hd).runEncoded G
        (IntegerStartup.input G d) v,
        ⟨IntegerStartup.input G d v,decide (v ∈ IntegerSetup.F G d),decide (v ∈ IntegerSetup.linked G d)⟩) := by
  simp only [runtime,Program.runEncoded_eq_run,Program.run]
  rw [IntegerStartup.correct]
  exact ProgramMemory.run G _ _ _

theorem solution_eq {ids : ℕ} (codec : BitCode V ids) {rho ε : ℝ} {d : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε) (t k b n : ℕ) (hd : 1 ≤ d) :
    solution G codec p t k b n hd =
      GeneralCoveringFractionalEndpoint.solution G codec p t k b n hd (IntegerStartup.input G d) := by
  funext v
  simp only [solution,run_eq,GeneralCoveringFractionalEndpoint.solution]

theorem parameters_general (rho : ℝ) (hrho : 1 ≤ rho) (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters rho d ε,
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G rho → (∀ v, (G.neighborFinset v).Nonempty) →
        ∀ {ids : ℕ} (codec : BitCode V ids),
        let x := CoveringOptimum.cap (solution G codec p t k b n (by omega))
        CoveringOptimum.Feasible (fun r => G.neighborFinset r) (IntegerSetup.Z G d) x ∧
        (∀ v, x v ≤ 1) ∧ (∀ v ∉ IntegerSetup.K G d, x v = 0) ∧
        (∑ v, (IntegerSetup.c G d v : ℝ)*x v) ≤
          (1+ε)*InitialSelection.residualOptimum G d := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := GeneralCoveringFractionalEndpoint.parameters
    rho hrho d (by omega) ε hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hden hfree ids codec
  let rows := fun r => G.neighborFinset r ∩ IntegerSetup.K G d
  let y := solution G codec p t k b n (by omega : 1 ≤ d)
  let x := CoveringOptimum.cap y
  have hs := hp G hden codec (IntegerStartup.input G d)
    (IntegerStartup.original G d (by omega) hfree) (IntegerStartup.positive_cost G d)
  rw [← solution_eq] at hs
  have hy : CoveringOptimum.Feasible rows (IntegerSetup.Z G d) y := ⟨hs.1.1,hs.1.2.2⟩
  have hxc := CoveringOptimum.cap_feasible rows (IntegerSetup.Z G d) y hy
  have hsupport : ∀ v ∉ IntegerSetup.K G d, x v = 0 := by
    intro v hv
    have hz : y v = 0 := hs.1.2.1 v (fun hm => hv (IntegerStartup.admissible_subset G d hm))
    simp only [x,CoveringOptimum.cap,hz,min_eq_right zero_le_one]
  refine ⟨⟨hxc.1,?_⟩,fun v => min_le_left _ _,hsupport,?_⟩
  · intro r hr
    have hc := hxc.2 r hr
    dsimp only [rows] at hc
    rw [InitialSelection.demand_rows G d (by omega) hr] at hc
    exact hc
  · have hc := hs.2.1
    have hnumber : GeneralCoveringNormalizedFractional.supportedNumber rows (IntegerSetup.Z G d)
        (fun v => (IntegerSetup.c G d v : ℝ)) = InitialSelection.residualOptimum G d := by
      apply GeneralCoveringNormalizedFractional.supportedNumber_eq_number rows (IntegerSetup.Z G d)
        (fun v => (IntegerSetup.c G d v : ℝ))
        (fun r hr => by dsimp only [rows];rw [InitialSelection.demand_rows G d (by omega) hr];exact hfree r)
        (fun _ => Nat.cast_nonneg _)
    change (∑ v, (IntegerSetup.c G d v : ℝ)*y v) ≤
      (1+ε)*GeneralCoveringNormalizedFractional.supportedNumber rows (IntegerSetup.Z G d)
        (fun v => (IntegerSetup.c G d v : ℝ)) at hc
    rw [hnumber] at hc
    exact (CoveringOptimum.cap_cost_le (fun v => (IntegerSetup.c G d v : ℝ)) y
      (fun _ => Nat.cast_nonneg _)).trans hc

theorem parameters (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters ((d:ℝ)/2) d ε,
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G ((d:ℝ)/2) → (∀ v, (G.neighborFinset v).Nonempty) →
        ∀ {ids : ℕ} (codec : BitCode V ids),
        let x := CoveringOptimum.cap (solution G codec p t k b n (by omega))
        CoveringOptimum.Feasible (fun r => G.neighborFinset r) (IntegerSetup.Z G d) x ∧
        (∀ v, x v ≤ 1) ∧ (∀ v ∉ IntegerSetup.K G d, x v = 0) ∧
        (∑ v, (IntegerSetup.c G d v : ℝ)*x v) ≤
          (1+ε)*InitialSelection.residualOptimum G d := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  exact parameters_general ((d:ℝ)/2) (by linarith) d hd ε hε

end Paper.TotalDomination.IntegerResidualSolver
#print axioms Paper.TotalDomination.IntegerResidualSolver.parameters
