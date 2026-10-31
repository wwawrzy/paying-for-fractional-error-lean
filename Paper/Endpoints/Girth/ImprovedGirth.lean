import Paper.Endpoints.Rounding.ImprovedExcessSolver
import Paper.Endpoints.Girth.NoncriticalGirth
import Paper.Averaging.Tasks.KT0Compiler

/-! The exact improved-girth corollary `fv:imp:girth`. The output is the
actual encoded KT0 port execution, with no neighbor-ID table supplied.
Existing planar girth-density and nonintegrality facts are reused unchanged. -/
namespace Paper.ImprovedGirth
open BroadcastModel SevenFoundation

/-- The paper's limiting coefficient, with its exact square-root gain. -/
noncomputable def limitingCoefficient (g : ℕ) : ℝ :=
  2 * (NoncriticalGirth.density g : ℝ) + 1 -
    ImprovedExcess.muMax (NoncriticalGirth.density g : ℝ)
      (ImprovedExcessEndpoint.gap (NoncriticalGirth.density g))

variable {V : Type} [LinearOrder V]

noncomputable def program {a : ℚ} {b : ℕ} (C : BitCode V b)
    (p : ImprovedExcessSolver.Config a) : PortBroadcastModel.Program V Unit Bool :=
  KT0Compiler.program C (ImprovedExcessSolver.program C p)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def output {a : ℚ} (ports : PortBroadcastModel.Numbering G)
    {b : ℕ} (C : BitCode V b) (p : ImprovedExcessSolver.Config a) : Finset V :=
  Finset.univ.filter fun v => (program C p).runEncoded G ports (fun _ => ()) v

theorem output_eq {a : ℚ} (ports : PortBroadcastModel.Numbering G) {b : ℕ}
    (C : BitCode V b) (p : ImprovedExcessSolver.Config a) :
    output G ports C p = ImprovedExcessSolver.output G C p := by
  unfold output program
  rw [KT0Compiler.program_encoded_correct]
  rfl

theorem rounds {a : ℚ} {b : ℕ} (C : BitCode V b) (p : ImprovedExcessSolver.Config a) :
    (program C p).rounds = 1 + ImprovedExcessSolver.roundBound p := by
  rw [program, KT0Compiler.program_rounds, ImprovedExcessSolver.rounds]

theorem logarithmic_bits {a : ℚ} {b : ℕ} (C : BitCode V b)
    (p : ImprovedExcessSolver.Config a) (n d : ℕ) (hids : b ≤ d * Nat.clog 2 (n + 2)) :
    (program C p).maxBits ≤ max d (ImprovedExcessSolver.messageConstant p d) * Nat.clog 2 (n + 2) :=
  KT0Compiler.logarithmic_bits C (ImprovedExcessSolver.program C p) n d _ hids
    (ImprovedExcessSolver.logarithmic_bits C p n d hids)

/-- Public choices precede the vertex type, graph, physical port numbering
and ID codec. The output has no additive error and uses only unit inputs. -/
theorem parameters (g : ℕ) (hg : 5 ≤ g) (hne : g ≠ 6) (c : ℚ)
    (hc : limitingCoefficient g < (c : ℝ)) :
    ∃ p : ImprovedExcessSolver.Config (NoncriticalGirth.density g),
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar →
        (∀ (v : V) (cycle : G.Walk v v), cycle.IsCycle → g ≤ cycle.length) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
          dominates G (output G ports C p) ∧
          ((output G ports C p).card : ℝ) ≤ (c : ℝ) * fractionalNumber G ∧
          (program C p).rounds = 1 + ImprovedExcessSolver.roundBound p ∧
          ∀ n d, b ≤ d * Nat.clog 2 (n + 2) →
            (program C p).maxBits ≤
              max d (ImprovedExcessSolver.messageConstant p d) * Nat.clog 2 (n + 2) := by
  have hg3 : 3 ≤ g := by omega
  obtain ⟨p, hp⟩ := ImprovedExcessSolver.parameters (NoncriticalGirth.density g)
    (NoncriticalGirth.density_bounds g hg3).1 (NoncriticalGirth.density_noninteger g hg hne)
    (c : ℝ) hc
  refine ⟨p, ?_⟩
  intro V _ _ G _ hplanar hgirth ports b C
  have hminor := PlanarDensity.minor_density G hplanar
  have hsub := CurrentPlanarFaceBound.induced_density hplanar g hg3 hgirth
  rw [← NoncriticalGirth.density_cast] at hsub
  have h := hp G hminor hsub C
  rw [output_eq]
  exact ⟨h.1, h.2.1, rounds C p, fun n d hids => logarithmic_bits C p n d hids⟩

end Paper.ImprovedGirth
#print axioms Paper.ImprovedGirth.output_eq
#print axioms Paper.ImprovedGirth.rounds
#print axioms Paper.ImprovedGirth.logarithmic_bits
#print axioms Paper.ImprovedGirth.parameters
