import Paper.Endpoints.Rounding.CoveringMixedSolver
import Paper.Endpoints.Rounding.CoveringFractionalRounding

/-! Original private input and exact fractional coordinates for the single
mixed-threshold application of the graph-uniform fractional solver. -/
namespace Paper.CoveringApplicationInput
open BroadcastModel SevenFoundation
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractionalEndpoint.Input

def read {B : ℕ} (s : Input V B) : CoveringThresholdFlags.Input V B :=
  ⟨s.1.residual, s.2, s.1.candidates, s.1.targets, 0⟩

noncomputable def program {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n a : ℕ) (hB : 1 ≤ B) :=
  CoveringMixedSolver.program I a
    (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
    (GeneralCoveringFractionalEndpoint.runtime I p t k b n hB) read (fun z => z.1.val)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def data {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :=
  CoveringMixedSolver.input G
    (GeneralCoveringFractionalEndpoint.runtime I p t k b n hB) read (fun z => z.1.val) s

theorem vector_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    CoveringMixedOutput.vector
      (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
      (data G I p t k b n hB s) =
        GeneralCoveringFractionalEndpoint.solution G I p t k b n hB s := rfl

theorem demands_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    CoveringMixedOutput.demands (data G I p t k b n hB s) = d.R :=
  CoveringFractionalRounding.demands_eq G I p t k b n hB s d

theorem rows_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    CoveringMixedOutput.rows (data G I p t k b n hB s) =
      GeneralCoveringRounding.normalize d.cover d.R :=
  CoveringFractionalRounding.rows_eq G I p t k b n hB s d

theorem incidence {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    ∀ v r, r ∈ (data G I p t k b n hB s v).targets ↔
      v ∈ (data G I p t k b n hB s r).candidates := by
  intro v r
  change r ∈ (s v).1.targets ↔ v ∈ (s r).1.candidates
  rw [d.inverse, d.candidates]
  exact d.incidence v r

theorem admissible_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    GeneralCoveringRounding.admissible (fun r => (data G I p t k b n hB s r).candidates)
      (CoveringMixedOutput.demands (data G I p t k b n hB s)) =
        CoveringSupport.admissible d.cover d.R := by
  rw [demands_eq G I p t k b n hB s d]
  have hc : (fun r => (data G I p t k b n hB s r).candidates) = d.cover := by
    funext r
    exact d.candidates r
  rw [hc]
  rfl

theorem output_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n a : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    Finset.univ.filter (fun v => ((program I p t k b n a hB).runEncoded G s v).selected = true) =
      CoveringMixedCost.output G I a
        (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
        (data G I p t k b n hB s) :=
  CoveringMixedSolver.output_eq G I a _ _ read _ s

end Paper.CoveringApplicationInput

#print axioms Paper.CoveringApplicationInput.vector_eq
#print axioms Paper.CoveringApplicationInput.demands_eq
#print axioms Paper.CoveringApplicationInput.rows_eq
#print axioms Paper.CoveringApplicationInput.incidence
#print axioms Paper.CoveringApplicationInput.admissible_eq
#print axioms Paper.CoveringApplicationInput.output_eq
