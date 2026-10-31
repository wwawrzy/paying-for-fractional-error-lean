import Paper.Solver.LocalSearch.GeneralCoveringFractionalEndpoint
import Paper.Endpoints.Rounding.CoveringApproximateRounding

/-! Execute numerical rounding directly on the original covering solver input. -/
namespace Paper.CoveringFractionalRounding
open BroadcastModel SevenFoundation
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [LinearOrder V]

def read {B : ℕ} (s : GeneralCoveringFractionalEndpoint.Input V B) :
    CoveringThresholdInput.Input V B :=
  ⟨s.1.residual, s.2, s.1.candidates, 0⟩

noncomputable def program {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n threshold : ℕ) (hB : 1 ≤ B) :=
  CoveringSolverRounding.program I threshold
    (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
    (GeneralCoveringFractionalEndpoint.runtime I p t k b n hB) read (fun z => z.1.val)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def data {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B) :=
  CoveringSolverRounding.input G
    (GeneralCoveringFractionalEndpoint.runtime I p t k b n hB) read (fun z => z.1.val) s

theorem vector_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B) :
    CoveringThresholdCost.vector
      (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
      (data G I p t k b n hB s) =
        GeneralCoveringFractionalEndpoint.solution G I p t k b n hB s := rfl

theorem demands_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    CoveringThresholdCost.demands (data G I p t k b n hB s) = d.R := by
  ext r
  simp only [CoveringThresholdCost.demands, Finset.mem_filter, Finset.mem_univ, true_and]
  change (s r).1.residual = true ↔ r ∈ d.R
  rw [d.residual]
  simp

theorem rows_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    CoveringThresholdCost.rows (data G I p t k b n hB s) =
      GeneralCoveringRounding.normalize d.cover d.R := by
  unfold CoveringThresholdCost.rows
  rw [demands_eq G I p t k b n hB s d]
  have hc : (fun r => (data G I p t k b n hB s r).candidates) = d.cover := by
    funext r
    exact d.candidates r
  rw [hc]

theorem rounds {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n threshold : ℕ) (hB : 1 ≤ B) :
    (program I p t k b n threshold hB).rounds =
      (GeneralCoveringFractionalEndpoint.runtime I p t k b n hB).rounds + 3 :=
  CoveringSolverRounding.rounds I threshold _ _ read _

theorem output_eq {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n threshold : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B) :
    Finset.univ.filter (fun v => ((program I p t k b n threshold hB).runEncoded G s v).selected = true) =
      CoveringThresholdCost.output G I threshold
        (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
        (data G I p t k b n hB s) :=
  CoveringSolverRounding.output_eq G I threshold _ _ read _ s

theorem local_rows {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    ∀ r, (data G I p t k b n hB s r).demand = true →
      (data G I p t k b n hB s r).candidates ⊆ closed G r := by
  intro r hr
  change (s r).1.residual = true at hr
  rw [d.residual, decide_eq_true_eq] at hr
  change (s r).1.candidates ⊆ closed G r
  rw [d.candidates]
  exact d.local_rows r hr

theorem nonempty_rows {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s) :
    ∀ r, (data G I p t k b n hB s r).demand = true →
      (data G I p t k b n hB s r).candidates.Nonempty := by
  intro r hr
  change (s r).1.residual = true at hr
  rw [d.residual, decide_eq_true_eq] at hr
  change (s r).1.candidates.Nonempty
  rw [d.candidates]
  exact d.rows r hr

theorem feasible_rows {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringFractionalEndpoint.Input V B)
    (d : GeneralCoveringInitializedFrameAverage.Original G s)
    (hf : feasible (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2))
      (GeneralCoveringFractionalEndpoint.solution G I p t k b n hB s)) :
    ∀ r, (data G I p t k b n hB s r).demand = true →
      1 ≤ ∑ v ∈ (data G I p t k b n hB s r).candidates,
        CoveringThresholdCost.vector
          (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
          (data G I p t k b n hB s) v := by
  intro r hr
  change (s r).1.residual = true at hr
  rw [d.residual, decide_eq_true_eq] at hr
  rw [vector_eq]
  change 1 ≤ ∑ v ∈ (s r).1.candidates,
    GeneralCoveringFractionalEndpoint.solution G I p t k b n hB s v
  rw [d.candidates]
  exact hf.2.2 r hr

end Paper.CoveringFractionalRounding

#print axioms Paper.CoveringFractionalRounding.vector_eq
#print axioms Paper.CoveringFractionalRounding.demands_eq
#print axioms Paper.CoveringFractionalRounding.rows_eq
#print axioms Paper.CoveringFractionalRounding.rounds
#print axioms Paper.CoveringFractionalRounding.output_eq
