import Paper.Endpoints.Rounding.CoveringApplicationInput

/-! Graph-independent rounds and logarithmic broadcast width for the same
algorithm used in the covering application endpoint. -/
namespace Paper.CoveringApplicationResources
open BroadcastModel CoveringApplicationInput
variable {V : Type} [Fintype V] [LinearOrder V]

theorem rounds {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n a : ℕ) (hB : 1 ≤ B) :
    (program I p t k b n a hB).rounds =
      GeneralCoveringInitializerFractional.scale ρ * (5 + 2 * GeneralCoveringInitializerFractional.listThreshold ρ) +
        18 + 4 * GeneralCoveringOwnerFrameTaskInputs.outerRadius k n +
        RecursiveSearch.roundBound (4 * k) p.A (GeneralCoveringTaskFractionalSolve.numeratorBound p.A B k p.q) + 4 := by
  simp only [program, CoveringMixedSolver.rounds, GeneralCoveringFractionalEndpoint.rounds]

theorem logarithmic_bits {ids : ℕ} (I : BitCode V ids) {ρ δ : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters ρ B δ)
    (t k b n a : ℕ) (hB : 1 ≤ B) (N c : ℕ) (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (program I p t k b n a hB).maxBits ≤
      (GeneralCoveringFrameAverageResources.coefficient (GeneralCoveringInitializerFractional.listThreshold ρ)
        p.L p.Δ p.A B k b n p.q c + B + c + 3) * Nat.clog 2 (N + 2) := by
  let H := Nat.clog 2 (N + 2)
  let C := GeneralCoveringFrameAverageResources.coefficient (GeneralCoveringInitializerFractional.listThreshold ρ)
    p.L p.Δ p.A B k b n p.q c
  have hH : 1 ≤ H := Nat.clog_pos (by omega) (by omega)
  have hi : ids + 1 ≤ (c + 1) * H := by nlinarith [hids]
  have hB' : B + 2 ≤ (B + 2) * H := by nlinarith
  have hs := GeneralCoveringFractionalEndpoint.logarithmic_bits I p t k b n hB N c hids
  have hm := CoveringMixedSolver.maxBits I a
    (GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q)
    (GeneralCoveringFractionalEndpoint.runtime I p t k b n hB) read (fun z => z.1.val)
  apply hm.trans
  apply max_le
  · exact hs.trans (Nat.mul_le_mul_right H (by omega))
  · apply max_le
    · exact hB'.trans (Nat.mul_le_mul_right H (by omega))
    · exact hi.trans (Nat.mul_le_mul_right H (by omega))

end Paper.CoveringApplicationResources

#print axioms Paper.CoveringApplicationResources.rounds
#print axioms Paper.CoveringApplicationResources.logarithmic_bits
