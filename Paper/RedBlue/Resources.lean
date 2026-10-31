import Paper.RedBlue.IntegralEndpoint

/-! Resource bounds for the same solver-rounding program used by the endpoint. -/
namespace Paper.RedBlue
open BroadcastModel
variable {V : Type} [LinearOrder V]

theorem integral_rounds {ids M : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) :
    (integralProgram I p t k b n hM).rounds =
      (GeneralCoveringFractionalEndpoint.runtime I p t k b n hM).rounds + 3 :=
  CoveringSolverRounding.rounds I 4 _ _ _ _

theorem integral_bits {ids M : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) :
    (integralProgram I p t k b n hM).maxBits ≤
      max (GeneralCoveringFractionalEndpoint.runtime I p t k b n hM).maxBits
        (max (M + 2) (ids + 1)) :=
  CoveringSolverRounding.maxBits I 4 _ _ _ _

variable [Fintype V]

theorem integral_round_bound {ids M : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) :
    (integralProgram I p t k b n hM).rounds =
      GeneralCoveringInitializerFractional.scale 3 *
        (5 + 2 * GeneralCoveringInitializerFractional.listThreshold 3) +
        18 + 4 * GeneralCoveringOwnerFrameTaskInputs.outerRadius k n +
        RecursiveSearch.roundBound (4 * k) p.A
          (GeneralCoveringTaskFractionalSolve.numeratorBound p.A M k p.q) + 3 := by
  rw [integral_rounds, GeneralCoveringFractionalEndpoint.rounds]

theorem integral_logarithmic_bits {ids M : ℕ} (I : BitCode V ids) {ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters 3 M ε)
    (t k b n : ℕ) (hM : 1 ≤ M) (N c : ℕ)
    (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (integralProgram I p t k b n hM).maxBits ≤
      (GeneralCoveringFrameAverageResources.coefficient
        (GeneralCoveringInitializerFractional.listThreshold 3)
        p.L p.Δ p.A M k b n p.q c + M + c + 3) * Nat.clog 2 (N + 2) := by
  let H := Nat.clog 2 (N + 2)
  have hH : 1 ≤ H := Nat.clog_pos (by omega) (by omega)
  have hi : ids + 1 ≤ (c + 1) * H := by nlinarith [hids]
  have hM' : M + 2 ≤ (M + 2) * H := by nlinarith
  have hs := GeneralCoveringFractionalEndpoint.logarithmic_bits I p t k b n hM N c hids
  apply (integral_bits I p t k b n hM).trans
  apply max_le
  · exact hs.trans (Nat.mul_le_mul_right H (by omega))
  · apply max_le
    · exact hM'.trans (Nat.mul_le_mul_right H (by omega))
    · exact hi.trans (Nat.mul_le_mul_right H (by omega))

end Paper.RedBlue
#print axioms Paper.RedBlue.integral_rounds
#print axioms Paper.RedBlue.integral_bits
#print axioms Paper.RedBlue.integral_round_bound
#print axioms Paper.RedBlue.integral_logarithmic_bits
