import Paper.Solver.LocalSearch.PartialFractionalProgram

namespace Paper.PartialFractionalBudget
open BroadcastModel
variable {V : Type} [LinearOrder V] [Fintype V]

def constant (L Δ r k Q T s a B q M c : ℕ) : ℕ :=
  max ((L + Δ + 4) * (c + 2))
    (max ((L + Δ + 4) * (c + (Δ + 1) ^ (OwnerBoundaryMean.radius k T + 1) * (c + 1) + 2))
      (OwnerRoleSolverBudget.constant L Δ r k Q T s a B q M c))

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q)
    (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (PartialFractionalProgram.program C L Δ r k t Q T s a B q M hQ).maxBits ≤
      constant L Δ r k Q T s a B q M c * Nat.clog 2 (n + 2) := by
  have h₁ := OwnerVirtualPrepare.logarithmic_bits C L Δ n c hids
  have h₂ := OwnerBoundaryMean.logarithmic_bits C L Δ k t Q T hQ n c hids
  have h₃ : (OwnerRoleNumerator.program C L Δ r k t Q T s a B q M hQ).maxBits ≤
      OwnerRoleSolverBudget.constant L Δ r k Q T s a B q M c * Nat.clog 2 (n + 2) := by
    rw [OwnerRoleNumerator.maxBits]
    exact OwnerRoleSolverBudget.logarithmic_bits C L Δ r k t Q T s a B q M hQ n c hids
  rw [PartialFractionalProgram.maxBits]
  exact (max_le_max h₁ (max_le_max h₂ h₃)).trans_eq (by
    unfold constant
    rw [max_mul_mul_right, max_mul_mul_right])

end Paper.PartialFractionalBudget
