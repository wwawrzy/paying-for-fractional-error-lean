import Paper.Owners.Construction.OwnerRoleSolver

namespace Paper.OwnerRoleSolverBudget
open BroadcastModel
variable {V : Type} [LinearOrder V] [Fintype V]

def frameConstant (L Δ r c : ℕ) :=
  max ((L + Δ + 4) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2))
    (c + OwnerFramePayload.capacity Δ r * (c + Δ * (c + 1) + 1) + 1)

def constant (L Δ r k Q T s a B q M c : ℕ) :=
  max (frameConstant L Δ r c)
    (OwnerRoleInputs.capacity L Δ k Q T s *
      ((c + OwnerRoleInputs.metadataCount Δ k Q T s) +
        (3 * c + RecursiveSearch.extraBits (4 * k) a B q M) + 1))

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ)
    (hQ : 0 < Q) (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).maxBits ≤
      constant L Δ r k Q T s a B q M c * Nat.clog 2 (n + 2) := by
  change max (OwnerRoleInputs.program C L Δ r k t Q T s B hQ).maxBits
    (SparseFractional.program C (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s))
      (OwnerRoleInputs.capacity L Δ k Q T s) (4 * k) a B q M).maxBits ≤ _
  apply max_le
  · rw [OwnerRoleInputs.maxBits]
    exact (OwnerRoleFrames.logarithmic_bits C L Δ r k n c hids).trans
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · exact (SparseParallel.logarithmic_bits (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s))
      (OwnerRoleInputs.capacity L Δ k Q T s) (FractionalSearch.program C (4 * k) a B q M) n
      (c + OwnerRoleInputs.metadataCount Δ k Q T s)
      (3 * c + RecursiveSearch.extraBits (4 * k) a B q M)
      (TaskRoleId.logarithmic_width C _ n c hids)
      (FractionalSearch.logarithmic_bits C k a B q M n c hids)).trans
        (Nat.mul_le_mul_right _ (le_max_right _ _))

end Paper.OwnerRoleSolverBudget
