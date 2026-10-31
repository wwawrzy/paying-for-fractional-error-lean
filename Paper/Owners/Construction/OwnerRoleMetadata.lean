import Paper.Preliminaries.FiniteWordCode
import Paper.Averaging.Tasks.TaskRoleId

/-! Concrete fixed metadata for a role: one subset mask and one padded
local priority configuration. The only variable part of its public ID is
the physical anchor identifier. -/
namespace Paper.OwnerRoleMetadata

def slots (B T F : ℕ) : ℕ := F * (T * 2 ^ B)
def count (B Q T F : ℕ) : ℕ := 2 ^ B * Q ^ slots B T F

abbrev Data (B Q T F : ℕ) := (Fin B → Bool) × (Fin (slots B T F) → Fin Q)

def equiv (B Q T F : ℕ) : Data B Q T F ≃ Fin (count B Q T F) :=
  (Equiv.prodCongr (PriorityTableCode.masks B) (FiniteWordCode.words Q (slots B T F))).trans
    finProdFinEquiv

def mask (B Q T F : ℕ) (i : Fin (count B Q T F)) : Fin B → Bool :=
  ((equiv B Q T F).symm i).1

def configuration (B Q T F : ℕ) (i : Fin (count B Q T F)) : Fin (slots B T F) → Fin Q :=
  ((equiv B Q T F).symm i).2

def table (B Q T F : ℕ) (i : Fin (count B Q T F)) (u : Fin F) :
    (Fin T × (Fin B → Bool)) → Fin Q := fun p =>
  configuration B Q T F i (finProdFinEquiv (u, finProdFinEquiv (p.1, PriorityTableCode.masks B p.2)))

theorem mask_encode (B Q T F : ℕ) (d : Data B Q T F) :
    mask B Q T F (equiv B Q T F d) = d.1 := by
  exact congrArg Prod.fst ((equiv B Q T F).symm_apply_apply d)

theorem configuration_encode (B Q T F : ℕ) (d : Data B Q T F) :
    configuration B Q T F (equiv B Q T F d) = d.2 := by
  exact congrArg Prod.snd ((equiv B Q T F).symm_apply_apply d)

theorem encode_decode (B Q T F : ℕ) (i : Fin (count B Q T F)) :
    equiv B Q T F (mask B Q T F i, configuration B Q T F i) = i :=
  (equiv B Q T F).apply_symm_apply i

theorem positive (B Q T F : ℕ) (hQ : 0 < Q) : 0 < count B Q T F :=
  Nat.mul_pos (pow_pos (by omega) _) (pow_pos hQ _)

end Paper.OwnerRoleMetadata
