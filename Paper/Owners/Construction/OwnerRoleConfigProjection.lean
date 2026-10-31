import Paper.Partitions.Local.PackedPriorityConfiguration

/-! Explicit projection of a global priority source into one fixed role
configuration. This is used only to prove coverage of the local enumeration. -/
namespace Paper.OwnerRoleConfigProjection
variable {V : Type}

def pad {A : Type} (l : List V) (F : ℕ) (fallback : A) (ζ : V → A) : Fin F → A :=
  fun i => if hi : i.val < l.length then ζ (l.get ⟨i.val, hi⟩) else fallback

theorem pad_slot {A : Type} (l : List V) (F : ℕ) (hF : l.length ≤ F) (fallback : A)
    (ζ : V → A) (j : Fin l.length) : pad l F fallback ζ (LocalSeedRecords.slot l hF j) = ζ (l.get j) := by
  simp only [pad, LocalSeedRecords.slot, dif_pos j.isLt]

def project (B Q T F : ℕ) (hQ : 0 < Q) (l : List V)
    (ζ : V → PackedPriorityConfiguration.Table B Q T) (mask : Fin B → Bool) :
    Fin (OwnerRoleMetadata.count B Q T F) :=
  OwnerRoleMetadata.equiv B Q T F
    (mask, (PackedPriorityConfiguration.flatten B Q T F).symm (pad l F (fun _ => ⟨0, hQ⟩) ζ))

theorem mask_project (B Q T F : ℕ) (hQ : 0 < Q) (l : List V)
    (ζ : V → PackedPriorityConfiguration.Table B Q T) (mask : Fin B → Bool) :
    OwnerRoleMetadata.mask B Q T F (project B Q T F hQ l ζ mask) = mask :=
  OwnerRoleMetadata.mask_encode B Q T F _

theorem table_project (B Q T F : ℕ) (hQ : 0 < Q) (l : List V) (hF : l.length ≤ F)
    (ζ : V → PackedPriorityConfiguration.Table B Q T) (mask : Fin B → Bool) (j : Fin l.length) :
    OwnerRoleMetadata.table B Q T F (project B Q T F hQ l ζ mask) (LocalSeedRecords.slot l hF j) =
      ζ (l.get j) := by
  have he : OwnerRoleMetadata.table B Q T F (project B Q T F hQ l ζ mask) =
      pad l F (fun _ => ⟨0, hQ⟩) ζ := by
    change (PackedPriorityConfiguration.flatten B Q T F)
      (OwnerRoleMetadata.configuration B Q T F (project B Q T F hQ l ζ mask)) = _
    rw [project, OwnerRoleMetadata.configuration_encode, Equiv.apply_symm_apply]
  rw [he]
  exact pad_slot l F hF _ ζ j

end Paper.OwnerRoleConfigProjection
