import Paper.Owners.Construction.OwnerRoleConfigProjection

namespace Paper.RoleTableEncoding

def pack (B Q T F : ℕ) (mask : Fin B → Bool)
    (tables : Fin F → PackedPriorityConfiguration.Table B Q T) : Fin (OwnerRoleMetadata.count B Q T F) :=
  OwnerRoleMetadata.equiv B Q T F (mask, (PackedPriorityConfiguration.flatten B Q T F).symm tables)

theorem mask_pack (B Q T F : ℕ) (mask : Fin B → Bool)
    (tables : Fin F → PackedPriorityConfiguration.Table B Q T) :
    OwnerRoleMetadata.mask B Q T F (pack B Q T F mask tables) = mask :=
  OwnerRoleMetadata.mask_encode B Q T F _

theorem table_pack (B Q T F : ℕ) (mask : Fin B → Bool)
    (tables : Fin F → PackedPriorityConfiguration.Table B Q T) :
    OwnerRoleMetadata.table B Q T F (pack B Q T F mask tables) = tables := by
  change (PackedPriorityConfiguration.flatten B Q T F)
    (OwnerRoleMetadata.configuration B Q T F (pack B Q T F mask tables)) = tables
  rw [pack, OwnerRoleMetadata.configuration_encode, Equiv.apply_symm_apply]

def equiv (B Q T F : ℕ) :
    ((Fin B → Bool) × (Fin F → PackedPriorityConfiguration.Table B Q T)) ≃
      Fin (OwnerRoleMetadata.count B Q T F) :=
  (Equiv.prodCongr (Equiv.refl _) (PackedPriorityConfiguration.flatten B Q T F).symm).trans
    (OwnerRoleMetadata.equiv B Q T F)

theorem sum_pack {A : Type} [AddCommMonoid A] (B Q T F : ℕ)
    (f : Fin (OwnerRoleMetadata.count B Q T F) → A) :
    (∑ i, f i) = ∑ mask : Fin B → Bool,
      ∑ tables : Fin F → PackedPriorityConfiguration.Table B Q T, f (pack B Q T F mask tables) := by
  calc
    _ = ∑ p : (Fin B → Bool) × (Fin F → PackedPriorityConfiguration.Table B Q T),
        f (equiv B Q T F p) := (Fintype.sum_equiv (equiv B Q T F) _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

end Paper.RoleTableEncoding
