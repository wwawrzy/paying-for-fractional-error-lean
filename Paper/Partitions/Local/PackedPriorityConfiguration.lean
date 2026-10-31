import Paper.Owners.Construction.OwnerRoleMetadata
import Paper.Averaging.Tasks.FiniteLocalMean

/-! Exact reindexing from role configuration numbers to padded priority
tables, and their uniform local/global averaging identity. -/
namespace Paper.PackedPriorityConfiguration
open scoped BigOperators

abbrev Table (B Q T : ℕ) := (Fin T × (Fin B → Bool)) → Fin Q

def flatten (B Q T F : ℕ) :
    (Fin (OwnerRoleMetadata.slots B T F) → Fin Q) ≃ (Fin F → Table B Q T) where
  toFun f u p := f (finProdFinEquiv (u, finProdFinEquiv (p.1, PriorityTableCode.masks B p.2)))
  invFun f i := f (finProdFinEquiv.symm i).1
    ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1,
      (PriorityTableCode.masks B).symm (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2)
  left_inv f := by funext i; simp only [Equiv.apply_symm_apply, Prod.mk.eta]
  right_inv f := by funext u p; simp only [Equiv.symm_apply_apply, Prod.mk.eta]

def numbered (B Q T F : ℕ) : Fin (Q ^ OwnerRoleMetadata.slots B T F) ≃ (Fin F → Table B Q T) :=
  (FiniteWordCode.words Q (OwnerRoleMetadata.slots B T F)).symm.trans (flatten B Q T F)

theorem sum_numbered {A : Type} [AddCommMonoid A] (B Q T F : ℕ)
    (f : (Fin F → Table B Q T) → A) :
    (∑ i : Fin (Q ^ OwnerRoleMetadata.slots B T F), f (numbered B Q T F i)) =
      ∑ ω : Fin F → Table B Q T, f ω :=
  Fintype.sum_equiv (numbered B Q T F) _ _ (fun _ => rfl)

theorem sum_metadata {A : Type} [AddCommMonoid A] (B Q T F : ℕ)
    (f : (Fin B → Bool) → (Fin (OwnerRoleMetadata.slots B T F) → Fin Q) → A) :
    (∑ i : Fin (OwnerRoleMetadata.count B Q T F),
      f (OwnerRoleMetadata.mask B Q T F i) (OwnerRoleMetadata.configuration B Q T F i)) =
      ∑ ω : Fin B → Bool, ∑ cfg : Fin (OwnerRoleMetadata.slots B T F) → Fin Q, f ω cfg := by
  calc
    _ = ∑ d : OwnerRoleMetadata.Data B Q T F, f d.1 d.2 :=
      Fintype.sum_equiv (OwnerRoleMetadata.equiv B Q T F).symm _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

theorem denominator_eq (B Q T F : ℕ) :
    Q ^ OwnerRoleMetadata.slots B T F = FiniteLocalMean.denominator (Table B Q T) F := by
  simp only [OwnerRoleMetadata.slots, FiniteLocalMean.denominator, Fintype.card_fun,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, ← pow_mul, Nat.mul_comm F]

variable {V : Type} [LinearOrder V] [Fintype V]

theorem mean_eq (B Q T F : ℕ) (hQ : 0 < Q) (l : List V) (hl : l.Nodup) (hF : l.length ≤ F)
    (f : List (V × Table B Q T) → ℝ) :
    (∑ i : Fin (Q ^ OwnerRoleMetadata.slots B T F),
      f (LocalSeedRecords.records l hF (numbered B Q T F i))) / (Q ^ OwnerRoleMetadata.slots B T F : ℕ) =
      (∑ σ : V → Table B Q T, f (LocalSeedRecords.base l (fun i => σ (l.get i)))) /
        (Fintype.card (V → Table B Q T) : ℝ) := by
  letI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  rw [sum_numbered B Q T F (fun ω => f (LocalSeedRecords.records l hF ω)), denominator_eq]
  exact FiniteLocalMean.mean_eq l hl hF f

end Paper.PackedPriorityConfiguration
