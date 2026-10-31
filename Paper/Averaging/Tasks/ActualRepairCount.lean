import Paper.Owners.Construction.OwnerCompilerBound
import Paper.Owners.Construction.OwnerVirtualFacts

namespace Paper.ActualRepairCount
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

theorem image_card (D : Finset V) (Q : Finset D) : (PublicOwners.image D Q).card ≤ D.card := by
  apply Finset.card_le_card
  intro v hv
  obtain ⟨d, he, _⟩ := (PublicOwners.mem_image D Q v).mp hv
  exact he ▸ d.property

set_option maxHeartbeats 1000000 in
theorem bound (D R : Finset V) (hcover : R ⊆ covered G D) (L Δ : ℕ)
    (a : ℕ) (ha : 1 ≤ a) (hL : 4 * (a : ℝ) ≤ L) (hΔ : 1 ≤ Δ)
    (hden : MinorDensity.Bound G (a : ℝ)) (t : ℕ) (η : ℝ) (hη : 0 < η)
    (ht : (8 / (t : ℝ)) ≤ η) :
    ((HeavyRepair.heavy G D R L).card : ℝ) + (OwnerVirtualFacts.high G D R L Δ).card +
      (16 / (t : ℝ)) * (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)).card ≤
        OwnerCompilerBound.factor a L Δ η * D.card := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hLpos : (0 : ℝ) < L := by linarith
  have hLNat : 1 ≤ L := by
    have hp : 0 < L := by exact_mod_cast hLpos
    omega
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  let Q := OwnerVirtualFacts.high G D R L Δ
  have hp := HeavyRepair.count_div G D R hcover L haR hL hden
  have hhigh := OwnerHighRepair.count G D R L Δ hLNat hden (Nat.cast_nonneg a)
  have hSel : (OwnerHighRepair.selected G D R L Δ).card = Q.card := by
    exact Finset.card_image_of_injective _ Subtype.val_injective
  rw [hSel] at hhigh
  have hq : (Q.card : ℝ) ≤ 2 * ((a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) * D.card / Δ :=
    (le_div_iff₀ hΔpos).mpr (by simpa only [mul_comm] using hhigh)
  have hCard : ((PublicOwners.image D Q).card : ℝ) ≤ D.card := by exact_mod_cast image_card D Q
  have hnonneg : 0 ≤ (16 / (t : ℝ)) := by positivity
  have hrate : 16 / (t : ℝ) ≤ 2 * η := by
    calc
      _ = 2 * (8 / (t : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by norm_num)
  have hboundary := (mul_le_mul_of_nonneg_left hCard hnonneg).trans
    (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg D.card))
  calc
    _ ≤ 2 * (a : ℝ) * D.card / L +
      2 * ((a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) * D.card / Δ + 2 * η * D.card :=
      add_le_add (add_le_add hp hq) hboundary
    _ = _ := by unfold OwnerCompilerBound.factor; ring

end Paper.ActualRepairCount
