import Paper.Preliminaries.LocalSeedRecords
import Paper.Preliminaries.UniformProjection

/-! Exact local enumeration with a fixed padded denominator. The global
source space appears only in the proof of equality of averages. -/
namespace Paper.FiniteLocalMean
open scoped BigOperators
variable {V A : Type} [LinearOrder V] [Fintype A]

def denominator (A : Type) [Fintype A] (K : ℕ) : ℕ := Fintype.card A ^ K

def numerator (l : List V) {K : ℕ} (hK : l.length ≤ K) (f : List (V × A) → ℕ) : ℕ :=
  ∑ ω : Fin K → A, f (LocalSeedRecords.records l hK ω)

theorem denominator_pos [Nonempty A] (K : ℕ) : 0 < denominator A K :=
  pow_pos Fintype.card_pos K

theorem numerator_le (l : List V) {K : ℕ} (hK : l.length ≤ K)
    (f : List (V × A) → ℕ) (M : ℕ) (hf : ∀ ω, f (LocalSeedRecords.records l hK ω) ≤ M) :
    numerator l hK f ≤ denominator A K * M := by
  calc
    _ ≤ ∑ _ω : Fin K → A, M := Finset.sum_le_sum (fun ω _ => hf ω)
    _ = _ := by simp [denominator, Fintype.card_fun]

variable [Fintype V] [Nonempty A]

theorem mean_eq (l : List V) (hl : l.Nodup) {K : ℕ} (hK : l.length ≤ K)
    (f : List (V × A) → ℝ) :
    (∑ ω : Fin K → A, f (LocalSeedRecords.records l hK ω)) / (denominator A K : ℝ) =
      (∑ σ : V → A, f (LocalSeedRecords.base l (fun i => σ (l.get i)))) /
        (Fintype.card (V → A) : ℝ) := by
  let g : (Fin l.length → A) → ℝ := fun τ => f (LocalSeedRecords.base l τ)
  have hglobal := UniformProjection.sum_scaled l.get hl.injective_get g
  have hpad := UniformProjection.sum_scaled (LocalSeedRecords.slot l hK)
    (LocalSeedRecords.slot_injective l hK) g
  have hi : (0 : ℝ) < Fintype.card (Fin l.length → A) := by exact_mod_cast Fintype.card_pos
  have hv : (0 : ℝ) < Fintype.card (V → A) := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < Fintype.card (Fin K → A) := by exact_mod_cast Fintype.card_pos
  have he :
      (∑ ω : Fin K → A, g (fun i => ω (LocalSeedRecords.slot l hK i))) /
          (Fintype.card (Fin K → A) : ℝ) =
        (∑ σ : V → A, g (fun i => σ (l.get i))) / (Fintype.card (V → A) : ℝ) := by
    apply (div_eq_div_iff (ne_of_gt hk) (ne_of_gt hv)).mpr
    apply (mul_left_cancel₀ (ne_of_gt hi))
    calc
      _ = (Fintype.card (Fin l.length → A) *
          (∑ ω : Fin K → A, g (fun i => ω (LocalSeedRecords.slot l hK i)))) *
          Fintype.card (V → A) := by ring
      _ = (Fintype.card (Fin K → A) * ∑ τ : Fin l.length → A, g τ) *
          Fintype.card (V → A) := by rw [hpad]
      _ = (Fintype.card (Fin l.length → A) * (∑ σ : V → A, g (fun i => σ (l.get i)))) *
          Fintype.card (Fin K → A) := by rw [hglobal]; ring
      _ = _ := by ring
  simpa only [g, LocalSeedRecords.records, Fintype.card_fun, Fintype.card_fin, denominator] using he

theorem numerator_mean_eq (l : List V) (hl : l.Nodup) {K : ℕ} (hK : l.length ≤ K)
    (f : List (V × A) → ℕ) :
    (numerator l hK f : ℝ) / denominator A K =
      (∑ σ : V → A, (f (LocalSeedRecords.base l (fun i => σ (l.get i))) : ℝ)) /
        (Fintype.card (V → A) : ℝ) := by
  simpa only [numerator, Nat.cast_sum] using mean_eq l hl hK (fun xs => (f xs : ℝ))
end Paper.FiniteLocalMean
