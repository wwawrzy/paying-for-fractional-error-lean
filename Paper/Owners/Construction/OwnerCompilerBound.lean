import Paper.Owners.Construction.OwnerCompilerMath

/-! Substitute the actual two repair-count bounds into the actual averaged
compiler. The proved owner density constant is a*(L+1)^4. -/
namespace Paper.OwnerCompilerBound
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def factor (a L Δ : ℕ) (η : ℝ) : ℝ :=
  2 * (a : ℝ) / L + 2 * ((a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) / Δ + 2 * η

set_option maxHeartbeats 1000000 in
theorem spec (D R : Finset V) (hcover : R ⊆ covered G D) (L Δ : ℕ)
    (a : ℕ) (ha : 1 ≤ a) (hL : 4 * (a : ℝ) ≤ L) (hΔ : 1 ≤ Δ)
    (hden : MinorDensity.Bound G (a : ℝ))
    (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hcost : ∀ v, c v ≤ B₀)
    (ξ η : ℝ) (hξ : 0 < ξ) (hη : 0 < η) :
    ∃ x : V → ℝ, PartialOptimum.Feasible G R x ∧
      PartialOptimum.objective c x ≤ (1 + ξ) * PartialOptimum.number G R c +
        B₀ * factor a L Δ η * D.card := by
  classical
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hLpos : (0 : ℝ) < L := by linarith
  have hLNat : 1 ≤ L := by
    have hp : 0 < L := by exact_mod_cast hLpos
    omega
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  let Q := HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ
  obtain ⟨x, hx, hxcost⟩ := OwnerCompilerMath.spec G D R hcover L Δ hLNat a ha hden c hc B₀ hB₀ hcost ξ η hξ hη
  have hp := HeavyRepair.count_div G D R hcover L haR hL hden
  have hhigh := OwnerHighRepair.count G D R L Δ hLNat hden (Nat.cast_nonneg a)
  have hSel : (OwnerHighRepair.selected G D R L Δ).card = Q.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [hSel] at hhigh
  have hq : (Q.card : ℝ) ≤ 2 * ((a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) * D.card / Δ :=
    (le_div_iff₀ hΔpos).mpr (by simpa only [mul_comm] using hhigh)
  have hrepair : ((HeavyRepair.heavy G D R L).card : ℝ) + Q.card + 2 * η * D.card ≤
      factor a L Δ η * D.card := by
    calc
      _ ≤ 2 * (a : ℝ) * D.card / L +
          2 * ((a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) * D.card / Δ + 2 * η * D.card :=
        add_le_add (add_le_add hp hq) le_rfl
      _ = _ := by unfold factor; ring
  refine ⟨x, hx, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hrepair hB₀
  nlinarith
end Paper.OwnerCompilerBound
