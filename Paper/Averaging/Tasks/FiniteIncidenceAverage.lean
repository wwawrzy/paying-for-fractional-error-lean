import Mathlib

/-! Finite averaging by exact double counting, suitable for deterministic
enumeration of a finite experiment. -/
namespace Paper.FiniteIncidenceAverage
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {I Ω : Type*} [DecidableEq I] [DecidableEq Ω]

theorem incidence (E : Finset I) (W : Finset Ω) (P : I → Ω → Prop) :
    (∑ e ∈ E, (W.filter (P e)).card) = ∑ ω ∈ W, (E.filter (fun e => P e ω)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem bound (E : Finset I) (W : Finset Ω) (hW : W.Nonempty) (P : I → Ω → Prop)
    (C : ℕ) (B : ℝ)
    (hlow : ∀ e ∈ E, W.card ≤ C * (W.filter (P e)).card)
    (hhigh : ∀ ω ∈ W, ((E.filter (fun e => P e ω)).card : ℝ) ≤ B) :
    (E.card : ℝ) ≤ C * B := by
  have hlo : E.card * W.card ≤ C * (∑ ω ∈ W, (E.filter (fun e => P e ω)).card) := by
    calc
      _ = ∑ _e ∈ E, W.card := by simp
      _ ≤ ∑ e ∈ E, C * (W.filter (P e)).card := Finset.sum_le_sum hlow
      _ = _ := by rw [← Finset.mul_sum, incidence]
  have hlo' : (E.card : ℝ) * W.card ≤ C * (∑ ω ∈ W, ((E.filter (fun e => P e ω)).card : ℝ)) := by
    exact_mod_cast hlo
  have hhi : (∑ ω ∈ W, ((E.filter (fun e => P e ω)).card : ℝ)) ≤ W.card * B := by
    calc
      _ ≤ ∑ _ω ∈ W, B := Finset.sum_le_sum hhigh
      _ = _ := by simp [mul_comm]
  have hw : (0 : ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hW
  have hc : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hprod := hlo'.trans (mul_le_mul_of_nonneg_left hhi hc)
  nlinarith
end Paper.FiniteIncidenceAverage
