import Mathlib

/-! Exact uniform finite averaging under an injective coordinate map.
Unused coordinates contribute a constant fiber factor, explicitly proved
by splitting a function into used and unused coordinates. -/
namespace Paper.UniformProjection
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {I A B : Type*}

noncomputable def split (e : I → A) (hinj : Function.Injective e) :
    (A → B) ≃ (I → B) × ({a // a ∉ Set.range e} → B) where
  toFun ω := (fun i => ω (e i), fun a => ω a.val)
  invFun p a := if ha : a ∈ Set.range e then p.1 (Classical.choose ha) else p.2 ⟨a, ha⟩
  left_inv ω := by
    funext a
    by_cases ha : a ∈ Set.range e
    · simp only [dif_pos ha]
      exact congrArg ω (Classical.choose_spec ha)
    · simp only [dif_neg ha]
  right_inv p := by
    apply Prod.ext
    · funext i
      have ha : e i ∈ Set.range e := ⟨i, rfl⟩
      simp only [dif_pos ha]
      exact congrArg p.1 (hinj (Classical.choose_spec ha))
    · funext a
      simp only [dif_neg a.property]

theorem sum_fibers [Fintype I] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq A]
    (e : I → A) (hinj : Function.Injective e) (f : (I → B) → ℝ) :
    (∑ ω : A → B, f (fun i => ω (e i))) =
      Fintype.card ({a // a ∉ Set.range e} → B) * ∑ τ : I → B, f τ := by
  classical
  calc
    _ = ∑ p : (I → B) × ({a // a ∉ Set.range e} → B), f p.1 :=
      Fintype.sum_equiv (split e hinj) _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; simp [← Finset.mul_sum]

theorem sum_scaled [Fintype I] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq A]
    (e : I → A) (hinj : Function.Injective e) (f : (I → B) → ℝ) :
    (Fintype.card (I → B) : ℝ) * (∑ ω : A → B, f (fun i => ω (e i))) =
      Fintype.card (A → B) * ∑ τ : I → B, f τ := by
  classical
  have hc := Fintype.card_congr (split (B := B) e hinj)
  have hr : (Fintype.card (A → B) : ℝ) =
      Fintype.card (I → B) * Fintype.card ({a // a ∉ Set.range e} → B) := by
    exact_mod_cast hc.trans (Fintype.card_prod _ _)
  rw [sum_fibers e hinj f, hr]
  ring

theorem bound [Fintype I] [Fintype A] [Fintype B] [Nonempty B] [DecidableEq I] [DecidableEq A]
    (e : I → A) (hinj : Function.Injective e) (f : (I → B) → ℝ) (C : ℝ)
    (hmean : (∑ τ : I → B, f τ) ≤ Fintype.card (I → B) * C) :
    (∑ ω : A → B, f (fun i => ω (e i))) ≤ Fintype.card (A → B) * C := by
  have hcard : (0 : ℝ) < Fintype.card (I → B) := by exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg (Fintype.card (A → B)) : (0 : ℝ) ≤ _)
  rw [← sum_scaled e hinj f] at h
  apply (mul_le_mul_iff_right₀ hcard).mp
  nlinarith

theorem reflect_bound [Fintype I] [Fintype A] [Fintype B] [Nonempty B] [DecidableEq I] [DecidableEq A]
    (e : I → A) (hinj : Function.Injective e) (f : (I → B) → ℝ) (C : ℝ)
    (hmean : (∑ ω : A → B, f (fun i => ω (e i))) ≤ Fintype.card (A → B) * C) :
    (∑ τ : I → B, f τ) ≤ Fintype.card (I → B) * C := by
  classical
  have hcard : (0 : ℝ) < Fintype.card ({a // a ∉ Set.range e} → B) := by exact_mod_cast Fintype.card_pos
  have hc := Fintype.card_congr (split (B := B) e hinj)
  have hr : (Fintype.card (A → B) : ℝ) =
      Fintype.card (I → B) * Fintype.card ({a // a ∉ Set.range e} → B) := by
    exact_mod_cast hc.trans (Fintype.card_prod _ _)
  rw [sum_fibers e hinj f, hr] at hmean
  apply (mul_le_mul_iff_right₀ hcard).mp
  nlinarith
end Paper.UniformProjection
