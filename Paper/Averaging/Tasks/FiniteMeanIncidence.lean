import Paper.Averaging.Tasks.FiniteIncidenceAverage
import Paper.Preliminaries.FiniteCoordinateCount

namespace Paper.FiniteMeanIncidence
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- A varying per-outcome upper bound is averaged exactly, rather than
replaced by its worst case. -/
theorem bound {E Ω : Type} [Fintype E] [Fintype Ω] [Nonempty Ω]
    (P : E → Ω → Prop) (C : ℕ) (b : Ω → ℝ)
    (hlow : ∀ e, Fintype.card Ω ≤ C * (Finset.univ.filter (P e)).card)
    (hhigh : ∀ ω, ((Finset.univ.filter (fun e => P e ω)).card : ℝ) ≤ b ω) :
    (Fintype.card E : ℝ) * Fintype.card Ω ≤ C * ∑ ω, b ω := by
  classical
  have hl : (Fintype.card E : ℝ) * Fintype.card Ω ≤
      C * ∑ e, ((Finset.univ.filter (P e)).card : ℝ) := by
    calc
      _ = ∑ _e : E, (Fintype.card Ω : ℝ) := by simp [mul_comm]
      _ ≤ ∑ e : E, (C : ℝ)*(Finset.univ.filter (P e)).card :=
        Finset.sum_le_sum (fun e _ => by exact_mod_cast hlow e)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have he := FiniteIncidenceAverage.incidence (Finset.univ : Finset E) Finset.univ P
  have he' : (∑ e, ((Finset.univ.filter (P e)).card : ℝ)) =
      ∑ ω, ((Finset.univ.filter (fun e => P e ω)).card : ℝ) := by exact_mod_cast he
  rw [he'] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ => hhigh ω)) (Nat.cast_nonneg _))

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Bits := V → Fin 2
abbrev Choices (L : ℕ) := V → Fin L
abbrev Outcomes (L : ℕ) := Bits (V := V) × Choices (V := V) L

theorem bit_fiber (L : ℕ) (v : V) :
    2 * (Finset.univ.filter (fun ω : Outcomes (V := V) L => ω.1 v = 0)).card =
      Fintype.card (Outcomes (V := V) L) := by
  classical
  have he : (Finset.univ.filter (fun ω : Outcomes (V := V) L => ω.1 v = 0)) =
      (Finset.univ.filter (fun β : Bits (V := V) => β v = 0)) ×ˢ (Finset.univ : Finset (Choices (V := V) L)) := by
    ext ω
    simp
  rw [he, Finset.card_product, Finset.card_univ, ← mul_assoc, FiniteCoordinateCount.one]
  exact (Fintype.card_prod _ _).symm

theorem mean_selected (L : ℕ) (I : Finset V) :
    2 * (∑ ω : Outcomes (V := V) L, (I.filter (fun d => ω.1 d = 0)).card) =
      I.card * Fintype.card (Outcomes (V := V) L) := by
  classical
  have he := FiniteIncidenceAverage.incidence I
    (Finset.univ : Finset (Outcomes (V := V) L)) (fun d ω => ω.1 d = 0)
  calc
    _ = 2*(∑ d ∈ I, (Finset.univ.filter (fun ω : Outcomes (V := V) L => ω.1 d = 0)).card) := by
      congr 1
      convert he.symm using 1 <;>
        apply Finset.sum_congr rfl <;> intro x hx <;> congr 1 <;> ext y <;> simp
    _ = ∑ d ∈ I, 2*(Finset.univ.filter (fun ω : Outcomes (V := V) L => ω.1 d = 0)).card := Finset.mul_sum _ _ _
    _ = _ := by simp_rw [bit_fiber]; simp

end Paper.FiniteMeanIncidence
