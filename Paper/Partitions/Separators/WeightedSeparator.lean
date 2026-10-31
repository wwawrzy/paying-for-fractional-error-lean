import Paper.Preliminaries.HavenExclusion

/-! A weighted sublinear separator follows from the proved finite exchange
argument. We use a sufficient rounded constant instead of the sharp AST one. -/
namespace Paper.WeightedSeparator
attribute [local instance] Classical.propDecidable
open WeightedHaven DeletionComponents HeavyComponent
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def radius (h n : ℕ) : ℕ := h * (Nat.sqrt n + 1)

theorem radius_pos (h n : ℕ) (hh : 1 ≤ h) : 1 ≤ radius h n := by
  dsimp [radius]
  nlinarith

theorem radius_square (h n : ℕ) (hh : 1 ≤ h) : h * n ≤ radius h n * radius h n := by
  have hn := Nat.lt_succ_sqrt n
  have hmul := Nat.mul_le_mul_left h (Nat.le_of_lt hn)
  have hsq : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ h * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) := by
    simpa only [one_mul] using Nat.mul_le_mul_right ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) hh
  have hp := Nat.mul_le_mul_left h hsq
  calc
    _ ≤ h * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) := hmul
    _ ≤ h * (h * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1))) := hp
    _ = _ := by dsimp [radius]; ring

theorem balanced {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h : ℕ) (hh : 2 * a + 1 < h) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ X : Finset V, X.card ≤ h * radius h (Fintype.card V) ∧
      ∀ C : (deleted G X).ConnectedComponent, mass w (physical G X C) ≤ (∑ v, w v) / 2 := by
  have hp : (0 : ℝ) < h := by linarith
  have hnat : 0 < h := by exact_mod_cast hp
  have hn : 1 ≤ h := by omega
  exact HavenExclusion.balanced G hden ha h (radius h (Fintype.card V)) hh
    (radius_pos h _ hn) (radius_square h _ hn) w hw

theorem sqrt_bound {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h : ℕ) (hh : 2 * a + 1 < h) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ X : Finset V, (X.card : ℝ) ≤ 2 * (h : ℝ) ^ 2 * Real.sqrt (Fintype.card V) ∧
      ∀ C : (deleted G X).ConnectedComponent, mass w (physical G X C) ≤ (∑ v, w v) / 2 := by
  obtain ⟨X, hX, hbalanced⟩ := balanced G hden ha h hh w hw
  refine ⟨X, ?_, hbalanced⟩
  by_cases hn : Fintype.card V = 0
  · have hc := Finset.card_le_univ X
    have hz : X.card = 0 := by omega
    simp only [hz, hn, Nat.cast_zero, Real.sqrt_zero, mul_zero, le_refl]
  · have hnat : 1 ≤ Fintype.card V := by omega
    have hunit : (1 : ℝ) ≤ Real.sqrt (Fintype.card V) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hnat)
    have hsq : ((Nat.sqrt (Fintype.card V) : ℕ) : ℝ) ^ 2 ≤ Fintype.card V := by
      exact_mod_cast Nat.sqrt_le' (Fintype.card V)
    have hsqrt := Real.le_sqrt_of_sq_le hsq
    have hsize : (X.card : ℝ) ≤ (h : ℝ) * h * (Nat.sqrt (Fintype.card V) + 1) := by
      have hh' : X.card ≤ h * h * (Nat.sqrt (Fintype.card V) + 1) := by
        simpa only [radius, mul_assoc] using hX
      exact_mod_cast hh'
    calc
      _ ≤ (h : ℝ) * h * (Nat.sqrt (Fintype.card V) + 1) := hsize
      _ ≤ (h : ℝ) * h * (2 * Real.sqrt (Fintype.card V)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = _ := by ring
end Paper.WeightedSeparator
