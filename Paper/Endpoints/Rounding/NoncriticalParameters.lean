import Mathlib

/-! Parameter-only inequalities paying for fractional solver error in the
noninteger-density branch. No graph or solver enters this choice. -/
namespace Paper.NoncriticalParameters

noncomputable def gain (θ : ℝ) : ℝ := min (θ / 2) ((1 - θ) / 4)
noncomputable def threshold (a θ : ℝ) : ℝ :=
  max ((1 + gain θ) / (2 * a + 1))
    ((1 - θ) / ((a + 1) * (1 + gain θ - θ)))

theorem gain_bounds {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 < gain θ ∧ gain θ ≤ θ ∧ gain θ ≤ (1 - θ) / 4 ∧ gain θ ≤ 1 / 4 := by
  have h1 := min_le_left (θ / 2) ((1 - θ) / 4)
  have h2 := min_le_right (θ / 2) ((1 - θ) / 4)
  have hp : 0 < min (θ / 2) ((1 - θ) / 4) := lt_min (by linarith) (by linarith)
  dsimp only [gain]
  exact ⟨hp, by linarith, h2, by linarith⟩

theorem feasible {a θ : ℝ} (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1) :
    a * (1 + gain θ) * (1 + gain θ - θ) ≤ (2 * a + 1) * (1 - θ) := by
  obtain ⟨hp, hμθ, hμgap, hμquarter⟩ := gain_bounds hθ hθ1
  have hleft : 1 + gain θ ≤ (5 : ℝ) / 4 := by linarith
  have hright : 1 + gain θ - θ ≤ (5 : ℝ) / 4 * (1 - θ) := by linarith
  have hb := mul_le_mul hleft hright (by linarith : 0 ≤ 1 + gain θ - θ) (by norm_num : (0 : ℝ) ≤ 5 / 4)
  have hprod : (1 + gain θ) * (1 + gain θ - θ) ≤ (25 : ℝ) / 16 * (1 - θ) := by nlinarith only [hb]
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ a by linarith)
  have ht := mul_le_mul_of_nonneg_right (show (25 : ℝ) / 16 * a ≤ 2 * a + 1 by linarith)
    (show 0 ≤ 1 - θ by linarith)
  nlinarith only [hm, ht]

theorem threshold_bounds {a θ : ℝ} (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 ≤ threshold a θ ∧ (1 + gain θ) / (2 * a + 1) ≤ threshold a θ ∧
      (1 - θ) / ((a + 1) * (1 + gain θ - θ)) ≤ threshold a θ ∧
      threshold a θ ≤ (1 - θ) / (a * (1 + gain θ - θ)) := by
  obtain ⟨hp, _, _, _⟩ := gain_bounds hθ hθ1
  have ha0 : 0 < a := by linarith
  have hb : 0 < 2 * a + 1 := by linarith
  have hg : 0 < 1 + gain θ - θ := by linarith
  have hfirst : (1 + gain θ) / (2 * a + 1) ≤ (1 - θ) / (a * (1 + gain θ - θ)) := by
    apply (div_le_div_iff₀ hb (mul_pos ha0 hg)).mpr
    have h := feasible ha hθ hθ1
    nlinarith only [h]
  have hsecond : (1 - θ) / ((a + 1) * (1 + gain θ - θ)) ≤
      (1 - θ) / (a * (1 + gain θ - θ)) :=
    div_le_div_of_nonneg_left (by linarith) (mul_pos ha0 hg)
      (by nlinarith : a * (1 + gain θ - θ) ≤ (a + 1) * (1 + gain θ - θ))
  exact ⟨(by unfold threshold; exact (div_nonneg (by linarith) (le_of_lt hb)).trans (le_max_left _ _)),
    le_max_left _ _, le_max_right _ _, max_le hfirst hsecond⟩

theorem coefficients {a θ : ℝ} (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 < gain θ ∧ gain θ < 2 * a + 1 ∧ 0 ≤ threshold a θ ∧
      gain θ ≤ (2 * a + 1) * threshold a θ - 1 ∧
      gain θ * threshold a θ * a / (1 - θ) ≤ 1 - a * threshold a θ ∧
      -(gain θ * threshold a θ * (a + 1) / (1 - θ)) ≤ (a + 1) * threshold a θ - 1 ∧
      gain θ / θ ≤ 1 := by
  obtain ⟨hp, hμθ, _, hμquarter⟩ := gain_bounds hθ hθ1
  obtain ⟨hσ, hl, hl₂, hu⟩ := threshold_bounds ha hθ hθ1
  have hg : 0 < 1 + gain θ - θ := by linarith
  have hlo := (div_le_iff₀ (show 0 < 2 * a + 1 by linarith)).mp hl
  have hlo₂ := (div_le_iff₀ (mul_pos (show 0 < a + 1 by linarith) hg)).mp hl₂
  have hup := (le_div_iff₀ (mul_pos (show 0 < a by linarith) hg)).mp hu
  refine ⟨hp, by linarith, hσ, by nlinarith only [hlo], ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (by linarith : 0 < 1 - θ)).mpr
    nlinarith only [hup]
  · rw [← neg_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - θ)).mpr
    nlinarith only [hlo₂]
  · exact (div_le_iff₀ hθ).mpr (by linarith)

end Paper.NoncriticalParameters
