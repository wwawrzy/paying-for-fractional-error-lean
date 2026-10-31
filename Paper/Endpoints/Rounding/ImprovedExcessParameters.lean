import Paper.Endpoints.Rounding.NoncriticalParameters

/-! The caller chooses any admissible gain, including zero. These are the
exact threshold and coefficient comparisons in `fv:imp:lemma`. -/
namespace Paper.ImprovedExcess

noncomputable def threshold (a θ μ : ℝ) : ℝ :=
  max ((μ + 1) / (2 * a + 1)) ((1 - θ) / ((a + 1) * (μ + 1 - θ)))

noncomputable def additive (a θ μ η : ℝ) : ℝ :=
  2 * η * threshold a θ μ * (1 + μ / (1 - θ))

theorem threshold_bounds {a θ μ : ℝ} (ha : 1 ≤ a) (hθ1 : θ < 1) (hμ : 0 ≤ μ)
    (hadm : (μ + 1) * (μ + 1 - θ) ≤ (2 * a + 1) * (1 - θ) / a) :
    0 < threshold a θ μ ∧ (μ + 1) / (2 * a + 1) ≤ threshold a θ μ ∧
      (1 - θ) / ((a + 1) * (μ + 1 - θ)) ≤ threshold a θ μ ∧
      threshold a θ μ ≤ (1 - θ) / (a * (μ + 1 - θ)) := by
  have ha0 : 0 < a := by linarith
  have hb : 0 < 2 * a + 1 := by linarith
  have hg : 0 < μ + 1 - θ := by linarith
  have hprod := (le_div_iff₀ ha0).mp hadm
  have hfirst : (μ + 1) / (2 * a + 1) ≤ (1 - θ) / (a * (μ + 1 - θ)) := by
    apply (div_le_div_iff₀ hb (mul_pos ha0 hg)).mpr
    nlinarith only [hprod]
  have hsecond : (1 - θ) / ((a + 1) * (μ + 1 - θ)) ≤
      (1 - θ) / (a * (μ + 1 - θ)) :=
    div_le_div_of_nonneg_left (by linarith) (mul_pos ha0 hg)
      (by nlinarith : a * (μ + 1 - θ) ≤ (a + 1) * (μ + 1 - θ))
  exact ⟨lt_of_lt_of_le (div_pos (by linarith) hb) (le_max_left _ _),
    le_max_left _ _, le_max_right _ _, max_le hfirst hsecond⟩

theorem coefficients {a θ μ : ℝ} (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hμ : 0 ≤ μ) (hμθ : μ ≤ θ)
    (hadm : (μ + 1) * (μ + 1 - θ) ≤ (2 * a + 1) * (1 - θ) / a) :
    0 < threshold a θ μ ∧ μ ≤ (2 * a + 1) * threshold a θ μ - 1 ∧
      μ * threshold a θ μ * a / (1 - θ) ≤ 1 - a * threshold a θ μ ∧
      -(μ * threshold a θ μ * (a + 1) / (1 - θ)) ≤ (a + 1) * threshold a θ μ - 1 ∧
      μ / θ ≤ 1 := by
  obtain ⟨ht, hl, hl₂, hu⟩ := threshold_bounds ha hθ1 hμ hadm
  have hg : 0 < μ + 1 - θ := by linarith
  have hlo := (div_le_iff₀ (show 0 < 2 * a + 1 by linarith)).mp hl
  have hlo₂ := (div_le_iff₀ (mul_pos (show 0 < a + 1 by linarith) hg)).mp hl₂
  have hup := (le_div_iff₀ (mul_pos (show 0 < a by linarith) hg)).mp hu
  refine ⟨ht, by nlinarith only [hlo], ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (by linarith : 0 < 1 - θ)).mpr
    nlinarith only [hup]
  · rw [← neg_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - θ)).mpr
    nlinarith only [hlo₂]
  · exact (div_le_iff₀ hθ).mpr (by linarith)

end Paper.ImprovedExcess
#print axioms Paper.ImprovedExcess.coefficients
