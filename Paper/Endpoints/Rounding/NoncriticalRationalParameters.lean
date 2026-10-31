import Paper.Endpoints.Rounding.NoncriticalParameters

/-! Computable rational parameter choices and a natural numerator/denominator
representation for the real threshold used in the mathematical proof. -/
namespace Paper.NoncriticalRationalParameters

def gain (θ : ℚ) : ℚ := min (θ / 2) ((1 - θ) / 4)
def threshold (a θ : ℚ) : ℚ :=
  max ((1 + gain θ) / (2 * a + 1)) ((1 - θ) / ((a + 1) * (1 + gain θ - θ)))

theorem gain_cast (θ : ℚ) : (gain θ : ℝ) = NoncriticalParameters.gain (θ : ℝ) := by
  simp only [gain, NoncriticalParameters.gain, Rat.cast_min, Rat.cast_div, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat]

theorem threshold_cast (a θ : ℚ) :
    (threshold a θ : ℝ) = NoncriticalParameters.threshold (a : ℝ) (θ : ℝ) := by
  simp only [threshold, NoncriticalParameters.threshold, Rat.cast_max, Rat.cast_div,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat, gain_cast]

theorem natural_ratio (σ : ℚ) (hσ : 0 ≤ σ) :
    ∃ m h : ℕ, 0 < m ∧ (h : ℝ) / m = (σ : ℝ) := by
  refine ⟨σ.den, σ.num.toNat, σ.den_pos, ?_⟩
  have hn : 0 ≤ σ.num := Rat.num_nonneg.mpr hσ
  have he : ((σ.num.toNat : ℕ) : ℝ) = (σ.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  rw [he]
  exact (Rat.cast_def σ).symm

end Paper.NoncriticalRationalParameters
