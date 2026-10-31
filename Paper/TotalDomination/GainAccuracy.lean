import Paper.TotalDomination.MaximumGain

/-! Public scalar gain and accuracy choices for `fv:total:noncrit-cor`.
Both rational parameters are chosen before any graph or solver input. -/

namespace Paper.TotalDomination.Noninteger

/-- Every gain below the exact maximum leaves a positive coefficient. -/
theorem sub_gain_pos (d theta mu : ℝ) (hd : 2 ≤ d) (hone : theta < 1)
    (hmu : mu ≤ muMax theta) : 0 < d - mu := by
  have htheta := hmu.trans (muMax_le_theta theta)
  linarith

/-- A target strictly below the maximum admits positive rational gain and
accuracy parameters with the exact target coefficient after solver loss. -/
theorem gain_accuracy_below_max (d theta mu0 : ℝ) (hd : 2 ≤ d)
    (hzero : 0 < theta) (hone : theta < 1) (hmu0 : 0 < mu0)
    (hbelow : mu0 < muMax theta) :
    ∃ mu delta : ℚ, 0 < mu ∧ 0 < delta ∧ mu0 < (mu : ℝ) ∧
      (mu : ℝ) ≤ muMax theta ∧ (mu : ℝ) ≤ theta ∧
      (1 + (mu : ℝ)) * (1 + (mu : ℝ) - theta) ≤ 2 * (1 - theta) ∧
      0 < d - (mu : ℝ) ∧
      (d - (mu : ℝ)) * (1 + (delta : ℝ)) ≤ d - mu0 := by
  obtain ⟨mu, hmu, hlo, hhi⟩ := exists_rational_mu_above theta mu0 hmu0 hbelow
  have hmuR : (0 : ℝ) < mu := by exact_mod_cast hmu
  have hadmissible := (admissible_iff_le_muMax theta mu hzero hone hmuR).mpr hhi
  have hden := sub_gain_pos d theta mu hd hone hhi
  have hratio : 0 < ((mu : ℝ) - mu0) / (d - (mu : ℝ)) :=
    div_pos (sub_pos.mpr hlo) hden
  obtain ⟨delta, hdelta, hsmall⟩ := exists_rat_btwn hratio
  have hproduct := (lt_div_iff₀ hden).mp hsmall
  refine ⟨mu, delta, hmu, ?_, hlo, hhi, hadmissible.1, hadmissible.2, hden, ?_⟩
  · exact_mod_cast hdelta
  · nlinarith only [hproduct]

/-- Rational parameters approach the exact maximum coefficient within any
positive error, reserving at most half the error for solver accuracy. -/
theorem gain_accuracy_near_max (d theta epsilon : ℝ) (hd : 2 ≤ d)
    (hzero : 0 < theta) (hone : theta < 1) (hepsilon : 0 < epsilon) :
    ∃ mu delta : ℚ, 0 < mu ∧ 0 < delta ∧ (mu : ℝ) ≤ muMax theta ∧
      (mu : ℝ) ≤ theta ∧
      (1 + (mu : ℝ)) * (1 + (mu : ℝ) - theta) ≤ 2 * (1 - theta) ∧
      muMax theta - epsilon / 2 ≤ (mu : ℝ) ∧
      (delta : ℝ) ≤ epsilon / (2 * d) ∧ 0 < d - (mu : ℝ) ∧
      (d - (mu : ℝ)) * (1 + (delta : ℝ)) ≤ d - muMax theta + epsilon := by
  obtain ⟨mu, hmu, hhi, hnear⟩ := exists_rational_mu_near theta epsilon hzero hone hepsilon
  have hmuR : (0 : ℝ) < mu := by exact_mod_cast hmu
  have hadmissible := (admissible_iff_le_muMax theta mu hzero hone hmuR).mpr hhi
  have hden := sub_gain_pos d theta mu hd hone hhi
  have hdpos : 0 < 2 * d := by linarith
  obtain ⟨delta, hdelta, hsmall⟩ := exists_rat_btwn (div_pos hepsilon hdpos)
  have hproduct := (lt_div_iff₀ hdpos).mp hsmall
  have hnonneg := mul_nonneg hmuR.le hdelta.le
  refine ⟨mu, delta, hmu, ?_, hhi, hadmissible.1, hadmissible.2,
    hnear, hsmall.le, hden, ?_⟩
  · exact_mod_cast hdelta
  · nlinarith only [hproduct, hnonneg, hnear]

end Paper.TotalDomination.Noninteger

#print axioms Paper.TotalDomination.Noninteger.sub_gain_pos
#print axioms Paper.TotalDomination.Noninteger.gain_accuracy_below_max
#print axioms Paper.TotalDomination.Noninteger.gain_accuracy_near_max
