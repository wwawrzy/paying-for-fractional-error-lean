import Mathlib

/-! The exact maximum gain and rational choices in `fv:total:noncrit-cor`.
These scalar statements retain the paper's square-root formula. -/

namespace Paper.TotalDomination.Noninteger

/-- The paper's exact maximum admissible gain. -/
noncomputable def muMax (theta : ℝ) : ℝ :=
  min theta ((theta - 2 + Real.sqrt (theta ^ 2 - 8 * theta + 8)) / 2)

private theorem root_properties (theta : ℝ) (hzero : 0 < theta) (hone : theta < 1) :
    let r := (theta - 2 + Real.sqrt (theta ^ 2 - 8 * theta + 8)) / 2
    0 < r ∧ r ^ 2 + (2 - theta) * r + theta - 1 = 0 := by
  have hdisc : 0 ≤ theta ^ 2 - 8 * theta + 8 := by nlinarith [sq_nonneg theta]
  have hs := Real.sqrt_nonneg (theta ^ 2 - 8 * theta + 8)
  have hsq := Real.sq_sqrt hdisc
  have hlarge : 2 - theta < Real.sqrt (theta ^ 2 - 8 * theta + 8) := by
    by_contra h
    have hle := le_of_not_gt h
    have hp := mul_nonneg
      (sub_nonneg.mpr hle) (show 0 ≤ 2 - theta +
        Real.sqrt (theta ^ 2 - 8 * theta + 8) by linarith)
    nlinarith
  dsimp only
  constructor
  · linarith
  · nlinarith

theorem muMax_pos (theta : ℝ) (hzero : 0 < theta) (hone : theta < 1) :
    0 < muMax theta :=
  lt_min hzero (root_properties theta hzero hone).1

theorem muMax_le_theta (theta : ℝ) : muMax theta ≤ theta :=
  min_le_left _ _

/-- The positive gains allowed by the quadratic condition are exactly those
below the displayed maximum, including its endpoint. -/
theorem admissible_iff_le_muMax (theta mu : ℝ) (hzero : 0 < theta)
    (hone : theta < 1) (hmu : 0 < mu) :
    (mu ≤ theta ∧ (1 + mu) * (1 + mu - theta) ≤ 2 * (1 - theta)) ↔
      mu ≤ muMax theta := by
  let r := (theta - 2 + Real.sqrt (theta ^ 2 - 8 * theta + 8)) / 2
  obtain ⟨hr, heq⟩ := root_properties theta hzero hone
  change 0 < r at hr
  change r ^ 2 + (2 - theta) * r + theta - 1 = 0 at heq
  change (mu ≤ theta ∧ _) ↔ mu ≤ min theta r
  constructor
  · rintro ⟨htheta, hquad⟩
    refine le_min htheta ?_
    by_contra h
    have hlt : r < mu := lt_of_not_ge h
    have hp := mul_pos (sub_pos.mpr hlt)
      (show 0 < mu + r + 2 - theta by linarith)
    nlinarith
  · intro h
    have htheta := h.trans (min_le_left _ _)
    have hrmu := h.trans (min_le_right _ _)
    have hp := mul_nonneg (sub_nonneg.mpr hrmu)
      (show 0 ≤ r + mu + 2 - theta by linarith)
    exact ⟨htheta, by nlinarith⟩

/-- A rational gain strictly improves any positive target below the maximum. -/
theorem exists_rational_mu_above (theta mu0 : ℝ)
    (hmu0 : 0 < mu0) (hbelow : mu0 < muMax theta) :
    ∃ mu : ℚ, 0 < mu ∧ mu0 < (mu : ℝ) ∧ (mu : ℝ) ≤ muMax theta := by
  obtain ⟨mu, hlo, hhi⟩ := exists_rat_btwn hbelow
  refine ⟨mu, ?_, hlo, hhi.le⟩
  exact_mod_cast (lt_trans hmu0 hlo)

/-- A positive rational gain approaches the exact maximum within epsilon/2. -/
theorem exists_rational_mu_near (theta epsilon : ℝ) (hzero : 0 < theta)
    (hone : theta < 1) (hepsilon : 0 < epsilon) :
    ∃ mu : ℚ, 0 < mu ∧ (mu : ℝ) ≤ muMax theta ∧
      muMax theta - epsilon / 2 ≤ (mu : ℝ) := by
  have hmax := muMax_pos theta hzero hone
  have hgap : max 0 (muMax theta - epsilon / 2) < muMax theta :=
    max_lt hmax (by linarith)
  obtain ⟨mu, hlo, hhi⟩ := exists_rat_btwn hgap
  refine ⟨mu, ?_, hhi.le, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hlo)
  · exact (le_max_right _ _).trans hlo.le

end Paper.TotalDomination.Noninteger

#print axioms Paper.TotalDomination.Noninteger.muMax_pos
#print axioms Paper.TotalDomination.Noninteger.admissible_iff_le_muMax
#print axioms Paper.TotalDomination.Noninteger.exists_rational_mu_above
#print axioms Paper.TotalDomination.Noninteger.exists_rational_mu_near
