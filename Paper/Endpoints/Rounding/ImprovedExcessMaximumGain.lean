import Mathlib

/-! The exact maximum ordinary-domination gain in `fv:imp:lemma` and
`fv:imp:girth`. The square-root formula is retained, and the admissibility
equivalence includes zero gain. No graph or rounding conclusion is assumed. -/
namespace Paper.ImprovedExcess

/-- The paper's exact maximum, including its endpoint. -/
noncomputable def muMax (a theta : ℝ) : ℝ :=
  min theta ((theta - 2 + Real.sqrt ((2 - theta) ^ 2 +
    4 * (1 - theta) * (1 + 1 / a))) / 2)

private theorem root_properties (a theta : ℝ) (ha : 1 ≤ a) (hone : theta < 1) :
    let r := (theta - 2 + Real.sqrt ((2 - theta) ^ 2 +
      4 * (1 - theta) * (1 + 1 / a))) / 2
    0 < r ∧ r ^ 2 + (2 - theta) * r - (1 - theta) * (1 + 1 / a) = 0 := by
  have ha0 : 0 < a := by linarith
  have hc : 0 < (1 - theta) * (1 + 1 / a) :=
    mul_pos (by linarith) (by positivity)
  have hdisc : 0 ≤ (2 - theta) ^ 2 + 4 * (1 - theta) * (1 + 1 / a) := by
    nlinarith only [sq_nonneg (2 - theta), hc]
  have hs := Real.sqrt_nonneg ((2 - theta) ^ 2 + 4 * (1 - theta) * (1 + 1 / a))
  have hsq := Real.sq_sqrt hdisc
  have hlarge : 2 - theta <
      Real.sqrt ((2 - theta) ^ 2 + 4 * (1 - theta) * (1 + 1 / a)) := by
    by_contra h
    have hle := le_of_not_gt h
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 2 - theta + Real.sqrt
        ((2 - theta) ^ 2 + 4 * (1 - theta) * (1 + 1 / a)) by linarith)
    nlinarith only [hp, hsq, hc]
  dsimp only
  constructor
  · linarith only [hlarge]
  · nlinarith only [hsq]

theorem muMax_pos (a theta : ℝ) (ha : 1 ≤ a) (hzero : 0 < theta) (hone : theta < 1) :
    0 < muMax a theta :=
  lt_min hzero (root_properties a theta ha hone).1

theorem muMax_le_theta (a theta : ℝ) : muMax a theta ≤ theta :=
  min_le_left _ _

/-- Exactly the paper's admissibility condition for every nonnegative
gain, including mu = 0 and equality at the maximum. -/
theorem admissible_iff_le_muMax (a theta mu : ℝ) (ha : 1 ≤ a)
    (hzero : 0 < theta) (hone : theta < 1) (hmu : 0 ≤ mu) :
    (mu ≤ theta ∧ (mu + 1) * (mu + 1 - theta) ≤
      (2 * a + 1) * (1 - theta) / a) ↔ mu ≤ muMax a theta := by
  have ha0 : 0 < a := by linarith
  have hconstant : (2 * a + 1) * (1 - theta) / a =
      (1 - theta) + (1 - theta) * (1 + 1 / a) := by
    field_simp [ne_of_gt ha0]
    ring
  have hquad_iff : (mu + 1) * (mu + 1 - theta) ≤
      (2 * a + 1) * (1 - theta) / a ↔
      mu ^ 2 + (2 - theta) * mu - (1 - theta) * (1 + 1 / a) ≤ 0 := by
    rw [hconstant]
    constructor <;> intro h <;> nlinarith only [h]
  let r := (theta - 2 + Real.sqrt ((2 - theta) ^ 2 +
    4 * (1 - theta) * (1 + 1 / a))) / 2
  obtain ⟨hr, heq⟩ := root_properties a theta ha hone
  change 0 < r at hr
  change r ^ 2 + (2 - theta) * r - (1 - theta) * (1 + 1 / a) = 0 at heq
  change (mu ≤ theta ∧ _) ↔ mu ≤ min theta r
  constructor
  · rintro ⟨htheta, hquad⟩
    refine le_min htheta ?_
    have hq := hquad_iff.mp hquad
    by_contra h
    have hlt : r < mu := lt_of_not_ge h
    have hp := mul_pos (sub_pos.mpr hlt)
      (show 0 < mu + r + 2 - theta by linarith)
    nlinarith only [hp, heq, hq]
  · intro h
    have htheta := h.trans (min_le_left _ _)
    have hrmu := h.trans (min_le_right _ _)
    have hp := mul_nonneg (sub_nonneg.mpr hrmu)
      (show 0 ≤ r + mu + 2 - theta by linarith)
    exact ⟨htheta, hquad_iff.mpr (by nlinarith only [hp, heq])⟩

/-- A positive rational gain lies strictly between any nonnegative target
below the maximum and the exact maximum. All choices are graph-independent. -/
theorem exists_rational_mu_above (a theta mu0 : ℝ) (hmu0 : 0 ≤ mu0)
    (hbelow : mu0 < muMax a theta) :
    ∃ mu : ℚ, 0 < mu ∧ mu0 < (mu : ℝ) ∧ (mu : ℝ) < muMax a theta := by
  obtain ⟨mu, hlo, hhi⟩ := exists_rat_btwn hbelow
  refine ⟨mu, ?_, hlo, hhi⟩
  exact_mod_cast (lt_of_le_of_lt hmu0 hlo)

end Paper.ImprovedExcess

#print axioms Paper.ImprovedExcess.muMax_pos
#print axioms Paper.ImprovedExcess.muMax_le_theta
#print axioms Paper.ImprovedExcess.admissible_iff_le_muMax
#print axioms Paper.ImprovedExcess.exists_rational_mu_above
