import Paper.TotalDomination.NonintegerParameters
import Paper.TotalDomination.MaximumGain

/-! Connect the exact maximum gain to the noninteger rounding parameters.
The density fixes the floor and gap, while the caller retains its chosen gain. -/

namespace Paper.TotalDomination.Noninteger

/-- The actual fractional gap of twice the rational density. -/
noncomputable def gap (a : ℚ) : ℝ :=
  2 * (a : ℝ) - (Nat.floor (2 * (a : ℝ)) : ℝ)

theorem gap_bounds (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℝ) = 2 * (a : ℝ)) :
    0 < gap a ∧ gap a < 1 := by
  obtain ⟨p, _, _, htheta, _⟩ :=
    parameters_exist (a : ℝ) (by exact_mod_cast ha) hnoninteger
  simpa only [htheta, gap] using And.intro p.theta_pos p.theta_lt_one

/-- Construct parameters with the prescribed rational gain, rather than
choosing a possibly different gain from the density alone. -/
theorem parameters_of_gain (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℝ) = 2 * (a : ℝ))
    (mu : ℚ) (hmu : 0 < mu) (hmax : (mu : ℝ) ≤ muMax (gap a)) :
    ∃ p : Parameters, p.a = (a : ℝ) ∧ p.mu = (mu : ℝ) ∧
      p.k = Nat.floor (2 * (a : ℝ)) ∧ p.theta = gap a := by
  obtain ⟨hzero, hone⟩ := gap_bounds a ha hnoninteger
  have hmuR : (0 : ℝ) < mu := by exact_mod_cast hmu
  obtain ⟨hle, hadmissible⟩ :=
    (admissible_iff_le_muMax (gap a) mu hzero hone hmuR).mpr hmax
  refine ⟨{
    a := (a : ℝ)
    a_ge_one := by exact_mod_cast ha
    k := Nat.floor (2 * (a : ℝ))
    theta := gap a
    decomposition := by unfold gap; ring
    theta_pos := hzero
    theta_lt_one := hone
    mu := (mu : ℝ)
    mu_pos := hmuR
    mu_le_theta := hle
    admissible := hadmissible
  }, rfl, rfl, rfl, rfl⟩

/-- Rational nonintegrality also excludes an integer equality after real casting. -/
theorem noninteger_real_of_rat (a : ℚ)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ¬ ∃ z : ℤ, (z : ℝ) = 2 * (a : ℝ) := by
  rintro ⟨z, hz⟩
  apply hnoninteger
  refine ⟨z, ?_⟩
  exact_mod_cast hz

/-- The same chosen-gain constructor with entirely rational input hypotheses. -/
theorem parameters_of_gain_rat (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (mu : ℚ) (hmu : 0 < mu) (hmax : (mu : ℝ) ≤ muMax (gap a)) :
    ∃ p : Parameters, p.a = (a : ℝ) ∧ p.mu = (mu : ℝ) ∧
      p.k = Nat.floor (2 * (a : ℝ)) ∧ p.theta = gap a :=
  parameters_of_gain a ha (noninteger_real_of_rat a hnoninteger) mu hmu hmax

end Paper.TotalDomination.Noninteger

#print axioms Paper.TotalDomination.Noninteger.gap_bounds
#print axioms Paper.TotalDomination.Noninteger.parameters_of_gain
#print axioms Paper.TotalDomination.Noninteger.noninteger_real_of_rat
#print axioms Paper.TotalDomination.Noninteger.parameters_of_gain_rat
