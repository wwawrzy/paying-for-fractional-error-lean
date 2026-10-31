import Paper.TotalDomination.Noninteger

/-! Graph-independent scalar choices for `fv:total:noncrit`. A rational
`mu` below both `theta` and `(1-theta)/4` satisfies the paper's
quadratic condition. No formula involving a square root is needed. -/

namespace Paper.TotalDomination.Noninteger

/-- A positive rational accuracy gain exists for every noninteger gap. -/
theorem exists_rational_mu (theta : ℝ) (hzero : 0 < theta) (hone : theta < 1) :
    ∃ mu : ℚ, 0 < mu ∧ (mu : ℝ) ≤ theta ∧
      (1 + (mu : ℝ)) * (1 + (mu : ℝ) - theta) ≤ 2 * (1 - theta) := by
  have hbound : (0 : ℝ) < min theta ((1 - theta) / 4) :=
    lt_min hzero (by linarith)
  obtain ⟨mu, hmu, hsmall⟩ := exists_rat_btwn hbound
  have htheta : (mu : ℝ) ≤ theta := hsmall.le.trans (min_le_left _ _)
  have hfour : (mu : ℝ) ≤ (1 - theta) / 4 := hsmall.le.trans (min_le_right _ _)
  have hquarter : (mu : ℝ) ≤ 1 / 4 := by linarith
  have hquadratic := mul_le_mul_of_nonneg_left hquarter hmu.le
  have hproduct : 0 ≤ theta * (mu : ℝ) := mul_nonneg hzero.le hmu.le
  refine ⟨mu, ?_, htheta, ?_⟩
  · exact_mod_cast hmu
  · nlinarith only [hquadratic, hfour, hproduct, hone]

/-- The complete scalar package can be chosen before a vertex type, graph,
identifier assignment, or fractional input is supplied. -/
theorem parameters_of_decomposition (a : ℝ) (ha : 1 ≤ a) (k : ℕ) (theta : ℝ)
    (hdecomposition : 2 * a = k + theta) (hzero : 0 < theta) (hone : theta < 1) :
    ∃ p : Parameters, p.a = a ∧ p.k = k ∧ p.theta = theta ∧
      ∃ mu : ℚ, 0 < mu ∧ p.mu = (mu : ℝ) := by
  obtain ⟨mu, hmu, htheta, hadmissible⟩ := exists_rational_mu theta hzero hone
  refine ⟨{
    a := a
    a_ge_one := ha
    k := k
    theta := theta
    decomposition := hdecomposition
    theta_pos := hzero
    theta_lt_one := hone
    mu := (mu : ℝ)
    mu_pos := by exact_mod_cast hmu
    mu_le_theta := htheta
    admissible := hadmissible
  }, rfl, rfl, rfl, mu, hmu, rfl⟩

/-- Arbitrary real density with noninteger `2a` supplies its actual natural
floor, a gap in `(0,1)`, and a positive rational gain. -/
theorem parameters_exist (a : ℝ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℝ) = 2 * a) :
    ∃ p : Parameters, p.a = a ∧ p.k = ⌊2 * a⌋₊ ∧
      p.theta = 2 * a - (⌊2 * a⌋₊ : ℝ) ∧
      ∃ mu : ℚ, 0 < mu ∧ p.mu = (mu : ℝ) := by
  let k : ℕ := ⌊2 * a⌋₊
  have hk_le : (k : ℝ) ≤ 2 * a := Nat.floor_le (by linarith)
  have hk_ne : (k : ℝ) ≠ 2 * a := by
    intro heq
    exact hnoninteger ⟨(k : ℤ), by exact_mod_cast heq⟩
  have hk_lower : (k : ℝ) < 2 * a := lt_of_le_of_ne hk_le hk_ne
  have hk_upper : 2 * a < (k : ℝ) + 1 := Nat.lt_floor_add_one (2 * a)
  have hdecomposition : 2 * a = (k : ℝ) + (2 * a - (k : ℝ)) := by ring
  exact parameters_of_decomposition a ha k (2 * a - (k : ℝ)) hdecomposition
    (by linarith) (by linarith)

end Paper.TotalDomination.Noninteger

#print axioms Paper.TotalDomination.Noninteger.exists_rational_mu
#print axioms Paper.TotalDomination.Noninteger.parameters_of_decomposition
#print axioms Paper.TotalDomination.Noninteger.parameters_exist
