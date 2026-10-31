import Paper.Solver.Density.CappedConvergence
import Paper.Solver.Density.CappedCounterState

/-! Public rational constants chosen solely from the paper density.
Every graph and identifier assignment is quantified after these choices. -/
namespace Paper.Density.CappedUniformParameters

def cap (a : ℚ) : ℚ := 1/(2*a+1)
def rho (m : ℕ) : ℚ := (m : ℚ)/((m : ℚ)+1)

theorem rho_cast (m : ℕ) : (rho m : ℝ) = CappedGrowth.rho m := by
  simp only [rho, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, CappedGrowth.rho]

theorem scale_cast (m : ℕ) : (CappedCounterState.scale m : ℝ) = CappedGrowth.factor m := by
  simp only [CappedCounterState.scale, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, CappedGrowth.factor]

theorem cap_cast (a : ℚ) : (cap a : ℝ) = 1/(2*(a : ℝ)+1) := by
  simp only [cap, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one]

theorem cap_pos (a : ℚ) (ha : 1 ≤ a) : 0 < cap a := by
  unfold cap
  apply one_div_pos.mpr
  linarith

/-- No graph, degree bound, order bound or execution horizon is used here. -/
theorem parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2*a) :
    ∃ p : NeighborhoodSlack.Parameters, ∃ m : ℕ, p.a = (a : ℝ) ∧ 0 < m ∧
      (cap a : ℝ) = CappedConvergence.cap p ∧
      2*p.a+1-NeighborhoodSlack.eta p ≤ (2*p.a+1)*(rho m : ℝ) := by
  let k : ℕ := ⌊2*a⌋₊
  have hk_le : (k : ℚ) ≤ 2*a := Nat.floor_le (by linarith)
  have hk_ne : (k : ℚ) ≠ 2*a := by
    intro h
    exact hnoninteger ⟨(k : ℤ), by exact_mod_cast h⟩
  have hk : (k : ℚ) < 2*a := lt_of_le_of_ne hk_le hk_ne
  have hk1 : 2*a < (k : ℚ)+1 := Nat.lt_floor_add_one (2*a)
  have hkR : (k : ℝ) < 2*(a : ℝ) := by exact_mod_cast hk
  have hk1R : 2*(a : ℝ) < (k : ℝ)+1 := by exact_mod_cast hk1
  let p : NeighborhoodSlack.Parameters := {
    a := (a : ℝ)
    a_ge_one := by exact_mod_cast ha
    k := k
    theta := 2*(a : ℝ)-(k : ℝ)
    decomposition := by ring
    theta_pos := by linarith
    theta_lt_one := by linarith }
  obtain ⟨m, hm, ht⟩ := CappedConvergence.parameters p
  refine ⟨p,m,rfl,hm,?_,?_⟩
  · exact cap_cast a
  · simpa only [rho_cast] using ht

end Paper.Density.CappedUniformParameters
#print axioms Paper.Density.CappedUniformParameters.parameters
