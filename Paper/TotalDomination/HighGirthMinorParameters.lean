import Paper.TotalDomination.HighGirthSlackArithmetic
import Mathlib.Algebra.Order.Floor.Ring

/-! Exact floor/max parameters of fv:hg:minor-three. These establish the
numerical threshold; the separate girth-dilution construction is required
before applying them to all members of a minor-density class. -/
namespace Paper.TotalDomination.HighGirthMinorParameters

def radius (rho : Rat) : Nat := max 1 ⌊8 * (rho - 1)⌋₊
def girth (rho : Rat) : Nat := 8 * radius rho + 3
def density (rho : Rat) : Rat := 1 + (rho - 1) / ((radius rho : Rat) + 1)

theorem radius_integer_formula (rho : Rat) (hrho : 1 ≤ rho) :
    (radius rho : Int) = max 1 ⌊8 * (rho - 1)⌋ := by
  have hnon : 0 ≤ 8 * (rho - 1) := by linarith
  simp only [radius, Nat.cast_max, Nat.cast_one]
  rw [Int.natCast_floor_eq_floor hnon]

theorem radius_pos (rho : Rat) : 1 ≤ radius rho := le_max_left _ _

theorem girth_strict (rho : Rat) : 8 * radius rho + 2 < girth rho := by
  unfold girth
  omega

theorem density_range (rho : Rat) (hrho : 1 ≤ rho) :
    1 ≤ density rho ∧ density rho < 9/8 := by
  have hrad : (⌊8 * (rho - 1)⌋₊ : Rat) ≤ (radius rho : Rat) := by
    exact_mod_cast (le_max_right 1 ⌊8 * (rho - 1)⌋₊)
  have hf := Nat.lt_floor_add_one (8 * (rho - 1))
  have hd : (0 : Rat) < (radius rho : Rat) + 1 := by positivity
  have hn : 0 ≤ rho - 1 := by linarith
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hn hd.le)
  · have hdiv : (rho - 1) / ((radius rho : Rat) + 1) < 1/8 := by
      apply (div_lt_div_iff₀ hd (by norm_num : (0 : Rat) < 8)).mpr
      linarith
    unfold density
    linarith


end Paper.TotalDomination.HighGirthMinorParameters
#print axioms Paper.TotalDomination.HighGirthMinorParameters.density_range
