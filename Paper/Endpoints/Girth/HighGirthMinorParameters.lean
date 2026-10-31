import Paper.Endpoints.Girth.HighGirthSlackParameter
import Mathlib.Algebra.Order.Floor.Ring

/-! Exact floor/max parameters of fv:hg:minor-three. These establish the
numerical threshold; the separate girth-dilution construction is required
before applying them to all members of a minor-density class. -/
namespace Paper.HighGirthMinorParameters

def radius (rho : Rat) : Nat := max 1 ⌊7 * (rho - 1)⌋₊
def girth (rho : Rat) : Nat := 8 * radius rho + 3
def density (rho : Rat) : Rat := 1 + (rho - 1) / ((radius rho : Rat) + 1)

theorem radius_integer_formula (rho : Rat) (hrho : 1 ≤ rho) :
    (radius rho : Int) = max 1 ⌊7 * (rho - 1)⌋ := by
  have hnon : 0 ≤ 7 * (rho - 1) := by linarith
  simp only [radius, Nat.cast_max, Nat.cast_one]
  rw [Int.natCast_floor_eq_floor hnon]

theorem radius_pos (rho : Rat) : 1 ≤ radius rho := le_max_left _ _

theorem girth_strict (rho : Rat) : 8 * radius rho + 2 < girth rho := by
  unfold girth
  omega

theorem density_range (rho : Rat) (hrho : 1 ≤ rho) :
    1 ≤ density rho ∧ density rho < 8/7 := by
  have hrad : (⌊7 * (rho - 1)⌋₊ : Rat) ≤ (radius rho : Rat) := by
    exact_mod_cast (le_max_right 1 ⌊7 * (rho - 1)⌋₊)
  have hf := Nat.lt_floor_add_one (7 * (rho - 1))
  have hd : (0 : Rat) < (radius rho : Rat) + 1 := by positivity
  have hn : 0 ≤ rho - 1 := by linarith
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hn hd.le)
  · have hdiv : (rho - 1) / ((radius rho : Rat) + 1) < 1/7 := by
      apply (div_lt_div_iff₀ hd (by norm_num : (0 : Rat) < 7)).mpr
      linarith
    unfold density
    linarith

theorem delta_pos (a : Rat) (ha : 1 ≤ a) (hu : a < 8/7) :
    0 < HighGirthSlackParameter.delta a := by
  have h8 : 0 < 8 - 7*a := by linarith
  have h3 : 0 < 3 - 2*a := by linarith
  have h6 : 0 < 6 - 5*a := by linarith
  have h4 : 0 < 4 - 3*a := by linarith
  have h42 : 0 < 4*a - 2 := by linarith
  have hb : 0 < HighGirthSlackParameter.beta a := by
    unfold HighGirthSlackParameter.beta
    positivity
  have hw : 0 < HighGirthSlackParameter.bw a := by
    unfold HighGirthSlackParameter.bw
    positivity
  have hl : 0 < HighGirthSlackParameter.bl a := by
    unfold HighGirthSlackParameter.bl
    positivity
  have hp : 0 < HighGirthSlackParameter.bP a := by
    unfold HighGirthSlackParameter.bP
    positivity
  have ho : 0 < HighGirthSlackParameter.bO a := by
    unfold HighGirthSlackParameter.bO
    positivity
  unfold HighGirthSlackParameter.delta
  positivity

theorem accuracy_pos (rho : Rat) (hrho : 1 ≤ rho) :
    0 < HighGirthSlackParameter.delta (density rho) :=
  delta_pos _ (density_range rho hrho).1 (density_range rho hrho).2

theorem planar_parameters : radius 3 = 14 ∧ girth 3 = 115 := by
  norm_num [radius, girth]

end Paper.HighGirthMinorParameters
#print axioms Paper.HighGirthMinorParameters.radius_integer_formula
#print axioms Paper.HighGirthMinorParameters.radius_pos
#print axioms Paper.HighGirthMinorParameters.girth_strict
#print axioms Paper.HighGirthMinorParameters.density_range
#print axioms Paper.HighGirthMinorParameters.delta_pos
#print axioms Paper.HighGirthMinorParameters.accuracy_pos
#print axioms Paper.HighGirthMinorParameters.planar_parameters
