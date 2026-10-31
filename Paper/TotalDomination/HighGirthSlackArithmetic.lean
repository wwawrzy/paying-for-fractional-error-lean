import Paper.TotalDomination.HighGirthSavingArithmetic
namespace Paper.TotalDomination.HighGirthSlackArithmetic
noncomputable def betaW (a : ℝ) : ℝ := 2+7*(5-2*a)/(9-8*a)
noncomputable def betaJ (a : ℝ) : ℝ := (2*a+6*(3-a))/(3-2*a)+14*(6*a-4)*(3-a)/((9-8*a)*(3-2*a))
noncomputable def betaF (a : ℝ) : ℝ := 14/(9-8*a)
noncomputable def betaP (a : ℝ) : ℝ := 7*(15-12*a)/(9-8*a)
noncomputable def betaSaving (a : ℝ) : ℝ := (9-8*a)/(3*(3-2*a))
noncomputable def accuracy (a : ℝ) : ℝ := min (1/(3*betaW a))
  (min (betaSaving a/betaJ a) (min (1/betaF a) (1/betaP a)))

theorem coefficients_positive (a : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8) :
    0 < betaW a ∧ 0 < betaJ a ∧ 0 < betaF a ∧ 0 < betaP a ∧ 0 < betaSaving a := by
  have h1 : 0 < 9-8*a := by linarith
  have h2 : 0 < 3-2*a := by linarith
  have h3 : 0 < 5-2*a := by linarith
  have h4 : 0 < 3-a := by linarith
  have h5 : 0 < 6*a-4 := by linarith
  have h6 : 0 < 15-12*a := by linarith
  have h7 : 0 < a := by linarith
  dsimp [betaW,betaJ,betaF,betaP,betaSaving]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> positivity

theorem accuracy_positive (a : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8) : 0 < accuracy a := by
  obtain ⟨hw,hj,hf,hp,hs⟩ := coefficients_positive a ha hhi
  unfold accuracy
  positivity

theorem size_bound (a w h y j q f z D : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hH : h ≤ a*j/(3-2*a)) (hY : y ≤ (3-a)*j/(3-2*a))
    (hq : (9-8*a)/2*q ≤ (5-2*a)/2*w+(6*a-4)*y+f+(15-12*a)/2*z)
    (hD : D ≤ 2*w+2*h+6*y+7*q) :
    D ≤ betaW a*w+betaJ a*j+betaF a*f+betaP a*z := by
  have hd : 0 < 9-8*a := by linarith
  have hd' : 0 < 3-2*a := by linarith
  have hy : 0 ≤ 6+14*(6*a-4)/(9-8*a) := by
    have hh : 0 ≤ 6*a-4 := by linarith
    positivity
  have hq' : q ≤ ((5-2*a)/2*w+(6*a-4)*y+f+(15-12*a)/2*z)/((9-8*a)/2) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hq])
  calc
    D ≤ 2*w+2*h+6*y+7*(((5-2*a)/2*w+(6*a-4)*y+f+(15-12*a)/2*z)/((9-8*a)/2)) := by linarith
    _ = betaW a*w+2*h+(6+14*(6*a-4)/(9-8*a))*y+betaF a*f+betaP a*z := by
      dsimp [betaW,betaF,betaP]; field_simp [ne_of_gt hd,ne_of_gt hd']; ring
    _ ≤ betaW a*w+2*(a*j/(3-2*a))+(6+14*(6*a-4)/(9-8*a))*((3-a)*j/(3-2*a))+betaF a*f+betaP a*z := by
      have hh := mul_le_mul_of_nonneg_left hH (by norm_num : (0:ℝ) ≤ 2)
      have hyy := mul_le_mul_of_nonneg_left hY hy
      linarith
    _ = _ := by dsimp [betaJ]; field_simp [ne_of_gt hd,ne_of_gt hd']; ring



theorem slack (a w j f z D cost : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hw : 0 ≤ w) (hj : 0 ≤ j) (hf : 0 ≤ f) (hz : 0 ≤ z)
    (hcount : D ≤ betaW a*w+betaJ a*j+betaF a*f+betaP a*z)
    (hsaving : w/3+betaSaving a*j+f+z ≤ cost-D) :
    (1+accuracy a)*D ≤ cost := by
  obtain ⟨hbw,hbj,hbf,hbp,hbs⟩ := coefficients_positive a ha hhi
  have hδ := accuracy_positive a ha hhi
  have hW : accuracy a*betaW a ≤ 1/3 := by
    have h : accuracy a ≤ 1/(3*betaW a) := min_le_left _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 3*betaW a)).mp h
    nlinarith
  have hJ : accuracy a*betaJ a ≤ betaSaving a := by
    have h : accuracy a ≤ betaSaving a/betaJ a := (min_le_right _ _).trans (min_le_left _ _)
    exact (le_div_iff₀ hbj).mp h
  have hF : accuracy a*betaF a ≤ 1 := by
    have h : accuracy a ≤ 1/betaF a := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (le_div_iff₀ hbf).mp h
  have hP : accuracy a*betaP a ≤ 1 := by
    have h : accuracy a ≤ 1/betaP a := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    exact (le_div_iff₀ hbp).mp h
  have hpaid : accuracy a*D ≤ w/3+betaSaving a*j+f+z := by
    calc
      _ ≤ accuracy a*(betaW a*w+betaJ a*j+betaF a*f+betaP a*z) := mul_le_mul_of_nonneg_left hcount hδ.le
      _ = (accuracy a*betaW a)*w+(accuracy a*betaJ a)*j+(accuracy a*betaF a)*f+(accuracy a*betaP a)*z := by ring
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_right hW hw
        have h2 := mul_le_mul_of_nonneg_right hJ hj
        have h3 := mul_le_mul_of_nonneg_right hF hf
        have h4 := mul_le_mul_of_nonneg_right hP hz
        linarith
  nlinarith only [hpaid,hsaving]

theorem numerical_coefficients : betaSaving (19/17)=1/39 ∧ betaW (19/17)=331 ∧
    betaJ (19/17)=20838/13 ∧ betaF (19/17)=238 ∧ betaP (19/17)=189 ∧
    accuracy (19/17)=1/62514 := by
  norm_num [betaSaving,betaW,betaJ,betaF,betaP,accuracy]

def rationalAccuracy (a : ℚ) : ℚ :=
  let w := 2+7*(5-2*a)/(9-8*a)
  let j := (2*a+6*(3-a))/(3-2*a)+14*(6*a-4)*(3-a)/((9-8*a)*(3-2*a))
  let f := 14/(9-8*a)
  let p := 7*(15-12*a)/(9-8*a)
  let b := (9-8*a)/(3*(3-2*a))
  min (1/(3*w)) (min (b/j) (min (1/f) (1/p)))

theorem rational_accuracy_cast (a : ℚ) : (rationalAccuracy a : ℝ)=accuracy (a:ℝ) := by
  norm_num [rationalAccuracy,accuracy,betaW,betaJ,betaF,betaP,betaSaving,Rat.cast_min]

theorem rational_accuracy_positive (a : ℚ) (ha : 1 ≤ a) (hhi : a < 9/8) : 0 < rationalAccuracy a := by
  have hhiR : (a:ℝ) < ((9/8:ℚ):ℝ) := Rat.cast_lt.mpr hhi
  norm_num at hhiR
  have h := accuracy_positive (a:ℝ) (by exact_mod_cast ha) hhiR
  rw [←rational_accuracy_cast] at h
  exact_mod_cast h

theorem rational_accuracy_numerical : rationalAccuracy (19/17)=1/62514 := by
  norm_num [rationalAccuracy]

end Paper.TotalDomination.HighGirthSlackArithmetic
#print axioms Paper.TotalDomination.HighGirthSlackArithmetic.slack
