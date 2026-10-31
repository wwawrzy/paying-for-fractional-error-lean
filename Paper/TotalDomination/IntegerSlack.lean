import Paper.TotalDomination.IntegerSaving

/-! Exact positive slack for the integer total-domination rounding rule.
The solver accuracy is still an explicit premise; this is the mathematical
rounding endpoint, not a distributed solver implementation. -/
namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

def countM (d : ℕ) : ℝ := (d:ℝ)^3-(d:ℝ)^2+d+1
def countGamma (d : ℕ) (κ : ℝ) : ℝ := countM d*(κ+1)
noncomputable def betaW (d : ℕ) (κ : ℝ) : ℝ := 1+countM d*κ+countGamma d κ*d*((d:ℝ)+2)/2
noncomputable def betaJ (d : ℕ) (κ : ℝ) : ℝ := countGamma d κ*(d:ℝ)^2/2
def betaP (d : ℕ) (κ : ℝ) : ℝ := 2*((d:ℝ)-1)*countM d+countGamma d κ*((d:ℝ)-1)*((d:ℝ)^2+2)
def betaOmega (d : ℕ) (κ : ℝ) : ℝ := countGamma d κ*d
noncomputable def accuracy (d : ℕ) (κ : ℝ) : ℝ :=
  min (1/(2*betaW d κ)) (min (1/(4*betaJ d κ)) (min (1/betaP d κ) (1/betaOmega d κ)))

theorem coefficients_positive (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 ≤ κ) :
    0 < betaW d κ ∧ 0 < betaJ d κ ∧ 0 < betaP d κ ∧ 0 < betaOmega d κ := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hM : 0 < countM d := by
    have h : (0:ℝ) ≤ (d:ℝ)^2*((d:ℝ)-1) := mul_nonneg (sq_nonneg _) (by linarith)
    dsimp [countM]
    nlinarith
  have hΓ : 0 < countGamma d κ := mul_pos hM (by linarith)
  have hdpos : (0:ℝ) < d := by linarith
  have hdm : (0:ℝ) < (d:ℝ)-1 := by linarith
  dsimp [betaW,betaJ,betaP,betaOmega]
  refine ⟨?_,?_,?_,?_⟩ <;> positivity

theorem accuracy_positive (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 ≤ κ) : 0 < accuracy d κ := by
  obtain ⟨hw,hj,hp,ho⟩ := coefficients_positive d hd hκ
  unfold accuracy
  positivity

theorem slack (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 ≤ κ)
    (hden : Incidence.InducedDensityBound G ((d:ℝ)/2))
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) (hsupport : ∀ v ∉ K G d, x v = 0)
    (hdefects : ((WeightedBudget.defects G d ∩ core G d x identifier hfree).card : ℝ) ≤
      κ*((servedLow G d x identifier hfree).card+(first G (I G d x identifier hfree)).card)) :
    (1+accuracy d κ)*(output G (I G d x identifier hfree)).card ≤
      objective G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
  have hc := selected_count G d x identifier hfree hd κ hκ hden hx hcap hdefects
  change ((output G (I G d x identifier hfree)).card : ℝ) ≤
    betaW d κ*(first G (I G d x identifier hfree)).card+
    betaJ d κ*surplus G (I G d x identifier hfree)+
    betaP d κ*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ))+
    betaOmega d κ*oversupply G (I G d x identifier hfree) at hc
  obtain ⟨hp,ho,hs⟩ := integer_saving G d x identifier hfree hd hden hx hsupport
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hj := surplus_nonneg G (I G d x identifier hfree) ((d:ℝ)/2) (by positivity)
    hden (by change 2*((d:ℝ)/2) ≤ (d:ℝ); linarith)
  obtain ⟨hbw,hbj,hbp,hbo⟩ := coefficients_positive d hd hκ
  have hδ := accuracy_positive d hd hκ
  have hw : accuracy d κ*betaW d κ ≤ 1/2 := by
    have h := min_le_left (1/(2*betaW d κ)) (min (1/(4*betaJ d κ)) (min (1/betaP d κ) (1/betaOmega d κ)))
    change accuracy d κ ≤ _ at h
    have h' := (le_div_iff₀ (by positivity : 0 < 2*betaW d κ)).mp h
    nlinarith
  have hJ : accuracy d κ*betaJ d κ ≤ 1/4 := by
    have h : accuracy d κ ≤ 1/(4*betaJ d κ) := (min_le_right _ _).trans (min_le_left _ _)
    have h' := (le_div_iff₀ (by positivity : 0 < 4*betaJ d κ)).mp h
    nlinarith
  have hP : accuracy d κ*betaP d κ ≤ 1 := by
    have h : accuracy d κ ≤ 1/betaP d κ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (le_div_iff₀ hbp).mp h
  have hO : accuracy d κ*betaOmega d κ ≤ 1 := by
    have h : accuracy d κ ≤ 1/betaOmega d κ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    exact (le_div_iff₀ hbo).mp h
  have hpaid : accuracy d κ*(output G (I G d x identifier hfree)).card ≤
      (first G (I G d x identifier hfree)).card/2+surplus G (I G d x identifier hfree)/4+
      penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ))+
      oversupply G (I G d x identifier hfree) := by
    calc
      _ ≤ accuracy d κ*(betaW d κ*(first G (I G d x identifier hfree)).card+
        betaJ d κ*surplus G (I G d x identifier hfree)+
        betaP d κ*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ))+
        betaOmega d κ*oversupply G (I G d x identifier hfree)) := mul_le_mul_of_nonneg_left hc hδ.le
      _ = (accuracy d κ*betaW d κ)*(first G (I G d x identifier hfree)).card+
        (accuracy d κ*betaJ d κ)*surplus G (I G d x identifier hfree)+
        (accuracy d κ*betaP d κ)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ))+
        (accuracy d κ*betaOmega d κ)*oversupply G (I G d x identifier hfree) := by ring
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg (first G (I G d x identifier hfree)).card)
        have h2 := mul_le_mul_of_nonneg_right hJ hj
        have h3 := mul_le_mul_of_nonneg_right hP hp
        have h4 := mul_le_mul_of_nonneg_right hO ho
        linarith
  linarith

end Paper.TotalDomination.IntegerSetup
#print axioms Paper.TotalDomination.IntegerSetup.slack
