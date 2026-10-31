import Mathlib
namespace Paper.RedBlueSurfaceCharging
variable {V : Type} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
/-- The weighted per-demand charge, allowing a nonzero orientation overload. -/
theorem request_charge (C : Finset V) (x c win wout : V → ℝ) (μ b er : ℝ)
    (hμ : 0 ≤ μ) (hμb : μ ≤ b) (her : 0 ≤ er)
    (hx : ∀ v ∈ C, 0 ≤ x v) (hsmall : ∀ v ∈ C, x v ≤ 1/4)
    (hc : ∀ v ∈ C, μ ≤ c v)
    (hwi : ∀ v ∈ C, 0 ≤ win v) (hwo : ∀ v ∈ C, 0 ≤ wout v)
    (hpair : ∀ v ∈ C, win v+wout v=1)
    (hload : (∑ v ∈ C, wout v) ≤ 2+er)
    (hcover : 1 ≤ ∑ v ∈ C, x v) :
    μ ≤ 2*(∑ v ∈ C, win v*c v*x v)+b*er/2 := by
  have hout : (∑ v ∈ C, wout v*x v) ≤ (2+er)/4 := by
    calc
      _ ≤ ∑ v ∈ C, wout v*(1/4) := Finset.sum_le_sum fun v hv =>
        mul_le_mul_of_nonneg_left (hsmall v hv) (hwo v hv)
      _ = (∑ v ∈ C, wout v)/4 := by rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro v hv; ring
      _ ≤ _ := div_le_div_of_nonneg_right hload (by norm_num)
  have hsplit : (∑ v ∈ C, win v*x v)+(∑ v ∈ C, wout v*x v)=∑ v ∈ C, x v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← add_mul,hpair v hv,one_mul]
  have hin : (2-er)/4 ≤ ∑ v ∈ C, win v*x v := by linarith
  have hm := mul_le_mul_of_nonneg_left hin hμ
  have hcost : μ*(∑ v ∈ C, win v*x v) ≤ ∑ v ∈ C, win v*c v*x v := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hh := mul_le_mul_of_nonneg_right (hc v hv) (mul_nonneg (hwi v hv) (hx v hv))
    nlinarith only [hh]
  have he := mul_le_mul_of_nonneg_right hμb her
  nlinarith
theorem requests_charge (T B : Finset V) (hTB : Disjoint T B)
    (w : V → V → ℝ) (c x μ err : V → ℝ) (b E : ℝ)
    (hb : 0 ≤ b) (herr : ∀ v, 0 ≤ err v) (hbudget : (∑ v, err v) ≤ E)
    (hc : ∀ v ∈ B, 0 ≤ c v ∧ c v ≤ b)
    (hx : ∀ v ∈ B, 0 ≤ x v ∧ x v ≤ 1/4)
    (hcol : ∀ v ∈ B, (∑ r ∈ T, w r v) ≤ 2+err v)
    (hcharge : ∀ r ∈ T, μ r ≤ 2*(∑ v ∈ B, w r v*c v*x v)+b*err r/2) :
    (∑ r ∈ T, μ r) ≤ 4*(∑ v ∈ B, c v*x v)+b*E/2 := by
  have hdouble : (∑ r ∈ T, ∑ v ∈ B, w r v*c v*x v) =
      ∑ v ∈ B, (∑ r ∈ T, w r v)*c v*x v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.sum_mul,Finset.sum_mul]
  have hmass : (∑ r ∈ T, ∑ v ∈ B, w r v*c v*x v) ≤
      2*(∑ v ∈ B, c v*x v)+(b/4)*(∑ v ∈ B, err v) := by
    rw [hdouble,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v hv
    have hprod : 0 ≤ c v*x v := mul_nonneg (hc v hv).1 (hx v hv).1
    have hh := mul_le_mul_of_nonneg_right (hcol v hv) hprod
    have hcx : c v*x v ≤ b/4 := by
      have hh1 := mul_le_mul_of_nonneg_left (hx v hv).2 (hc v hv).1
      have hh2 := (hc v hv).2
      nlinarith
    have he := mul_le_mul_of_nonneg_left hcx (herr v)
    nlinarith
  have hsum := Finset.sum_le_sum (fun r hr => hcharge r hr)
  have hs : (∑ r ∈ T, μ r) ≤
      2*(∑ r ∈ T, ∑ v ∈ B, w r v*c v*x v)+(b/2)*(∑ r ∈ T, err r) := by
    calc
      _ ≤ _ := hsum
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
  have he : (∑ v ∈ B, err v)+(∑ r ∈ T, err r) ≤ E := by
    rw [← Finset.sum_union hTB.symm]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => herr v)).trans hbudget
  have hbe := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ b/2)
  nlinarith
end Paper.RedBlueSurfaceCharging
#print axioms Paper.RedBlueSurfaceCharging.request_charge
#print axioms Paper.RedBlueSurfaceCharging.requests_charge
