import Paper.Endpoints.Rounding.AdditiveThresholdGeometry

namespace Paper.AdditiveThreshold
open ApproximateOrientation OrientationShares
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem copied_bound (a η t : ℝ) (ht : 0 ≤ t) (x : V → ℝ)
    (hx : PartialOptimum.Feasible G Finset.univ x)
    (hden : ∀ S : Finset V, (G.inducedEdgeCount S : ℝ) ≤ a*S.card+η)
    (q : ℕ) (hq : 0 < q) :
    (1-t-t*((⌈a*q⌉₊ : ℝ)/q))*(residual G t x).card ≤
      ((⌈a*q⌉₊ : ℝ)/q)*(∑ v ∈ low G t x, x v) + 2*t*((⌈η*q⌉₊ : ℝ)/q) := by
  classical
  obtain ⟨O,err,hl,he⟩ := ApproximateOrientation.exists_scaled G a η q hden
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  apply FractionalCharging.bound (residual G t x) (low G t x) (share G O) x
    (fun v => (err v : ℝ)/q) ((⌈a*q⌉₊ : ℝ)/q) t ((⌈η*q⌉₊ : ℝ)/q)
    (div_nonneg (Nat.cast_nonneg _) hqR.le) ht
    (share_nonneg G O) hx.1
    (fun v => div_nonneg (Nat.cast_nonneg _) hqR.le)
  · rw [← Finset.sum_div]
    apply (div_le_div_iff_of_pos_right hqR).mpr
    exact_mod_cast he
  · intro v
    rw [share_load,← add_div]
    apply (div_le_div_iff_of_pos_right hqR).mpr
    exact_mod_cast hl v
  · exact low_small G t x
  · exact residual_small G t x
  · exact local_feasibility G t x (share G O) (share_zero G O) (share_pair G O hq) hx

theorem ceil_div_bound (a : ℝ) (ha : 0 ≤ a) (q : ℕ) (hq : 0 < q) :
    (⌈a*q⌉₊ : ℝ)/q ≤ a + 1/q := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  apply (div_le_iff₀ hqR).mpr
  have h := (Nat.ceil_lt_add_one (mul_nonneg ha hqR.le)).le
  have heq : (a + 1/(q:ℝ)) * q = a*q+1 := by field_simp
  rwa [heq]

theorem le_of_recip_error (A B C : ℝ)
    (h : ∀ q : ℕ, 0 < q → A ≤ B+C/q) : A ≤ B := by
  by_contra hn
  have hg : 0 < A-B := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨q,hq⟩ := exists_nat_gt (max 0 (C/(A-B)))
  have hqR : (0:ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqN : 0 < q := by exact_mod_cast hqR
  have hmul : C < (A-B)*q := by
    have hh := (div_lt_iff₀ hg).mp (lt_of_le_of_lt (le_max_right _ _) hq)
    nlinarith only [hh]
  have hdiv := (div_lt_iff₀ hqR).mpr hmul
  linarith [h q hqN]

theorem residual_bound (a η t : ℝ) (ha : 0 ≤ a) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x)
    (hden : ∀ S : Finset V, (G.inducedEdgeCount S : ℝ) ≤ a*S.card+η) :
    (1-t-t*a)*(residual G t x).card ≤ a*(∑ v ∈ low G t x, x v)+2*t*η := by
  classical
  let n : ℝ := (residual G t x).card
  let M : ℝ := ∑ v ∈ low G t x, x v
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hM : 0 ≤ M := Finset.sum_nonneg fun v _ => hx.1 v
  apply le_of_recip_error _ _ (t*n+M+2*t)
  intro q hq
  have hc := copied_bound G a η t ht x hx hden q hq
  have hp := ceil_div_bound a ha q hq
  have he := ceil_div_bound η hη q hq
  have h1 := mul_le_mul_of_nonneg_right hp (add_nonneg (mul_nonneg ht hn) hM)
  have h2 := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht)
  change (1-t-t*((⌈a*q⌉₊ : ℝ)/q))*n ≤ ((⌈a*q⌉₊ : ℝ)/q)*M+2*t*((⌈η*q⌉₊ : ℝ)/q) at hc
  change (1-t-t*a)*n ≤ a*M+2*t*η+(t*n+M+2*t)/q
  simp only [div_eq_mul_inv] at hc h1 h2 ⊢
  nlinarith only [hc,h1,h2]

theorem output_bound (a η : ℝ) (ha : 0 < a) (hη : 0 ≤ η)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x)
    (hden : ∀ S : Finset V, (G.inducedEdgeCount S : ℝ) ≤ a*S.card+η) :
    ((output G (1/(2*a+1)) x).card : ℝ) ≤ (2*a+1)*(∑ v, x v)+2*η/a := by
  classical
  let b := 2*a+1
  have hb : 0 < b := by dsimp [b];linarith
  have ht : 0 ≤ 1/b := (div_pos zero_lt_one hb).le
  have hr := residual_bound G a η (1/b) ha.le hη ht x hx hden
  have hw := first_mass G (1/b) x
  have hcoef : 1-1/b-1/b*a = a/b := by dsimp [b];field_simp;ring
  rw [hcoef] at hr
  have hr' := mul_le_mul_of_nonneg_left hr hb.le
  have hw' := mul_le_mul_of_nonneg_left hw (mul_nonneg ha.le hb.le)
  have hcancel : b*(a/b) = a := by field_simp
  have hcancel' : b*(1/b) = 1 := by field_simp
  have hcancelη : b*(2*(1/b)*η) = 2*η := by field_simp
  have hr'' : a*(residual G (1/b) x).card ≤
      a*b*(∑ v ∈ low G (1/b) x, x v)+2*η := by
    nlinarith only [hr',hcancel,hcancelη]
  have hw'' : a*(first G (1/b) x).card ≤ a*b*(∑ v ∈ first G (1/b) x, x v) := by
    have heqW : a*b*(1/b*((first G (1/b) x).card : ℝ)) = a*(first G (1/b) x).card := by field_simp
    rw [heqW] at hw'
    exact hw'
  have hs := Finset.sum_sdiff (s₁ := first G (1/b) x) (s₂ := Finset.univ)
    (f := x) (Finset.subset_univ _)
  change (∑ v ∈ low G (1/b) x, x v)+(∑ v ∈ first G (1/b) x, x v) = ∑ v, x v at hs
  have hc : ((output G (1/b) x).card : ℝ) ≤
      (first G (1/b) x).card+(residual G (1/b) x).card := by
    exact_mod_cast Finset.card_union_le (first G (1/b) x) (residual G (1/b) x)
  have hc' := mul_le_mul_of_nonneg_left hc ha.le
  have hbound : a*(output G (1/b) x).card ≤ a*b*(∑ v, x v)+2*η := by
    have hs' := congrArg (fun z : ℝ => a*b*z) hs
    nlinarith only [hr'',hw'',hs',hc']
  have hdiv : ((output G (1/b) x).card : ℝ) ≤ (a*b*(∑ v, x v)+2*η)/a :=
    (le_div_iff₀ ha).mpr (by nlinarith only [hbound])
  have heq : (a*b*(∑ v, x v)+2*η)/a = b*(∑ v, x v)+2*η/a := by field_simp
  rw [heq] at hdiv
  exact hdiv

end Paper.AdditiveThreshold
#print axioms Paper.AdditiveThreshold.copied_bound
