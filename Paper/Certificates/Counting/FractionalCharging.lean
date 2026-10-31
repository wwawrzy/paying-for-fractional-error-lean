import Paper.Certificates.Counting.OrientationShares

/-! The finite weighted charging calculation, separated from the construction
of endpoint shares and the graph-specific threshold sets. -/
namespace Paper.FractionalCharging
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bound (U L : Finset V) (w : V → V → ℝ) (x err : V → ℝ)
    (p t η : ℝ) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hw : ∀ u v, 0 ≤ w u v) (hx : ∀ v, 0 ≤ x v)
    (he : ∀ v, 0 ≤ err v) (het : (∑ v, err v) ≤ η)
    (hload : ∀ v, (∑ u, w u v) ≤ p + err v)
    (hsmall : ∀ v ∈ L, x v ≤ t) (hU : ∀ u ∈ U, x u ≤ t)
    (hfeas : ∀ u ∈ U, 1 ≤ x u + ∑ v ∈ L, (w u v + w v u) * x v) :
    (1-t-t*p) * U.card ≤ p * (∑ v ∈ L, x v) + 2*t*η := by
  classical
  have hrow (v : V) (S : Finset V) : (∑ u ∈ S, w u v) ≤ p + err v := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun u _ _ => hw u v)).trans (hload v)
  have hsumerr (S : Finset V) : (∑ v ∈ S, err v) ≤ η := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun v _ _ => he v)).trans het
  have hlower (u : V) (hu : u ∈ U) :
      1-t-t*(p+err u) ≤ ∑ v ∈ L, w u v * x v := by
    have ho : (∑ v ∈ L, w v u * x v) ≤ t*(p+err u) := by
      calc
        _ ≤ ∑ v ∈ L, w v u * t := Finset.sum_le_sum fun v hv =>
          mul_le_mul_of_nonneg_left (hsmall v hv) (hw v u)
        _ = t * (∑ v ∈ L, w v u) := by simp only [← Finset.sum_mul,mul_comm,Finset.mul_sum]
        _ ≤ t*(p+err u) := mul_le_mul_of_nonneg_left (hrow u L) ht
    have hf := hfeas u hu
    simp only [add_mul,Finset.sum_add_distrib] at hf
    linarith [hU u hu]
  have hlo := Finset.sum_le_sum hlower
  have hloweq : (∑ u ∈ U, (1-t-t*(p+err u))) =
      (1-t-t*p)*U.card - t*(∑ u ∈ U, err u) := by
    simp only [mul_add,sub_sub,Finset.sum_sub_distrib,Finset.sum_const,
      nsmul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  rw [hloweq] at hlo
  have hup : (∑ u ∈ U, ∑ v ∈ L, w u v * x v) ≤
      p*(∑ v ∈ L, x v) + t*η := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ v ∈ L, (∑ u ∈ U, w u v) * x v := by simp only [Finset.sum_mul]
      _ ≤ ∑ v ∈ L, (p+err v)*x v := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_right (hrow v U) (hx v)
      _ ≤ ∑ v ∈ L, (p*x v + err v*t) := Finset.sum_le_sum fun v hv => by
        have h := mul_le_mul_of_nonneg_left (hsmall v hv) (he v)
        nlinarith
      _ = p*(∑ v ∈ L, x v) + t*(∑ v ∈ L, err v) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,mul_comm]
      _ ≤ p*(∑ v ∈ L, x v) + t*η := by
        have h := mul_le_mul_of_nonneg_left (hsumerr L) ht
        linarith
  have herr := mul_le_mul_of_nonneg_left (hsumerr U) ht
  linarith

end Paper.FractionalCharging
#print axioms Paper.FractionalCharging.bound
