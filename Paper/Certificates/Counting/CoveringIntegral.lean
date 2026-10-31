import Paper.Certificates.Counting.CoveringCertificateOptimum

/-! Integral support covers for arbitrary local covering lists, derived from
the induced-subgraph density bound alone. -/
namespace Paper.CoveringIntegral
attribute [local instance] Classical.propDecidable
open SevenFoundation CoveringOptimum CoveringSupport
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vertices used by a nonnegative integral multiplicity vector. -/
def positiveSupport (m : V → ℕ) : Finset V :=
  Finset.univ.filter (fun v => 0 < m v)

/-- An integral cover of arbitrary nonempty lists, with its support contained
in the admissible union. The orientation is constructed from induced density;
it is not an endpoint hypothesis. -/
theorem exists_integral_optimum_cover (C : V → Finset V)
    (hclosed : ∀ r, C r ⊆ closed G r) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) {a : ℝ}
    (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    ∃ D : Finset V,
      (∀ v ∈ D, v ∈ admissible C R) ∧
      (∀ r ∈ R, (D ∩ C r).Nonempty) ∧
      (∑ v ∈ D, c v) ≤
        (2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c := by
  let p := Nat.ceil a
  have hpa : a ≤ (p : ℝ) := Nat.le_ceil a
  have hp : 1 ≤ p := by
    exact_mod_cast ha.trans hpa
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density G hden p hpa
  obtain ⟨m, hcover, hsupp, hcost⟩ :=
    CoveringCertificateOptimum.exists_optimum_certificate G C hclosed R hrows
      O hp 1 c hc
  let D := positiveSupport m
  have hDsupport : ∀ v ∈ D, v ∈ admissible C R := by
    intro v hv
    have hpos : 0 < m v := (Finset.mem_filter.mp hv).2
    by_contra hnot
    have hz := hsupp v hnot
    omega
  have hhit : ∀ r ∈ R, (D ∩ C r).Nonempty := by
    intro r hr
    by_contra hnone
    have hzero : ∀ v ∈ C r, m v = 0 := by
      intro v hv
      by_contra hne
      apply hnone
      refine ⟨v, ?_⟩
      apply Finset.mem_inter.mpr
      refine ⟨?_, hv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hsum : (∑ v ∈ C r, m v) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      exact hzero v hv
    have hcover_r := hcover r hr
    rw [hsum] at hcover_r
    have := hcover r hr
    omega
  have hcostD : (∑ v ∈ D, c v) ≤ ∑ v, c v * (m v : ℝ) := by
    calc
      (∑ v ∈ D, c v) ≤ ∑ v ∈ D, c v * (m v : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        have hm : (1 : ℝ) ≤ (m v : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp hv).2
        calc
          c v = c v * 1 := (mul_one _).symm
          _ ≤ c v * (m v : ℝ) := mul_le_mul_of_nonneg_left hm (hc v)
      _ ≤ ∑ v, c v * (m v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
          (fun v _ _ => mul_nonneg (hc v) (Nat.cast_nonneg _))
  have hbound : (∑ v, c v * (m v : ℝ)) ≤
      (1 + 2 * (p : ℝ)) * CoveringOptimum.number C R c := by
    simpa only [Nat.cast_one, p] using hcost
  refine ⟨D, hDsupport, hhit, ?_⟩
  calc
    (∑ v ∈ D, c v) ≤ ∑ v, c v * (m v : ℝ) := hcostD
    _ ≤ (1 + 2 * (p : ℝ)) * CoveringOptimum.number C R c := hbound
    _ = (2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c := by
      dsimp [p]
      ring

/-- If each selected vertex costs at least one, the very same cover also has
the corresponding cardinality bound. -/
theorem exists_integral_optimum_cover_card (C : V → Finset V)
    (hclosed : ∀ r, C r ⊆ closed G r) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) {a : ℝ}
    (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hc_one : ∀ v, 1 ≤ c v) :
    ∃ D : Finset V,
      (∀ v ∈ D, v ∈ admissible C R) ∧
      (∀ r ∈ R, (D ∩ C r).Nonempty) ∧
      (D.card : ℝ) ≤
        (2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c ∧
      (∑ v ∈ D, c v) ≤
        (2 * (Nat.ceil a : ℝ) + 1) * CoveringOptimum.number C R c := by
  obtain ⟨D, hDsupport, hhit, hcost⟩ :=
    exists_integral_optimum_cover G C hclosed R hrows ha hden c hc
  have hcard : (D.card : ℝ) ≤ ∑ v ∈ D, c v := by
    calc
      (D.card : ℝ) = ∑ v ∈ D, (1 : ℝ) := by simp
      _ ≤ ∑ v ∈ D, c v := Finset.sum_le_sum (fun v _ => hc_one v)
  exact ⟨D, hDsupport, hhit, hcard.trans hcost, hcost⟩

end Paper.CoveringIntegral
