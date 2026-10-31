import Paper.Certificates.Counting.PartialOptimum
import Paper.Certificates.Counting.HallOrientation
import Paper.Certificates.Counting.WeightedCertificate
import Paper.Preliminaries.WeightedIntegrality

/-! Standalone certificate and integrality bounds under induced-subgraph
density only. These are the exact density hypotheses needed by the proofs;
no bound on arbitrary minors is assumed. -/
namespace Paper.SubgraphCertificates
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A weighted q-fold closed-neighborhood cover of cost at most
`(q + 2*ceil(a))` times the weighted fractional optimum. -/
theorem certificate_optimum (a : ℝ) (ha : 1 ≤ a)
    (hden : Incidence.InducedDensityBound G a)
    (R : Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) (q : ℕ) :
    ∃ m : V → ℕ,
      (∀ r ∈ R, q ≤ ∑ v ∈ closed G r, m v) ∧
      (∑ v, c v * (m v : ℝ)) ≤
        (q + 2 * (Nat.ceil a : ℝ)) * PartialOptimum.number G R c := by
  let p := Nat.ceil a
  have hpa : a ≤ (p : ℝ) := Nat.le_ceil a
  have hp : 1 ≤ p := by
    exact_mod_cast ha.trans hpa
  obtain ⟨x, hx, he⟩ := PartialOptimum.exists_optimum_eq_number G R c hc
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density G hden p hpa
  obtain ⟨m, hm, hb⟩ :=
    WeightedCertificate.exists_certificate G R O hp q c x hx.1 hx.2
  change (∑ v, c v * x v) = PartialOptimum.number G R c at he
  rw [he] at hb
  exact ⟨m, hm, hb⟩

/-- One integral cover simultaneously meets the weighted cost bound and,
when every cost is at least one, the cardinality bound. -/
theorem integral_optimum (a : ℝ) (ha : 1 ≤ a)
    (hden : Incidence.InducedDensityBound G a)
    (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (hc_one : ∀ v, 1 ≤ c v) :
    ∃ D : Finset V,
      R ⊆ covered G D ∧
      (D.card : ℝ) ≤
        (2 * (Nat.ceil a : ℝ) + 1) * PartialOptimum.number G R c ∧
      (∑ v ∈ D, c v) ≤
        (2 * (Nat.ceil a : ℝ) + 1) * PartialOptimum.number G R c := by
  let p := Nat.ceil a
  have hpa : a ≤ (p : ℝ) := Nat.le_ceil a
  have hp : 1 ≤ p := by
    exact_mod_cast ha.trans hpa
  have hnat (S : Finset V) : G.inducedEdgeCount S ≤ p * S.card := by
    have hreal : (G.inducedEdgeCount S : ℝ) ≤ (p : ℝ) * S.card :=
      (hden S).trans (mul_le_mul_of_nonneg_right hpa (Nat.cast_nonneg S.card))
    exact_mod_cast hreal
  obtain ⟨x, hx, he⟩ := PartialOptimum.exists_optimum_eq_number G R c hc
  obtain ⟨D, hD, hb⟩ :=
    WeightedIntegrality.exists_integral_cover G R p hp hnat c x hc hx.1 hx.2
  have hD' : R ⊆ covered G D := by
    intro r hr
    exact hD r hr
  have he' : (∑ v, c v * x v) = PartialOptimum.number G R c := by
    change PartialOptimum.objective c x = PartialOptimum.number G R c at he
    exact he
  have hcost : (∑ v ∈ D, c v) ≤
      (2 * (Nat.ceil a : ℝ) + 1) * PartialOptimum.number G R c := by
    rw [he'] at hb
    simpa only [p, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add] using hb
  have hcardCost : (D.card : ℝ) ≤ ∑ v ∈ D, c v := by
    calc
      (D.card : ℝ) = ∑ v ∈ D, (1 : ℝ) := by simp
      _ ≤ ∑ v ∈ D, c v := Finset.sum_le_sum (fun v _ => hc_one v)
  exact ⟨D, hD', hcardCost.trans hcost, hcost⟩

end Paper.SubgraphCertificates

#print axioms Paper.SubgraphCertificates.certificate_optimum
#print axioms Paper.SubgraphCertificates.integral_optimum
