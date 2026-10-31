import Paper.Endpoints.Rounding.CoveringSolverRounding

/-! The approximation factors of the executed numerical rounding, before
instantiating its fractional input with the full covering solver. -/
namespace Paper.CoveringApproximateRounding

open BroadcastModel SevenFoundation
open CoveringThresholdInput CoveringThresholdCost GeneralCoveringRounding
open scoped BigOperators
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

theorem scale_error {D F τ ε s : ℝ} (hs : 0 < s)
    (hD : D ≤ s * F) (hF : F ≤ (1 + ε / s) * τ) : D ≤ (s + ε) * τ := by
  have he : s * (1 + ε / s) = s + ε := by
    field_simp
    <;> ring
  calc
    D ≤ s * F := hD
    _ ≤ s * ((1 + ε / s) * τ) := mul_le_mul_of_nonneg_left hF hs.le
    _ = (s + ε) * τ := by rw [← mul_assoc, he]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem closed_bound {b B : ℕ} (ids : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hden : Incidence.InducedDensityBound (incidenceGraph G (rows s)) (a : ℝ))
    (hcover : ∀ r, (s r).demand = true → 1 ≤ ∑ v ∈ (s r).candidates, vector q s v)
    (τ ε : ℝ)
    (happrox : (∑ v, cost s v * vector q s v) ≤ (1 + ε / (2 * (a : ℝ) + 1)) * τ) :
    (∑ v ∈ output G ids (2 * a + 1) q s, cost s v) ≤ (2 * (a : ℝ) + 1 + ε) * τ :=
  scale_error (by positivity) (closed_cost G ids a q ha hq s hlocal hrows hden hcover) happrox

theorem open_bound {b B : ℕ} (ids : BitCode V b) (a q : ℕ) (ha : 1 ≤ a) (hq : 0 < q)
    (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty)
    (hden : Incidence.InducedDensityBound (incidenceGraph G (rows s)) (a : ℝ))
    (hself : ∀ r, (s r).demand = true → r ∉ (s r).candidates)
    (hcover : ∀ r, (s r).demand = true → 1 ≤ ∑ v ∈ (s r).candidates, vector q s v)
    (τ ε : ℝ)
    (happrox : (∑ v, cost s v * vector q s v) ≤ (1 + ε / (2 * (a : ℝ))) * τ) :
    (∑ v ∈ output G ids (2 * a) q s, cost s v) ≤ (2 * (a : ℝ) + ε) * τ := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  exact scale_error (by linarith) (open_cost G ids a q ha hq s hlocal hrows hden hself hcover) happrox

end Paper.CoveringApproximateRounding

#print axioms Paper.CoveringApproximateRounding.closed_bound
#print axioms Paper.CoveringApproximateRounding.open_bound
