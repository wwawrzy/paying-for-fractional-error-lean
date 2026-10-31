import Paper.Certificates.Counting.PartialOptimum

/-! Exact finite coordinatewise averaging preserves actual partial-cover
constraints and weighted cost. This is mathematical feasibility, separate
from the local computation of each event probability. -/
namespace Paper.FiniteAverage
open scoped BigOperators
variable {Ω V : Type*} [Fintype Ω] [Nonempty Ω] [Fintype V] [DecidableEq V]

noncomputable def vector (x : Ω → V → ℝ) (v : V) : ℝ := (∑ ω, x ω v) / Fintype.card Ω

theorem card_pos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos

theorem nonneg (x : Ω → V → ℝ) (hx : ∀ ω v, 0 ≤ x ω v) (v : V) : 0 ≤ vector x v := by
  unfold vector
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => hx ω v)) (Nat.cast_nonneg _)

theorem sum_eq (x : Ω → V → ℝ) (S : Finset V) :
    (∑ v ∈ S, vector x v) = (∑ ω, ∑ v ∈ S, x ω v) / Fintype.card Ω := by
  unfold vector
  rw [← Finset.sum_div, Finset.sum_comm]

theorem feasible (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V)
    (x : Ω → V → ℝ) (hx : ∀ ω, PartialOptimum.Feasible G R (x ω)) :
    PartialOptimum.Feasible G R (vector x) := by
  refine ⟨nonneg x (fun ω v => (hx ω).1 v), ?_⟩
  intro r hr
  rw [sum_eq]
  apply (le_div_iff₀ (card_pos (Ω := Ω))).mpr
  have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => (hx ω).2 r hr)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul] using hs

theorem cost (c : V → ℝ) (x : Ω → V → ℝ) :
    PartialOptimum.objective c (vector x) = (∑ ω, PartialOptimum.objective c (x ω)) / Fintype.card Ω := by
  dsimp only [PartialOptimum.objective, vector]
  simp only [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem cost_bound (c : V → ℝ) (x : Ω → V → ℝ) (C : ℝ)
    (hC : (∑ ω, PartialOptimum.objective c (x ω)) ≤ Fintype.card Ω * C) :
    PartialOptimum.objective c (vector x) ≤ C := by
  rw [cost]
  apply (div_le_iff₀ (card_pos (Ω := Ω))).mpr
  simpa only [mul_comm] using hC
end Paper.FiniteAverage
