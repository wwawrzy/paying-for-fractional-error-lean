import Paper.Preliminaries.OutcomeMath
import Paper.Averaging.Tasks.FiniteAverage

/-! Average actual feasible outcomes over any explicit finite partition
source. The only distribution input is its proved boundary-count sum. -/
namespace Paper.MeanOutcome
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
open scoped BigOperators
variable {V Ω : Type*} [Fintype V] [LinearOrder V] [Fintype Ω] [Nonempty Ω]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D R : Finset V) (L : ℕ) (Q : Finset D)
variable (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
variable (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hcost : ∀ v, c v ≤ B₀)
variable (ξ : ℝ) (hξ : 0 < ξ)

noncomputable def vector (k : ℕ)
    (P : Ω → SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k) : V → ℝ :=
  FiniteAverage.vector (fun ω => OutcomeMath.vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ k (P ω))

set_option maxHeartbeats 1000000 in
theorem spec (hcover : R ⊆ covered G D) (k : ℕ)
    (P : Ω → SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k) (β : ℝ)
    (hboundary : (∑ ω : Ω, ((BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts).card : ℝ)) ≤
      Fintype.card Ω * β) :
    PartialOptimum.Feasible G R (vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ k P) ∧
      PartialOptimum.objective c (vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ k P) ≤
        (1 + ξ) * PartialOptimum.number G R c +
          B₀ * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ) + β) := by
  classical
  let y := fun ω => OutcomeMath.vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ k (P ω)
  have hy := fun ω => OutcomeMath.spec G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ hcover k (P ω)
  refine ⟨FiniteAverage.feasible G R y (fun ω => (hy ω).1), ?_⟩
  let base := (1 + ξ) * PartialOptimum.number G R c + B₀ * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ))
  have hsum : (∑ ω : Ω, PartialOptimum.objective c (y ω)) ≤ Fintype.card Ω * (base + B₀ * β) := by
    calc
      _ ≤ ∑ ω : Ω, (base + B₀ * (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts).card) := by
        apply Finset.sum_le_sum
        intro ω _
        have h := (hy ω).2
        dsimp only [base]
        nlinarith
      _ = Fintype.card Ω * base + B₀ *
          ∑ ω : Ω, ((BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts).card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card Ω * base + B₀ * (Fintype.card Ω * β) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hboundary hB₀)
      _ = _ := by ring
  have hmean := FiniteAverage.cost_bound c y (base + B₀ * β) hsum
  calc
    _ ≤ base + B₀ * β := hmean
    _ = _ := by dsimp only [base]; ring
end Paper.MeanOutcome
