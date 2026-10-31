import Paper.Preliminaries.OutcomeVector
import Paper.Averaging.Tasks.TaskCostSum

/-! The actual outcome costs the sum of the three repair budgets plus
(1+ξ) times the true global partial-cover optimum. -/
namespace Paper.OutcomeCost
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem bound (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k)
    (z : OutcomeVector.Family G D R L Q) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (B₀ : ℝ) (hcost : ∀ v, c v ≤ B₀) (ξ : ℝ) (hξ : 0 ≤ ξ) :
    let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
    (∀ I ∈ P.parts, PartialOptimum.objective (fun v => c v.val) (z I) ≤
      (1 + ξ) * TaskOptimum.number G D R L Q I B c) →
    PartialOptimum.objective c (OutcomeVector.vector G D R L Q B P.parts z) ≤
      (1 + ξ) * PartialOptimum.number G R c +
        B₀ * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ) + B.card) := by
  classical
  dsimp only
  let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
  intro happrox
  have hsum : (∑ I ∈ P.parts, PartialOptimum.objective (fun v => c v.val) (z I)) ≤
      (1 + ξ) * PartialOptimum.number G R c := by
    calc
      _ ≤ ∑ I ∈ P.parts, (1 + ξ) * TaskOptimum.number G D R L Q I B c := Finset.sum_le_sum happrox
      _ = (1 + ξ) * ∑ I ∈ P.parts, TaskOptimum.number G D R L Q I B c := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (TaskCostSum.optimum_bound G D R L Q k P c hc) (by linarith)
  have h₁ := CoverVectorSum.indicator_bound (HeavyRepair.heavy G D R L) c B₀ hcost
  have h₂ := CoverVectorSum.indicator_bound (TaskDecomposition.highCenters D Q) c B₀ hcost
  have h₃ := CoverVectorSum.indicator_bound (PhysicalTasks.centers D Q B) c B₀ hcost
  have hQ : (TaskDecomposition.highCenters D Q).card = Q.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [hQ] at h₂
  rw [PhysicalTasks.centers_card] at h₃
  rw [OutcomeVector.cost]
  linarith
end Paper.OutcomeCost
