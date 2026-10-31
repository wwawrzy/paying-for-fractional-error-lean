import Paper.Partitions.Local.FinitePartitionLaw
import Paper.Averaging.Tasks.MeanOutcome

/-! The true finite partition law supplies all inputs to the actual mean
outcome. This constructs a feasible vector with the compiler cost bound. -/
namespace Paper.CompilerFromLaw
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem spec (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (Q : Finset D)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hcost : ∀ v, c v ≤ B₀)
    (ξ : ℝ) (hξ : 0 < ξ) (η : ℝ)
    (law : FinitePartitionLaw.Data (OwnerTasks.graph G D R L Q) η) :
    ∃ x : V → ℝ, PartialOptimum.Feasible G R x ∧
      PartialOptimum.objective c x ≤ (1 + ξ) * PartialOptimum.number G R c +
        B₀ * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ) + 2 * η * Fintype.card (Low D Q)) := by
  classical
  letI : Fintype law.Ω := law.fintype
  letI : Nonempty law.Ω := law.nonempty
  refine ⟨MeanOutcome.vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ law.k law.partition, ?_⟩
  exact MeanOutcome.spec G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ hcover law.k law.partition
    (2 * η * Fintype.card (Low D Q)) law.boundary
end Paper.CompilerFromLaw
