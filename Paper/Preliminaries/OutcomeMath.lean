import Paper.Preliminaries.OutcomeCost
import Paper.Averaging.Tasks.TaskSolutions

/-! Construct the actual outcome from the actual bounded-search task
solutions. Feasibility and cost require no local-solver oracle. -/
namespace Paper.OutcomeMath
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D R : Finset V) (L : ℕ) (Q : Finset D)
variable (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
variable (c : V → ℝ) (hc : ∀ v, 1 ≤ c v) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hcost : ∀ v, c v ≤ B₀)
variable (ξ : ℝ) (hξ : 0 < ξ)

noncomputable def family (B : Finset (Low D Q)) : OutcomeVector.Family G D R L Q :=
  fun I => TaskSolutions.vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ I B

noncomputable def vector (k : ℕ) (P : SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k) : V → ℝ :=
  let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
  OutcomeVector.vector G D R L Q B P.parts (family G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ B)

set_option maxHeartbeats 1000000 in
theorem spec (hcover : R ⊆ covered G D) (k : ℕ)
    (P : SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k) :
    let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
    let y := vector G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ k P
    PartialOptimum.Feasible G R y ∧ PartialOptimum.objective c y ≤
      (1 + ξ) * PartialOptimum.number G R c +
        B₀ * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ) + B.card) := by
  classical
  dsimp only
  let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
  let z := family G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ B
  have hz := fun I => TaskSolutions.spec G D R L Q a ha hden c hc B₀ hB₀ hcost ξ hξ I B
  constructor
  · exact OutcomeVector.feasible G D R hcover L Q B k P z (fun I _ => (hz I).1)
  · exact OutcomeCost.bound G D R L Q k P z c (fun v => zero_le_one.trans (hc v)) B₀ hcost ξ hξ.le
      (fun I _ => (hz I).2.1)
end Paper.OutcomeMath
