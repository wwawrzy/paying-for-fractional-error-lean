import Paper.Preliminaries.OutcomeCost
import Paper.Averaging.Tasks.FiniteAverage

/-! Feasibility/cost averaging for arbitrary actual task vectors. No
mathematical task-solution selector is hardcoded in this aggregation law. -/
namespace Paper.GenericOutcomeMean
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
open scoped BigOperators
variable {V Ω : Type} [Fintype V] [LinearOrder V] [Fintype Ω] [Nonempty Ω]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def vector (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : Ω → SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k)
    (z : Ω → OutcomeVector.Family G D R L Q) : V → ℝ :=
  FiniteAverage.vector (fun ω => OutcomeVector.vector G D R L Q
    (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts) (P ω).parts (z ω))

set_option maxHeartbeats 1000000 in
theorem spec (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : Ω → SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k)
    (z : Ω → OutcomeVector.Family G D R L Q) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (B : ℝ) (hB : 0 ≤ B) (hcost : ∀ v, c v ≤ B) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hfeasible : ∀ ω I, I ∈ (P ω).parts → PartialOptimum.Feasible
      (G.induce (PhysicalTasks.vertices G D R L Q I : Set V))
      (InducedSubsets.lift (PhysicalTasks.vertices G D R L Q I) (OwnerTasks.demands G D R L Q I
        (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts))) (z ω I))
    (happrox : ∀ ω I, I ∈ (P ω).parts → PartialOptimum.objective (fun v => c v.val) (z ω I) ≤
      (1 + ξ) * TaskOptimum.number G D R L Q I
        (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts) c)
    (β : ℝ) (hboundary : (∑ ω : Ω,
      ((BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts).card : ℝ)) ≤
      Fintype.card Ω * β) :
    PartialOptimum.Feasible G R (vector G D R L Q k P z) ∧
      PartialOptimum.objective c (vector G D R L Q k P z) ≤
        (1 + ξ) * PartialOptimum.number G R c +
          B * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ) + β) := by
  classical
  let y := fun ω => OutcomeVector.vector G D R L Q
    (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts) (P ω).parts (z ω)
  have hyf : ∀ ω, PartialOptimum.Feasible G R (y ω) := fun ω =>
    OutcomeVector.feasible G D R hcover L Q _ k (P ω) (z ω) (hfeasible ω)
  have hyc : ∀ ω, PartialOptimum.objective c (y ω) ≤
      (1 + ξ) * PartialOptimum.number G R c + B * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ) +
        (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts).card) := fun ω =>
    OutcomeCost.bound G D R L Q k (P ω) (z ω) c hc B hcost ξ hξ (happrox ω)
  refine ⟨FiniteAverage.feasible G R y hyf, ?_⟩
  let base := (1 + ξ) * PartialOptimum.number G R c + B * ((HeavyRepair.heavy G D R L).card + (Q.card : ℝ))
  have hsum : (∑ ω : Ω, PartialOptimum.objective c (y ω)) ≤ Fintype.card Ω * (base + B * β) := by
    calc
      _ ≤ ∑ ω : Ω, (base + B * (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts).card) := by
        apply Finset.sum_le_sum
        intro ω _
        have h := hyc ω
        dsimp only [base]
        nlinarith
      _ = Fintype.card Ω * base + B *
          ∑ ω : Ω, ((BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (P ω).parts).card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card Ω * base + B * (Fintype.card Ω * β) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hboundary hB)
      _ = _ := by ring
  exact (FiniteAverage.cost_bound c y (base + B * β) hsum).trans_eq (by dsimp only [base]; ring)

end Paper.GenericOutcomeMean
