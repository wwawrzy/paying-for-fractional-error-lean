import Paper.Averaging.Tasks.TaskOptimum

/-! Sum the true physical task optima using the proved disjoint useful
candidate sets, and compare with the actual global partial-cover optimum. -/
namespace Paper.TaskCostSum
attribute [local instance] Classical.propDecidable Classical.decEq
open OwnerTasks
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem vector_bound (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k)
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : PartialOptimum.Feasible G R x) :
    let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
    (∑ I ∈ P.parts, TaskOptimum.number G D R L Q I B c) ≤ PartialOptimum.objective c x := by
  classical
  dsimp only
  let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
  let S := fun I => OwnerTasks.service G D R L Q I B
  have hd : (P.parts : Set (Finset (Low D Q))).PairwiseDisjoint S :=
    fun I hI J hJ hne => OwnerTasks.service_disjoint G D R L Q k P I J hI hJ hne
  calc
    _ ≤ ∑ I ∈ P.parts, ∑ v ∈ S I, c v * x v :=
      Finset.sum_le_sum (fun I _ => TaskOptimum.bound G D R L Q I B c x hc hx)
    _ = ∑ v ∈ P.parts.biUnion S, c v * x v := (Finset.sum_biUnion hd).symm
    _ ≤ ∑ v, c v * x v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun v _ _ => mul_nonneg (hc v) (hx.1 v))

theorem optimum_bound (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    let B := BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ P.parts
    (∑ I ∈ P.parts, TaskOptimum.number G D R L Q I B c) ≤ PartialOptimum.number G R c := by
  obtain ⟨x, hx, he⟩ := PartialOptimum.exists_optimum_eq_number G R c hc
  have hb := vector_bound G D R L Q k P c x hc hx
  rwa [he] at hb
end Paper.TaskCostSum
