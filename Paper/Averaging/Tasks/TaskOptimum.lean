import Paper.Averaging.Tasks.PhysicalTasks
import Paper.Preliminaries.InducedCover

/-! The actual fractional optimum of every physical task is bounded by
the global covering vector restricted to its useful candidates. -/
namespace Paper.TaskOptimum
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def number (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I B : Finset (Low D Q)) (c : V → ℝ) : ℝ :=
  PartialOptimum.number (G.induce (PhysicalTasks.vertices G D R L Q I : Set V))
    (InducedSubsets.lift (PhysicalTasks.vertices G D R L Q I) (OwnerTasks.demands G D R L Q I B))
    (fun v => c v.val)

theorem demand_subset (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q)) :
    OwnerTasks.demands G D R L Q I B ⊆ R := by
  intro r hr
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hr).1).1

theorem closed_service (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q))
    {r : V} (hr : r ∈ OwnerTasks.demands G D R L Q I B) :
    closed G r ⊆ OwnerTasks.service G D R L Q I B := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hr, hv⟩

set_option maxHeartbeats 1000000 in
theorem bound (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset (Low D Q))
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : PartialOptimum.Feasible G R x) :
    number G D R L Q I B c ≤ ∑ v ∈ OwnerTasks.service G D R L Q I B, c v * x v := by
  classical
  let H := PhysicalTasks.vertices G D R L Q I
  let T := OwnerTasks.demands G D R L Q I B
  let S := OwnerTasks.service G D R L Q I B
  have hT : T ⊆ H := PhysicalTasks.demands_subset G D R L Q I B
  have hS : S ⊆ H := PhysicalTasks.service_subset G D R L Q I B
  have hxT : PartialOptimum.Feasible G T x :=
    ⟨hx.1, fun r hr => hx.2 r (demand_subset G D R L Q I B hr)⟩
  have hmask := InducedCover.mask_feasible G H S T hT hS
    (fun r hr => closed_service G D R L Q I B hr) x hxT
  obtain ⟨z, hzFeas, _, hmin⟩ := PartialOptimum.exists_optimum (G.induce (H : Set V))
    (InducedSubsets.lift H T) (fun v => c v.val) (fun v => hc v.val)
  have hzmask := hmin (InducedCover.mask H S x) hmask
  -- Use attainment directly for the sInf lower bound, not an LP oracle.
  have hvalues : IsLeast (PartialOptimum.values (G.induce (H : Set V)) (InducedSubsets.lift H T)
      (fun v => c v.val)) (PartialOptimum.objective (fun v => c v.val) z) := by
    refine ⟨⟨z, hzFeas, rfl⟩, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact hmin y hy
  have hnum : number G D R L Q I B c = PartialOptimum.objective (fun v => c v.val) z := by
    simpa only [number, PhysicalTasks.graph, PartialOptimum.number, H, T] using hvalues.csInf_eq
  rw [hnum]
  exact hzmask.trans_eq (InducedCover.mask_cost H S hS c x)
end Paper.TaskOptimum
