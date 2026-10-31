import Paper.Preliminaries.InducedExtension
import Paper.Averaging.Tasks.TaskDecomposition
import Paper.Preliminaries.CoverVectorSum

/-! The actual outcome vector: three repair indicators plus the zero
extensions of all physical task vectors. Every original demand is covered. -/
namespace Paper.OutcomeVector
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerTasks
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Family (D R : Finset V) (L : ℕ) (Q : Finset D) :=
  (I : Finset (Low D Q)) → ↥(PhysicalTasks.vertices G D R L Q I : Set V) → ℝ

noncomputable def tasks (D R : Finset V) (L : ℕ) (Q : Finset D)
    (F : Finset (Finset (Low D Q))) (z : Family G D R L Q) : V → ℝ :=
  CoverVectorSum.vector F (fun I => InducedExtension.extend (PhysicalTasks.vertices G D R L Q I) (z I))

noncomputable def vector (D R : Finset V) (L : ℕ) (Q : Finset D) (B : Finset (Low D Q))
    (F : Finset (Finset (Low D Q))) (z : Family G D R L Q) (v : V) : ℝ :=
  indicator (HeavyRepair.heavy G D R L) v + indicator (TaskDecomposition.highCenters D Q) v +
    indicator (PhysicalTasks.centers D Q B) v + tasks G D R L Q F z v

theorem nonneg (D R : Finset V) (L : ℕ) (Q : Finset D) (B : Finset (Low D Q))
    (F : Finset (Finset (Low D Q))) (z : Family G D R L Q)
    (hz : ∀ I ∈ F, ∀ v, 0 ≤ z I v) : ∀ v, 0 ≤ vector G D R L Q B F z v := by
  have ht := CoverVectorSum.nonneg F
    (fun I => InducedExtension.extend (PhysicalTasks.vertices G D R L Q I) (z I))
    (fun I hI => InducedExtension.nonneg _ _ (hz I hI))
  intro v
  exact add_nonneg (add_nonneg (add_nonneg (CoverVectorSum.indicator_nonneg _ _)
    (CoverVectorSum.indicator_nonneg _ _)) (CoverVectorSum.indicator_nonneg _ _)) (ht v)

theorem repair_le (D R : Finset V) (L : ℕ) (Q : Finset D) (B : Finset (Low D Q))
    (F : Finset (Finset (Low D Q))) (z : Family G D R L Q)
    (hz : ∀ I ∈ F, ∀ v, 0 ≤ z I v) (v : V) :
    indicator (HeavyRepair.heavy G D R L) v ≤ vector G D R L Q B F z v ∧
      indicator (TaskDecomposition.highCenters D Q) v ≤ vector G D R L Q B F z v ∧
      indicator (PhysicalTasks.centers D Q B) v ≤ vector G D R L Q B F z v := by
  have h₁ := CoverVectorSum.indicator_nonneg (HeavyRepair.heavy G D R L) v
  have h₂ := CoverVectorSum.indicator_nonneg (TaskDecomposition.highCenters D Q) v
  have h₃ := CoverVectorSum.indicator_nonneg (PhysicalTasks.centers D Q B) v
  have ht := CoverVectorSum.nonneg F
    (fun I => InducedExtension.extend (PhysicalTasks.vertices G D R L Q I) (z I))
    (fun I hI => InducedExtension.nonneg _ _ (hz I hI)) v
  change 0 ≤ tasks G D R L Q F z v at ht
  dsimp only [vector]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem task_le (D R : Finset V) (L : ℕ) (Q : Finset D) (B : Finset (Low D Q))
    (F : Finset (Finset (Low D Q))) (z : Family G D R L Q)
    (hz : ∀ I ∈ F, ∀ v, 0 ≤ z I v) (I : Finset (Low D Q)) (hI : I ∈ F) (v : V) :
    InducedExtension.extend (PhysicalTasks.vertices G D R L Q I) (z I) v ≤ vector G D R L Q B F z v := by
  have ht := CoverVectorSum.single_le F
    (fun I => InducedExtension.extend (PhysicalTasks.vertices G D R L Q I) (z I))
    (fun I hI => InducedExtension.nonneg _ _ (hz I hI)) hI v
  change _ ≤ tasks G D R L Q F z v at ht
  have h₁ := CoverVectorSum.indicator_nonneg (HeavyRepair.heavy G D R L) v
  have h₂ := CoverVectorSum.indicator_nonneg (TaskDecomposition.highCenters D Q) v
  have h₃ := CoverVectorSum.indicator_nonneg (PhysicalTasks.centers D Q B) v
  dsimp only [vector]
  linarith

set_option maxHeartbeats 1000000 in
theorem feasible (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (Q : Finset D)
    (B : Finset (Low D Q)) (k : ℕ) (P : SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k)
    (z : Family G D R L Q)
    (hz : ∀ I ∈ P.parts, PartialOptimum.Feasible (G.induce (PhysicalTasks.vertices G D R L Q I : Set V))
      (InducedSubsets.lift (PhysicalTasks.vertices G D R L Q I) (OwnerTasks.demands G D R L Q I B)) (z I)) :
    PartialOptimum.Feasible G R (vector G D R L Q B P.parts z) := by
  classical
  have hzn : ∀ I ∈ P.parts, ∀ v, 0 ≤ z I v := fun I hI => (hz I hI).1
  refine ⟨nonneg G D R L Q B P.parts z hzn, ?_⟩
  intro r hr
  have hmono (x : V → ℝ) (hle : ∀ v, x v ≤ vector G D R L Q B P.parts z v)
      (hx : 1 ≤ ∑ v ∈ closed G r, x v) : 1 ≤ ∑ v ∈ closed G r, vector G D R L Q B P.parts z v :=
    hx.trans (Finset.sum_le_sum (fun v _ => hle v))
  rcases TaskDecomposition.covers G D R hcover L Q B k P hr with hP | hQ | hB | ⟨I, hI, hrI⟩
  · exact hmono _ (fun v => (repair_le G D R L Q B P.parts z hzn v).1) (CoverVectorSum.indicator_covers G _ hP)
  · exact hmono _ (fun v => (repair_le G D R L Q B P.parts z hzn v).2.1) (CoverVectorSum.indicator_covers G _ hQ)
  · exact hmono _ (fun v => (repair_le G D R L Q B P.parts z hzn v).2.2) (CoverVectorSum.indicator_covers G _ hB)
  · have hext := InducedExtension.feasible G (PhysicalTasks.vertices G D R L Q I)
      (OwnerTasks.demands G D R L Q I B) (PhysicalTasks.demands_subset G D R L Q I B)
      (fun r hr _ hv => PhysicalTasks.candidates_complete G D R L Q I B hr hv) (z I) (hz I hI)
    exact hmono _ (fun v => task_le G D R L Q B P.parts z hzn I hI v) (hext.2 r hrI)

theorem cost (D R : Finset V) (L : ℕ) (Q : Finset D) (B : Finset (Low D Q))
    (F : Finset (Finset (Low D Q))) (z : Family G D R L Q) (c : V → ℝ) :
    PartialOptimum.objective c (vector G D R L Q B F z) =
      PartialOptimum.objective c (indicator (HeavyRepair.heavy G D R L)) +
      PartialOptimum.objective c (indicator (TaskDecomposition.highCenters D Q)) +
      PartialOptimum.objective c (indicator (PhysicalTasks.centers D Q B)) +
      ∑ I ∈ F, PartialOptimum.objective (fun v => c v.val) (z I) := by
  unfold vector
  rw [CoverVectorSum.cost_add, CoverVectorSum.cost_add, CoverVectorSum.cost_add]
  congr 1
  unfold tasks
  rw [CoverVectorSum.cost]
  exact Finset.sum_congr rfl (fun I _ => InducedExtension.cost _ _ c)
end Paper.OutcomeVector
