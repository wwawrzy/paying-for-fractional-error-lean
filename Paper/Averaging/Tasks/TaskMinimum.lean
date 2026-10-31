import Paper.Averaging.Tasks.TaskAggregate
import Paper.Preliminaries.MinimumPayload
import Paper.Preliminaries.MaskedMinimum

/-! Actual minimum-ID query over any locally selected subset of a physical
task. The leader/tree construction is included in the concrete program. -/
namespace Paper.TaskMinimum
open BroadcastModel MinimumPayload
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sum_selected (S : Finset V) :
    (∑ v, if v ∈ S then singleton v else (0 : Data V)).value = MaskedMinimum.minimum S := by
  have he : (∑ v, if v ∈ S then singleton v else (0 : Data V)) = ∑ v ∈ S, singleton v := by
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [he]
  unfold MaskedMinimum.minimum
  split
  · rename_i hne
    exact sum_minimum S hne
  · rename_i he
    have hs : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst S
    rfl

theorem physical_task {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (S : Finset V)
    (hS : S ⊆ PhysicalTasks.vertices G D R L Q I) :
    ∃ hne : (PhysicalTasks.vertices G D R L Q I).Nonempty,
      (((TaskAggregate.program C (code C) (4 * k)).run G
        (fun v => (decide (v ∈ PhysicalTasks.vertices G D R L Q I),
          if v ∈ S then singleton v else 0))
        ((PhysicalTasks.vertices G D R L Q I).min' hne)).2).value = MaskedMinimum.minimum S := by
  have hz : ∀ v, v ∉ PhysicalTasks.vertices G D R L Q I →
      (if v ∈ S then singleton v else (0 : Data V)) = 0 := by
    intro v hv
    have hs : v ∉ S := fun hs => hv (hS hs)
    simp [hs]
  obtain ⟨hne, hres⟩ := TaskAggregate.physical_task G C (code C) D R L Q I hI k hsize
    (fun v => if v ∈ S then singleton v else 0) hz
  exact ⟨hne, (congrArg Data.value hres).trans (sum_selected S)⟩
end Paper.TaskMinimum
