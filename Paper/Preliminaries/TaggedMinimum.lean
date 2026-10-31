import Paper.Averaging.Tasks.TaskQueries

/-! Actual task minimum queries for locally attached ordered tags, such as
bounded cost followed by identifier. The tag decoder is public and graph
independent; each vertex supplies only its own tag. -/
namespace Paper.TaggedMinimum
open BroadcastModel MinimumPayload
variable {V U : Type} [LinearOrder V] [LinearOrder U]

def program {b c : ℕ} (C : BitCode V b) (F : BitCode U c) (D : ℕ) :=
  TaskAllReduce.program C (MinimumPayload.code F) D

variable [Fintype V]

theorem sum_selected (S : Finset V) (tag : V → U) (hinj : Function.Injective tag) :
    (∑ v, if v ∈ S then singleton (tag v) else (0 : Data U)).value =
      MaskedMinimum.minimum (S.image tag) := by
  have he : (∑ v, if v ∈ S then singleton (tag v) else (0 : Data U)) =
      ∑ u ∈ S.image tag, singleton u := by
    rw [← Finset.sum_filter]
    have hs : Finset.univ.filter (fun v => v ∈ S) = S := by ext v; simp
    rw [hs, Finset.sum_image (fun _ _ _ _ h => hinj h)]
  rw [he]
  unfold MaskedMinimum.minimum
  split
  · exact sum_minimum _ ‹(S.image tag).Nonempty›
  · have hs : S.image tag = ∅ := Finset.not_nonempty_iff_eq_empty.mp ‹¬(S.image tag).Nonempty›
    rw [hs]
    rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem physical_task {b c : ℕ} (C : BitCode V b) (F : BitCode U c)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (S : Finset V)
    (hS : S ⊆ PhysicalTasks.vertices G D R L Q I) (tag : V → U) (hinj : Function.Injective tag) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      (((program C F (4 * k)).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I),
          if u ∈ S then singleton (tag u) else 0)) v).2.map
            Data.value) = some (MaskedMinimum.minimum (S.image tag)) := by
  have hz : ∀ u, u ∉ PhysicalTasks.vertices G D R L Q I →
      (if u ∈ S then singleton (tag u) else (0 : Data U)) = 0 := by
    intro u hu
    have hs : u ∉ S := fun hs => hu (hS hs)
    simp [hs]
  intro v hv
  have hres := TaskAllReduce.physical_task G C (MinimumPayload.code F)
    D R L Q I hI k hsize (fun u => if u ∈ S then singleton (tag u) else 0) hz v hv
  change ((TaskAllReduce.program C (MinimumPayload.code F) (4 * k)).run G _ v).2.map _ = _
  rw [hres, Option.map_some, sum_selected S tag hinj]
  rfl

theorem least (S : Finset V) (tag : V → U) {u : U}
    (h : MaskedMinimum.minimum (S.image tag) = some u) :
    (∃ v ∈ S, tag v = u) ∧ ∀ v ∈ S, u ≤ tag v := by
  refine ⟨Finset.mem_image.mp (MaskedMinimum.minimum_mem h), ?_⟩
  intro v hv
  have hv' : tag v ∈ S.image tag := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  obtain ⟨m, hm, hle⟩ := MaskedMinimum.minimum_le hv'
  have he : m = u := Option.some.inj (hm.symm.trans h)
  exact he ▸ hle
end Paper.TaggedMinimum
