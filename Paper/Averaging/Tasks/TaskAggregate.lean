import Paper.Communication.ProgramMemory
import Paper.Preliminaries.TreeAggregate
import Paper.Averaging.Tasks.TaskTree

/-! Actual end-to-end task aggregation: elect a leader, build the tree,
preserve each vertex's private payload, and aggregate along physical edges. -/
namespace Paper.TaskAggregate
open BroadcastModel TreeAggregateRound
variable {V A : Type} [LinearOrder V] [AddCommMonoid A]

def program {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ) :
    Program V (Bool × A) (State V A D) :=
  .seq (ProgramMemory.carry (LeaderTree.program C D)) (TreeAggregate.program C F D D)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_eq {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ)
    (active : V → Bool) (weights : V → A) :
    (program C F D).run G (fun v => (active v, weights v)) =
      (TreeAggregate.program C F D D).run G
        (fun v => ((LeaderTree.program C D).run G active v, weights v)) := by
  change (TreeAggregate.program C F D D).run G
    ((ProgramMemory.carry (LeaderTree.program C D)).run G (fun v => (active v, weights v))) = _
  rw [ProgramMemory.run]

theorem correct {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ)
    (active : V → Bool) (root : V)
    (h : LeaderTreeCorrect.Spec G active D root ((LeaderTree.program C D).run G active))
    (weights : V → A) (hz : ∀ v, active v = false → weights v = 0) :
    ((program C F D).run G (fun v => (active v, weights v)) root).2 = ∑ v, weights v ∧
      ∀ v, v ≠ root → ((program C F D).run G (fun v => (active v, weights v)) v).2 = 0 := by
  rw [run_eq]
  exact (TreeAggregate.correct G C F h weights hz).2

theorem physical_task {b c : ℕ} (C : BitCode V b) (F : BitCode A c)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (weights : V → A)
    (hz : ∀ v, v ∉ PhysicalTasks.vertices G D R L Q I → weights v = 0) :
    ∃ hne : (PhysicalTasks.vertices G D R L Q I).Nonempty,
      ((program C F (4 * k)).run G
        (fun v => (decide (v ∈ PhysicalTasks.vertices G D R L Q I), weights v))
        ((PhysicalTasks.vertices G D R L Q I).min' hne)).2 = ∑ v, weights v := by
  obtain ⟨hne, hs, _, _⟩ := TaskTree.spec G C D R L Q I hI k hsize
  refine ⟨hne, (correct G C F (4 * k) _ _ hs weights ?_).1⟩
  intro v hv
  exact hz v (by simpa using hv)

theorem rounds {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ) :
    (program C F D).rounds = 3 * D + 1 := by
  simp only [program, Program.rounds, ProgramMemory.rounds, LeaderTree.rounds,
    TreeAggregate.rounds]
  omega

theorem maxBits {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ) :
    (program C F D).maxBits ≤ max (b + c + 1) (D + 2) := by
  change max (ProgramMemory.carry (LeaderTree.program C D)).maxBits
    (TreeAggregate.program C F D D).maxBits ≤ _
  rw [ProgramMemory.maxBits]
  apply max_le
  · apply (LeaderTree.maxBits C D).trans
    exact max_le (by omega) (le_max_right _ _)
  · exact (TreeAggregate.maxBits C F D D).trans (le_max_left _ _)
end Paper.TaskAggregate
