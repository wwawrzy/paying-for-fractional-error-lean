import Paper.Averaging.Tasks.ActiveTaskQueries
import Paper.Averaging.Tasks.MaskedTaskGraph

/-! Proof-side geometric data for an actual active task. The tree
correctness certificate is derived from the literal broadcast program. -/
namespace Paper.ActiveTask
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]

structure Context (G : SimpleGraph V) where
  vertices : Finset V
  nonempty : vertices.Nonempty
  diameter : ℕ
  paths : ∀ x y : ↥(vertices : Set V), ∃ p : (G.induce (vertices : Set V)).Walk x y, p.length ≤ diameter

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem tree (K : Context G) {b : ℕ} (C : BitCode V b) :
    LeaderTreeCorrect.Spec G (fun v => decide (v ∈ K.vertices)) K.diameter
      (K.vertices.min' K.nonempty) ((LeaderTree.program C K.diameter).run G (fun v => decide (v ∈ K.vertices))) :=
  (TaskTree.induced G C K.vertices K.nonempty K.diameter K.paths).1

noncomputable def physicalMasked (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) :
    Context (MaskedTaskGraph.graph G (PhysicalTasks.vertices G D R L Q I)) where
  vertices := PhysicalTasks.vertices G D R L Q I
  nonempty := by
    obtain ⟨v⟩ := (TaskDiameter.spec G D R L Q I hI k hsize).1.nonempty
    exact ⟨v.val, v.property⟩
  diameter := 4 * k
  paths := by
    intro x y
    rw [MaskedTaskGraph.induced_eq G]
    exact (TaskDiameter.spec G D R L Q I hI k hsize).2 x y
end Paper.ActiveTask
