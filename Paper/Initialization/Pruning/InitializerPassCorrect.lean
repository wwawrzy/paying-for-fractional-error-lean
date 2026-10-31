import Paper.Initialization.Pruning.InitializerPassBroadcast

/-! Exact equality of every broadcast initialization pass with the proved
mathematical pass, including large suppressed lists and empty self lists. -/
namespace Paper.InitializerPassCorrect
open BroadcastModel SevenFoundation InitializerPassBroadcast
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem selection_correct {b : ℕ} (C : BitCode V b) (a h f : ℕ) (ha : 1 ≤ a) (R : Finset V) :
    (selection C a h f).run G (fun v => decide (v ∈ R)) =
      fun v => (decide (v ∈ InitializerPass.selected G a h f R), decide (v ∈ R)) := by
  change finishCore.run G ((ProgramMemory.carry (CoreSelectionBroadcast.program C f (2 * a))).run G
    (prepareCore.run G ((ProgramMemory.carry (InitializerListBroadcast.program h f)).run G
      (fun v => (decide (v ∈ R), decide (v ∈ R)))))) = _
  rw [ProgramMemory.run G (InitializerListBroadcast.program h f), InitializerListBroadcast.correct G h f R]
  change finishCore.run G ((ProgramMemory.carry (CoreSelectionBroadcast.program C f (2 * a))).run G
    (fun v => (InitializerListBroadcast.hosted G h f R v,
      (decide (v ∈ InitializerPass.emptyLists G h R), decide (v ∈ R))))) = _
  rw [ProgramMemory.run G (CoreSelectionBroadcast.program C f (2 * a))]
  rw [CoreSelectionCorrect.correct G C f (2 * a) (by omega) (InitializerListBroadcast.hosted G h f R)
    (InitializerListBroadcast.hosted_bound G h f R) (InitializerListBroadcast.hosted_local G h f R),
    InitializerListBroadcast.family_eq G h f R]
  funext v
  change (decide (v ∈ BoundedLists.cover (InitializerPass.lists G h f R) (2 * a) f) ||
    decide (v ∈ InitializerPass.emptyLists G h R), decide (v ∈ R)) = _
  simp only [InitializerPass.selected, Finset.mem_union, Bool.decide_or]

theorem covered_iff (S : Finset V) (v : V) :
    v ∈ covered G S ↔ (closed G v ∩ S).Nonempty := by
  constructor
  · intro hv
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hv
    exact ⟨u, Finset.mem_inter.mpr ⟨(closed_symm G u v).mpr hvu, hu⟩⟩
  · rintro ⟨u, hu⟩
    exact Finset.mem_biUnion.mpr ⟨u, (Finset.mem_inter.mp hu).2,
      (closed_symm G u v).mp (Finset.mem_inter.mp hu).1⟩

theorem snapshot_empty (S : Finset V) (v : V) :
    closed G v ∩ S = ∅ ↔ v ∉ covered G S := by
  rw [← Finset.not_nonempty_iff_eq_empty, ← covered_iff G S v]

theorem correct {b : ℕ} (C : BitCode V b) (a h f : ℕ) (ha : 1 ≤ a) (R : Finset V) :
    (program C a h f).run G (fun v => decide (v ∈ R)) =
      fun v => (decide (v ∈ InitializerPass.selected G a h f R),
        decide (v ∈ InitializerPass.residual G a h f R)) := by
  change finishResidual.run G ((ProgramMemory.carry FlagNeighborhood.program).run G
    (prepareResidual.run G ((selection C a h f).run G (fun v => decide (v ∈ R))))) = _
  rw [selection_correct G C a h f ha R]
  change finishResidual.run G ((ProgramMemory.carry FlagNeighborhood.program).run G
    (fun v => (decide (v ∈ InitializerPass.selected G a h f R),
      (decide (v ∈ InitializerPass.selected G a h f R), decide (v ∈ R))))) = _
  rw [ProgramMemory.run G FlagNeighborhood.program]
  funext v
  change (decide (v ∈ InitializerPass.selected G a h f R), decide (v ∈ R) &&
    decide (FlagNeighborhood.program.run G (fun u => decide (u ∈ InitializerPass.selected G a h f R)) v = ∅)) = _
  rw [FlagNeighborhood.correct G (InitializerPass.selected G a h f R) v]
  refine Prod.ext rfl ?_
  rw [← Bool.decide_and]
  apply Bool.decide_congr
  rw [snapshot_empty]
  simp only [InitializerPass.residual, Finset.mem_sdiff]
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
end Paper.InitializerPassCorrect
