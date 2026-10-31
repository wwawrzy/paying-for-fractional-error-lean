import Paper.Owners.Construction.OwnerMetadataBroadcast
import Paper.Initialization.Pruning.InitializerPassCorrect

/-! Each of the four actual broadcasts computes the physical owner/repair
objects already used by the mathematical compiler. No metadata oracle. -/
namespace Paper.OwnerMetadataCorrect
open BroadcastModel SevenFoundation OwnerMetadataBroadcast
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem root_correct (D R : Finset V) :
    root.run G (fun v => (decide (v ∈ D), decide (v ∈ R))) =
      fun v => (⟨decide (v ∈ D), decide (v ∈ R), OwnerSupport.owner G D v, ∅, false, false, ∅⟩ : State V) := by
  change (Program.local fun _ _ s => (⟨s.2.1, s.2.2, s.1, ∅, false, false, ∅⟩ : State V)).run G
    ((ProgramMemory.carry OwnerRootBroadcast.program).run G
      (fun v => (decide (v ∈ D), (decide (v ∈ D), decide (v ∈ R))))) = _
  rw [ProgramMemory.run G OwnerRootBroadcast.program, OwnerRootBroadcast.correct G D]
  rfl

theorem augmented_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L : ℕ) (s : V → State V)
    (ho : ∀ v, (s v).owner = OwnerSupport.owner G D v)
    (ha : ∀ v, ((s v).center || (s v).demand) = decide (v ∈ R ∪ D)) :
    (augmented C L).run G s = fun v => {s v with augmented := OwnerSupport.support G D R v, heavy := decide (L < (OwnerSupport.support G D R v).card)} := by
  have hin : (fun v => ((s v).owner, (s v).center || (s v).demand)) =
      fun v => (OwnerSupport.owner G D v, decide (v ∈ R ∪ D)) := by
    funext v
    rw [ho v, ha v]
  change (Program.local fun _ _ st => {st.2 with augmented := st.1, heavy := decide (L < st.1.card)}).run G
    ((ProgramMemory.carry (LabelNeighborhood.program C)).run G
      (fun v => (((s v).owner, (s v).center || (s v).demand), s v))) = _
  rw [ProgramMemory.run G (LabelNeighborhood.program C)]
  dsimp only
  rw [hin]
  have hs : (LabelNeighborhood.program C).run G
      (fun v => (OwnerSupport.owner G D v, decide (v ∈ R ∪ D))) = OwnerSupport.support G D R := by
    funext v
    rw [LabelNeighborhood.correct G C]
    unfold OwnerSupport.support
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst]
  rw [hs]
  rfl

theorem repair_correct (D R : Finset V) (L : ℕ) (s : V → State V)
    (hh : ∀ v, (s v).heavy = decide (v ∈ HeavyRepair.heavy G D R L))
    (hr : ∀ v, (s v).demand = decide (v ∈ R)) :
    repair.run G s = fun v => {s v with remaining := decide (v ∈ OwnerInteraction.remaining G D R L)} := by
  have hin : (fun v => (s v).heavy) = fun v => decide (v ∈ HeavyRepair.heavy G D R L) := funext hh
  change (Program.local fun _ _ st => {st.2 with remaining := st.2.demand && decide (st.1 = ∅)}).run G
    ((ProgramMemory.carry FlagNeighborhood.program).run G (fun v => ((s v).heavy, s v))) = _
  rw [ProgramMemory.run G FlagNeighborhood.program]
  dsimp only
  rw [hin]
  funext v
  change {s v with remaining := (s v).demand && decide (FlagNeighborhood.program.run G (fun u => decide (u ∈ HeavyRepair.heavy G D R L)) v = ∅)} = _
  rw [FlagNeighborhood.correct G (HeavyRepair.heavy G D R L) v]
  have hbool : ((s v).demand && decide (closed G v ∩ HeavyRepair.heavy G D R L = ∅)) =
      decide (v ∈ OwnerInteraction.remaining G D R L) := by
    rw [hr v, ← Bool.decide_and]
    apply Bool.decide_congr
    rw [InitializerPassCorrect.snapshot_empty]
    simp only [OwnerInteraction.remaining, Finset.mem_sdiff]
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst]
  exact congrArg (fun flag => {s v with remaining := flag}) hbool

theorem actual_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L : ℕ) (s : V → State V)
    (ho : ∀ v, (s v).owner = OwnerSupport.owner G D v)
    (hr : ∀ v, (s v).remaining = decide (v ∈ OwnerInteraction.remaining G D R L)) :
    (actual C).run G s = fun v => {s v with support := OwnerInteraction.actualSupport G D R L v} := by
  have hin : (fun v => ((s v).owner, (s v).remaining)) = fun v =>
      (OwnerSupport.owner G D v, decide (v ∈ OwnerInteraction.remaining G D R L)) := by
    funext v
    rw [ho v, hr v]
  change (Program.local fun _ _ st => {st.2 with support := st.1}).run G
    ((ProgramMemory.carry (LabelNeighborhood.program C)).run G (fun v => (((s v).owner, (s v).remaining), s v))) = _
  rw [ProgramMemory.run G (LabelNeighborhood.program C)]
  dsimp only
  rw [hin]
  have hs : (LabelNeighborhood.program C).run G
      (fun v => (OwnerSupport.owner G D v, decide (v ∈ OwnerInteraction.remaining G D R L))) =
        OwnerInteraction.actualSupport G D R L := by
    funext v
    rw [LabelNeighborhood.correct G C]
    unfold OwnerInteraction.actualSupport
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst]
  rw [hs]
  rfl

noncomputable def expected (D R : Finset V) (L : ℕ) (v : V) : State V :=
  ⟨decide (v ∈ D), decide (v ∈ R), OwnerSupport.owner G D v, OwnerSupport.support G D R v,
    decide (L < (OwnerSupport.support G D R v).card), decide (v ∈ OwnerInteraction.remaining G D R L),
    OwnerInteraction.actualSupport G D R L v⟩

theorem correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L : ℕ) :
    (program C L).run G (fun v => (decide (v ∈ D), decide (v ∈ R))) = expected G D R L := by
  change (actual C).run G (repair.run G ((augmented C L).run G
    (root.run G (fun v => (decide (v ∈ D), decide (v ∈ R)))))) = _
  rw [root_correct G D R]
  rw [augmented_correct G C D R L _ (fun _ => rfl) (by
    intro v
    simp only [Finset.mem_union, Bool.decide_or, Bool.or_comm])]
  rw [repair_correct G D R L _ (by
    intro v
    simp only [HeavyRepair.heavy, Finset.mem_filter, Finset.mem_univ, true_and]) (fun _ => rfl)]
  rw [actual_correct G C D R L _ (fun _ => rfl) (fun _ => rfl)]
  rfl

theorem support_bound {b : ℕ} (C : BitCode V b) (D R : Finset V) (L : ℕ) (v : V) :
    (((program C L).run G (fun u => (decide (u ∈ D), decide (u ∈ R))) v).support).card ≤ L := by
  rw [correct]
  exact OwnerInteraction.support_bound G D R L v
end Paper.OwnerMetadataCorrect
