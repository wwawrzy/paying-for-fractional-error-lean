import Paper.Initialization.Lists.MarkedBroadcast
import Paper.Initialization.Lists.InitializerListBroadcast
import Paper.Initialization.Pruning.InitializerPassCorrect
import Paper.Initialization.Pruning.SimpleInitializer
import Paper.Preliminaries.ListPacket

/-! Physical implementation of the marked-list initializer and its repeated
residual passes. -/
namespace Paper.SimpleBroadcast
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def prepareLists : Program V ((Finset V × Bool) × Bool) (Finset V × (Bool × Bool)) :=
  .local fun _ _ s => (s.1.1, (s.1.2, s.2))

def finishSelection : Program V (Bool × (Bool × Bool)) (Bool × Bool) :=
  .local fun _ _ s => (s.1 || s.2.1, s.2.2)

def selection {b : ℕ} (C : BitCode V b) (h q : ℕ) :
    Program V Bool (Bool × Bool) :=
  .seq (.local fun _ _ s => (s, s))
    (.seq (ProgramMemory.carry (InitializerListBroadcast.program h h))
      (.seq prepareLists
        (.seq (ProgramMemory.carry (MarkedBroadcast.program C h q)) finishSelection)))

def prepareResidual : Program V (Bool × Bool) (Bool × (Bool × Bool)) :=
  .local fun _ _ s => (s.1, s)

def finishResidual : Program V (Finset V × (Bool × Bool)) (Bool × Bool) :=
  .local fun _ _ s => (s.2.1, s.2.2 && decide (s.1 = ∅))

def pass {b : ℕ} (C : BitCode V b) (h q : ℕ) :
    Program V Bool (Bool × Bool) :=
  .seq (selection C h q) (.seq prepareResidual
    (.seq (ProgramMemory.carry FlagNeighborhood.program) finishResidual))

def step {b : ℕ} (C : BitCode V b) (h q : ℕ) :
    Program V (Bool × Bool) (Bool × Bool) :=
  .seq (ProgramMemory.carry (pass C h q))
    (.local fun _ _ s => (s.1.2, s.2 || s.1.1))

def program {b : ℕ} (C : BitCode V b) (h q T : ℕ) : Program V Bool Bool :=
  .seq (.local fun _ _ s => (s, false))
    (.seq ((step C h q).iterate T) (.local fun _ _ s => s.2 || s.1))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem selection_correct {b : ℕ} (C : BitCode V b) (h q : ℕ) (R : Finset V) :
    (selection C h q).run G (fun v => decide (v ∈ R)) = fun v =>
      (decide (v ∈ SimpleInitializer.selected G h q R), decide (v ∈ R)) := by
  change finishSelection.run G
    ((ProgramMemory.carry (MarkedBroadcast.program C h q)).run G
      (prepareLists.run G
        ((ProgramMemory.carry (InitializerListBroadcast.program h h)).run G
          (fun v => (decide (v ∈ R), decide (v ∈ R)))))) = _
  rw [ProgramMemory.run G (InitializerListBroadcast.program h h)]
  rw [InitializerListBroadcast.correct G h h R]
  change finishSelection.run G
    ((ProgramMemory.carry (MarkedBroadcast.program C h q)).run G
      (fun v => (InitializerListBroadcast.hosted G h h R v,
        (decide (v ∈ InitializerPass.emptyLists G h R), decide (v ∈ R))))) = _
  rw [ProgramMemory.run G (MarkedBroadcast.program C h q)]
  rw [MarkedBroadcast.correct G C h q (InitializerListBroadcast.hosted G h h R)
    (InitializerListBroadcast.hosted_bound G h h R)
    (InitializerListBroadcast.hosted_local G h h R)]
  rw [InitializerListBroadcast.family_eq G h h R]
  funext v
  change (decide (v ∈ MarkedLists.output (InitializerPass.lists G h h R) q h) ||
    decide (v ∈ InitializerPass.emptyLists G h R), decide (v ∈ R)) = _
  simp only [SimpleInitializer.selected, Finset.mem_union, Bool.decide_or]

theorem pass_correct {b : ℕ} (C : BitCode V b) (h q : ℕ) (R : Finset V) :
    (pass C h q).run G (fun v => decide (v ∈ R)) = fun v =>
      (decide (v ∈ SimpleInitializer.selected G h q R),
       decide (v ∈ SimpleInitializer.residual G h q R)) := by
  change finishResidual.run G
    ((ProgramMemory.carry FlagNeighborhood.program).run G
      (prepareResidual.run G ((selection C h q).run G (fun v => decide (v ∈ R))))) = _
  rw [selection_correct G C h q R]
  rw [ProgramMemory.run G FlagNeighborhood.program]
  funext v
  change (decide (v ∈ SimpleInitializer.selected G h q R),
    decide (v ∈ R) && decide
      (FlagNeighborhood.program.run G
        (fun u => decide (u ∈ SimpleInitializer.selected G h q R)) v = ∅)) = _
  rw [FlagNeighborhood.correct G (SimpleInitializer.selected G h q R) v]
  refine Prod.ext rfl ?_
  rw [← Bool.decide_and]
  apply Bool.decide_congr
  rw [InitializerPassCorrect.snapshot_empty]
  simp only [SimpleInitializer.residual, Finset.mem_sdiff]
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]

theorem step_correct {b : ℕ} (C : BitCode V b) (h q : ℕ) (R P : Finset V) :
    (step C h q).run G (fun v => (decide (v ∈ R), decide (v ∈ P))) = fun v =>
      (decide (v ∈ SimpleInitializer.residual G h q R),
       decide (v ∈ P ∪ SimpleInitializer.selected G h q R)) := by
  change (fun v => (((ProgramMemory.carry (pass C h q)).run G
      (fun u => (decide (u ∈ R), decide (u ∈ P))) v).1.2,
    ((ProgramMemory.carry (pass C h q)).run G
      (fun u => (decide (u ∈ R), decide (u ∈ P))) v).2 ||
    ((ProgramMemory.carry (pass C h q)).run G
      (fun u => (decide (u ∈ R), decide (u ∈ P))) v).1.1)) = _
  rw [ProgramMemory.run G (pass C h q), pass_correct G C h q R]
  funext v
  simp only [Finset.mem_union, Bool.decide_or]

theorem past_succ (h q : ℕ) (R : Finset V) (n : ℕ) :
    (Finset.range (n + 1)).biUnion (SimpleInitializer.selection G h q R) =
      (Finset.range n).biUnion (SimpleInitializer.selection G h q R) ∪
        SimpleInitializer.selection G h q R n := by
  simp only [Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

theorem iterate_correct {b : ℕ} (C : BitCode V b) (h q : ℕ) (R : Finset V) (T : ℕ) :
    ((step C h q).iterate T).run G (fun v => (decide (v ∈ R), false)) = fun v =>
      (decide (v ∈ SimpleInitializer.state G h q R T),
       decide (v ∈ (Finset.range T).biUnion (SimpleInitializer.selection G h q R))) := by
  induction T with
  | zero =>
      funext v
      simp only [Program.iterate, Program.run, SimpleInitializer.state,
        Finset.range_zero, Finset.biUnion_empty, Finset.notMem_empty, decide_false]
      exact Prod.ext (Bool.decide_congr Iff.rfl) rfl
  | succ T ih =>
      change (step C h q).run G
        (((step C h q).iterate T).run G (fun v => (decide (v ∈ R), false))) = _
      rw [ih]
      rw [step_correct G C h q (SimpleInitializer.state G h q R T)
        ((Finset.range T).biUnion (SimpleInitializer.selection G h q R))]
      funext v
      apply Prod.ext
      · apply Bool.decide_congr
        simp only [SimpleInitializer.state]
      · apply Bool.decide_congr
        rw [past_succ G h q R T]
        rw [SimpleInitializer.selection]

theorem correct {b : ℕ} (C : BitCode V b) (h q T : ℕ) (R : Finset V) :
    (program C h q T).run G (fun v => decide (v ∈ R)) = fun v =>
      decide (v ∈ (Finset.range T).biUnion (SimpleInitializer.selection G h q R) ∪
        SimpleInitializer.state G h q R T) := by
  change (fun v => (((step C h q).iterate T).run G
      (fun u => (decide (u ∈ R), false)) v).2 ||
    (((step C h q).iterate T).run G
      (fun u => (decide (u ∈ R), false)) v).1) = _
  rw [iterate_correct G C h q R T]
  funext v
  simp only [Finset.mem_union, Bool.decide_or]

theorem pass_rounds {b : ℕ} (C : BitCode V b) (h q : ℕ) :
    (pass C h q).rounds = 4 + 2*h := by
  simp only [pass, prepareResidual, finishResidual, Program.rounds, ProgramMemory.rounds,
    selection, prepareLists, finishSelection, InitializerListBroadcast.rounds,
    MarkedBroadcast.rounds, FlagNeighborhood.rounds, Nat.zero_add, Nat.add_zero]
  omega

theorem rounds {b : ℕ} (C : BitCode V b) (h q T : ℕ) :
    (program C h q T).rounds = T * (4 + 2*h) := by
  simp only [program, step, Program.rounds, Program.iterate_rounds, ProgramMemory.rounds,
    pass_rounds, Nat.zero_add, Nat.add_zero]

theorem selection_maxBits {b : ℕ} (C : BitCode V b) (h q : ℕ) :
    (selection C h q).maxBits ≤ max 1 (h * (b + 1)) := by
  simp only [selection, prepareLists, finishSelection, Program.maxBits,
    ProgramMemory.maxBits, InitializerListBroadcast.maxBits,
    Nat.zero_max, Nat.max_zero]
  exact max_le (le_max_left _ _) (MarkedBroadcast.maxBits C h q)

theorem pass_maxBits {b : ℕ} (C : BitCode V b) (h q : ℕ) :
    (pass C h q).maxBits ≤ max 1 (h * (b + 1)) := by
  simp only [pass, prepareResidual, finishResidual, Program.maxBits,
    ProgramMemory.maxBits, FlagNeighborhood.maxBits, Nat.zero_max, Nat.max_zero]
  exact max_le (selection_maxBits C h q) (le_max_left _ _)

theorem maxBits {b : ℕ} (C : BitCode V b) (h q T : ℕ) :
    (program C h q T).maxBits ≤ max 1 (h * (b + 1)) := by
  simp only [program, Program.maxBits, Nat.zero_max, Nat.max_zero]
  apply (Program.iterate_maxBits (step C h q) T).trans
  simp only [step, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero]
  exact pass_maxBits C h q

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (h q T n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C h q T).maxBits ≤ (1 + h * (c + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hw := ListPacket.logarithmic_width h b c n hids
  apply (maxBits C h q T).trans
  apply max_le <;> nlinarith

end Paper.SimpleBroadcast

#print axioms Paper.SimpleBroadcast.selection_correct
#print axioms Paper.SimpleBroadcast.pass_correct
#print axioms Paper.SimpleBroadcast.iterate_correct
#print axioms Paper.SimpleBroadcast.correct
#print axioms Paper.SimpleBroadcast.rounds
#print axioms Paper.SimpleBroadcast.maxBits
#print axioms Paper.SimpleBroadcast.logarithmic_bits
