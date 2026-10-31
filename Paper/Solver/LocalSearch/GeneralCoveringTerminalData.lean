import Paper.Preliminaries.DemandValues
import Paper.Solver.LocalSearch.GeneralCoveringTable
import Paper.Preliminaries.TableInterpretation

/-! Concrete terminal protocol on an already collected bounded demand list:
query its residual values, query the representative table, then compute the
minimum-cost bounded word locally. All private inputs remain local. -/
namespace Paper.GeneralCoveringTerminalData
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B q : ℕ) where
  active : Bool
  cost : Fin (B + 1)
  value : Fin (q + 1)
  demands : List V
  targets : Finset V

def valueInput {B q : ℕ} (s : Input V B q) : DemandValues.Input V q :=
  ⟨s.active, s.value, s.demands⟩

def maskInput {B q : ℕ} (s : Input V B q) : GeneralCoveringQuery.Input V B :=
  ⟨s.active, s.cost, s.demands, s.targets⟩

def prepareValues (B q : ℕ) : Program V (Input V B q) (DemandValues.Input V q × Input V B q) :=
  .local fun _ _ s => (valueInput s, s)

def finishValues (B q T : ℕ) : Program V
    ((DemandValues.Input V q × Option (Fin T → ℕ)) × Input V B q)
    (Input V B q × Option (Fin T → ℕ)) :=
  .local fun _ _ s => (s.2, s.1.2)

def valueStage {b : ℕ} (C : BitCode V b) (D B q T : ℕ) :=
  Program.seq (prepareValues B q) (.seq
    (ProgramMemory.carry (DemandValues.program C D q T)) (finishValues B q T))

def prepareTable (B q T : ℕ) : Program V (Input V B q × Option (Fin T → ℕ))
    (GeneralCoveringQuery.Input V B × Option (Fin T → ℕ)) :=
  .local fun _ _ s => (maskInput s.1, s.2)

def finish (B T m : ℕ) : Program V
    ((GeneralCoveringQuery.Input V B × List (TabularSearch.Entry V T)) × Option (Fin T → ℕ))
    (Option (List (TabularSearch.Entry V T))) :=
  .local fun _ _ s => match s.2 with
    | none => none
    | some target => TabularSearch.choose s.1.2 m target

def program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :=
  Program.seq (valueStage C D B q T) (.seq (prepareTable B q T) (.seq
    (ProgramMemory.carry (GeneralCoveringTable.alphabetProgram C D B T)) (finish B T m)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_valueStage {b : ℕ} (C : BitCode V b) (D B q T : ℕ) (s : V → Input V B q) :
    (valueStage C D B q T).run G s = fun v => (s v,
      ((DemandValues.program C D q T).run G (fun u => valueInput (s u)) v).2) := by
  change (finishValues B q T).run G ((ProgramMemory.carry (DemandValues.program C D q T)).run G
    (fun v => (valueInput (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem run_program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) (s : V → Input V B q) :
    (program C D B q T m).run G s = fun v =>
      match ((DemandValues.program C D q T).run G (fun u => valueInput (s u)) v).2 with
      | none => none
      | some target => TabularSearch.choose
          (((GeneralCoveringTable.alphabetProgram C D B T).run G (fun u => maskInput (s u)) v).2) m target := by
  change (finish B T m).run G ((ProgramMemory.carry (GeneralCoveringTable.alphabetProgram C D B T)).run G
    ((prepareTable B q T).run G ((valueStage C D B q T).run G s))) = _
  rw [run_valueStage]
  change (finish B T m).run G ((ProgramMemory.carry (GeneralCoveringTable.alphabetProgram C D B T)).run G
    (fun v => (maskInput (s v),
      ((DemandValues.program C D q T).run G (fun u => valueInput (s u)) v).2))) = _
  rw [ProgramMemory.run]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :
    (program C D B q T m).rounds = (2 ^ T + 1) * (4 * D + 1) := by
  simp only [program, valueStage, prepareValues, finishValues, prepareTable, finish,
    Program.rounds, ProgramMemory.rounds, DemandValues.rounds, GeneralCoveringTable.rounds]
  ring

theorem maxBits {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :
    (program C D B q T m).maxBits ≤
      max (b + T * (q + 1) + 1) (max (2 * b + B + 3) (D + 2)) := by
  have hv : (valueStage C D B q T).maxBits ≤ max (b + T * (q + 1) + 1) (D + 2) := by
    simpa only [valueStage, prepareValues, finishValues, Program.maxBits, ProgramMemory.maxBits,
      Nat.max_zero, Nat.zero_max] using DemandValues.maxBits C D q T
  have ht := GeneralCoveringTable.maxBits C D B T
  apply max_le
  · apply hv.trans
    exact max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))
  · change max (prepareTable B q T).maxBits
      (max (ProgramMemory.carry (GeneralCoveringTable.alphabetProgram C D B T)).maxBits (finish B T m).maxBits) ≤ _
    simp only [prepareTable, finish, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero, Nat.zero_max]
    exact ht.trans (le_max_right _ _)
end Paper.GeneralCoveringTerminalData
