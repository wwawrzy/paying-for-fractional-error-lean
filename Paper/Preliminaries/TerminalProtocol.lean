import Paper.Preliminaries.TerminalDataCorrect
import Paper.Preliminaries.SelectCorrect

/-! Complete concrete small-demand terminal protocol. Input contains only
local task membership, own bounded cost and own bounded residual demand.
The common demand-ID list is computed by actual repeated-min queries. -/
namespace Paper.TerminalProtocol
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B q : ℕ) where
  active : Bool
  cost : Fin (B + 1)
  value : Fin (q + 1)

def selectionInput {B q : ℕ} (s : Input V B q) : Bool × Bool :=
  (s.active, decide (0 < s.value.val))

def prepare (B q : ℕ) : Program V (Input V B q) ((Bool × Bool) × Input V B q) :=
  .local fun _ _ s => (selectionInput s, s)

def dataInput {B q : ℕ} (chosen : SelectProtocol.State V) (s : Input V B q) : TerminalData.Input V B q :=
  ⟨s.active, s.cost, s.value, chosen.chosen⟩

def prepareData (B q : ℕ) : Program V (SelectProtocol.State V × Input V B q) (TerminalData.Input V B q) :=
  .local fun _ _ s => dataInput s.1 s.2

def program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :=
  Program.seq (prepare B q) (.seq
    (ProgramMemory.carry (SelectProtocol.program C D T)) (.seq (prepareData B q)
      (TerminalData.program C D B q T m)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def dataState {b : ℕ} (C : BitCode V b) (D B q T : ℕ) (s : V → Input V B q) (v : V) :=
  dataInput ((SelectProtocol.program C D T).run G (fun u => selectionInput (s u)) v) (s v)

theorem run_program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) (s : V → Input V B q) :
    (program C D B q T m).run G s = (TerminalData.program C D B q T m).run G
      (dataState G C D B q T s) := by
  change (TerminalData.program C D B q T m).run G
    ((prepareData B q).run G ((ProgramMemory.carry (SelectProtocol.program C D T)).run G
      (fun v => (selectionInput (s v), s v)))) = _
  rw [ProgramMemory.run]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :
    (program C D B q T m).rounds = (T + 2 ^ T + 1) * (4 * D + 1) := by
  simp only [program, prepare, prepareData, Program.rounds, ProgramMemory.rounds,
    SelectCorrect.rounds, TerminalData.rounds]
  ring

theorem maxBits {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :
    (program C D B q T m).maxBits ≤
      max (b + T * (q + 1) + 1) (max (2 * b + B + 3) (D + 2)) := by
  have hs : (SelectProtocol.program C D T).maxBits ≤
      max (b + T * (q + 1) + 1) (max (2 * b + B + 3) (D + 2)) := by
    apply (SelectCorrect.maxBits C D T).trans
    apply max_le
    · exact (by omega : 2 * b + 2 ≤ 2 * b + B + 3) |>.trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans (le_max_right _ _)
  simp only [program, prepare, prepareData, Program.maxBits, ProgramMemory.maxBits,
    Nat.zero_max]
  exact max_le hs (TerminalData.maxBits C D B q T m)
end Paper.TerminalProtocol
