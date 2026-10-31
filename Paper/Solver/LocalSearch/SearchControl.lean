import Paper.Solver.LocalSearch.SearchCount
import Paper.Owners.Construction.HeavyListShape
import Paper.Preliminaries.ListedCosts

/-! Actual shared control for one search budget: exact demand count,
bounded heavy-ID list, and actual bounded costs for every listed ID. -/
namespace Paper.SearchControl
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Output (V : Type) (B : ℕ) where
  large : Bool
  candidates : SolutionWord.Word V B

def heavyInput {B q : ℕ} (s : TerminalProtocol.Input V B q) : Bool × Bool :=
  (s.active, decide (s.active = true ∧ 0 < s.value.val))

def prepareCount (B q : ℕ) : Program V (TerminalProtocol.Input V B q)
    (TerminalProtocol.Input V B q × TerminalProtocol.Input V B q) := .local fun _ _ s => (s, s)

def finishCount (B q : ℕ) : Program V (Option ℕ × TerminalProtocol.Input V B q)
    (TerminalProtocol.Input V B q × Option ℕ) := .local fun _ _ s => (s.2, s.1)

def countStage {b : ℕ} (C : BitCode V b) (D B q : ℕ) :=
  Program.seq (prepareCount B q) (.seq
    (ProgramMemory.carry (SearchCount.program C D B q)) (finishCount B q))

def prepareHeavy (B q : ℕ) : Program V (TerminalProtocol.Input V B q × Option ℕ)
    ((Bool × Bool) × (TerminalProtocol.Input V B q × Option ℕ)) :=
  .local fun _ _ s => (heavyInput s.1, s)

def prepareCosts (B q : ℕ) : Program V
    (SelectProtocol.State V × (TerminalProtocol.Input V B q × Option ℕ))
    (DemandValues.Input V B × (List V × Option ℕ)) :=
  .local fun _ _ s => (⟨s.2.1.active, s.2.1.cost, s.1.chosen⟩, (s.1.chosen, s.2.2))

def finish (B a m : ℕ) : Program V
    ((DemandValues.Input V B × Option (Fin (2 * a * m) → ℕ)) × (List V × Option ℕ)) (Output V B) :=
  .local fun _ _ s => ⟨match s.2.2 with
      | none => false
      | some n => decide (2 * (a + 1) * m ≤ n),
    match s.1.2 with
      | none => []
      | some costs => ListedCosts.tags B (2 * a * m) s.2.1 costs⟩

def program {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :=
  Program.seq (countStage C D B q) (.seq (prepareHeavy B q) (.seq
    (ProgramMemory.carry (HeavyListing.program C D a m)) (.seq (prepareCosts B q) (.seq
      (ProgramMemory.carry (DemandValues.program C D B (2 * a * m))) (finish B a m)))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def heavyStates {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) (s : V → TerminalProtocol.Input V B q) :=
  (HeavyListing.program C D a m).run G (fun v => heavyInput (s v))

def costInputs {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) (s : V → TerminalProtocol.Input V B q)
    (v : V) : DemandValues.Input V B := ⟨(s v).active, (s v).cost, (heavyStates G C D a B q m s v).chosen⟩

theorem run_countStage {b : ℕ} (C : BitCode V b) (D B q : ℕ) (s : V → TerminalProtocol.Input V B q) :
    (countStage C D B q).run G s = fun v => (s v, (SearchCount.program C D B q).run G s v) := by
  change (finishCount B q).run G ((ProgramMemory.carry (SearchCount.program C D B q)).run G
    (fun v => (s v, s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem run_program {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) (s : V → TerminalProtocol.Input V B q) :
    (program C D a B q m).run G s = fun v =>
      ⟨match (SearchCount.program C D B q).run G s v with
        | none => false
        | some n => decide (2 * (a + 1) * m ≤ n),
       match ((DemandValues.program C D B (2 * a * m)).run G (costInputs G C D a B q m s) v).2 with
        | none => []
        | some costs => ListedCosts.tags B (2 * a * m) (heavyStates G C D a B q m s v).chosen costs⟩ := by
  change (finish B a m).run G ((ProgramMemory.carry (DemandValues.program C D B (2 * a * m))).run G
    ((prepareCosts B q).run G ((ProgramMemory.carry (HeavyListing.program C D a m)).run G
      ((prepareHeavy B q).run G ((countStage C D B q).run G s))))) = _
  rw [run_countStage]
  change (finish B a m).run G ((ProgramMemory.carry (DemandValues.program C D B (2 * a * m))).run G
    ((prepareCosts B q).run G ((ProgramMemory.carry (HeavyListing.program C D a m)).run G
      (fun v => (heavyInput (s v), (s v, (SearchCount.program C D B q).run G s v)))))) = _
  rw [ProgramMemory.run G (HeavyListing.program C D a m)]
  change (finish B a m).run G ((ProgramMemory.carry (DemandValues.program C D B (2 * a * m))).run G
    (fun v => (costInputs G C D a B q m s v,
      ((heavyStates G C D a B q m s v).chosen, (SearchCount.program C D B q).run G s v)))) = _
  rw [ProgramMemory.run G (DemandValues.program C D B (2 * a * m))]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (program C D a B q m).rounds = (2 * a * m + 3) * (4 * D + 1) + 1 := by
  simp only [program, countStage, prepareCount, finishCount, prepareHeavy, prepareCosts, finish,
    Program.rounds, ProgramMemory.rounds, SearchCount.rounds, HeavyListing.rounds, DemandValues.rounds]
  ring
end Paper.SearchControl
