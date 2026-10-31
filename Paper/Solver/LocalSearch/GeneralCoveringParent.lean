import Paper.Solver.LocalSearch.GeneralCoveringLoop

/-! Actual fixed-schedule parent: run terminal and branch control, preserve
private data, execute all padded child slots, then select the applicable
case locally. All supplied components are concrete broadcast programs. -/
namespace Paper.GeneralCoveringParent
open BroadcastModel
variable {V : Type} [DecidableEq V]

def prepareLeaf (B q : ℕ) : Program V (GeneralCoveringResidual.Input V B q)
    (GeneralCoveringResidual.Input V B q × GeneralCoveringResidual.Input V B q) := .local fun _ _ s => (s, s)

def prepareControl (B q : ℕ) : Program V (Option (SolutionWord.Word V B) × GeneralCoveringResidual.Input V B q)
    (GeneralCoveringResidual.Input V B q × (Option (SolutionWord.Word V B) × GeneralCoveringResidual.Input V B q)) :=
  .local fun _ _ s => (s.2, s)

def initializeLoop (B q : ℕ) : Program V
    (SearchControl.Output V B × (Option (SolutionWord.Word V B) × GeneralCoveringResidual.Input V B q))
    (GeneralCoveringLoop.State V B q × Option (SolutionWord.Word V B)) :=
  .local fun _ _ s => (⟨s.2.2, s.1, none⟩, s.2.1)

def finish (B q : ℕ) : Program V (GeneralCoveringLoop.State V B q × Option (SolutionWord.Word V B))
    (Option (SolutionWord.Word V B)) :=
  .local fun _ _ s => if s.1.info.large then s.1.best else s.2

def program {B q : ℕ}
    (leaf : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (control : Program V (GeneralCoveringResidual.Input V B q) (SearchControl.Output V B))
    (child : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B))) (K : ℕ) :=
  Program.seq (prepareLeaf B q) (.seq (ProgramMemory.carry leaf) (.seq (prepareControl B q)
    (.seq (ProgramMemory.carry control) (.seq (initializeLoop B q)
      (.seq (ProgramMemory.carry (GeneralCoveringLoop.program child (List.range K))) (finish B q))))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def initialState {B q : ℕ}
    (control : Program V (GeneralCoveringResidual.Input V B q) (SearchControl.Output V B))
    (s : V → GeneralCoveringResidual.Input V B q) (v : V) : GeneralCoveringLoop.State V B q :=
  ⟨s v, control.run G s v, none⟩

theorem run_program {B q : ℕ}
    (leaf : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (control : Program V (GeneralCoveringResidual.Input V B q) (SearchControl.Output V B))
    (child : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (K : ℕ) (s : V → GeneralCoveringResidual.Input V B q) :
    (program leaf control child K).run G s = fun v =>
      if (control.run G s v).large then
        BestWord.fold none ((List.range K).map (fun j => GeneralCoveringLoop.choice G child j (initialState G control s) v))
      else leaf.run G s v := by
  change (finish B q).run G ((ProgramMemory.carry (GeneralCoveringLoop.program child (List.range K))).run G
    ((initializeLoop B q).run G ((ProgramMemory.carry control).run G ((prepareControl B q).run G
      ((ProgramMemory.carry leaf).run G (fun v => (s v, s v))))))) = _
  rw [ProgramMemory.run G leaf]
  change (finish B q).run G ((ProgramMemory.carry (GeneralCoveringLoop.program child (List.range K))).run G
    ((initializeLoop B q).run G ((ProgramMemory.carry control).run G
      (fun v => (s v, (leaf.run G s v, s v)))))) = _
  rw [ProgramMemory.run G control]
  change (finish B q).run G ((ProgramMemory.carry (GeneralCoveringLoop.program child (List.range K))).run G
    (fun v => (initialState G control s v, leaf.run G s v))) = _
  rw [ProgramMemory.run G (GeneralCoveringLoop.program child (List.range K))]
  funext v
  have hi := GeneralCoveringLoop.invariant G child (List.range K) (initialState G control s)
  change (if ((GeneralCoveringLoop.program child (List.range K)).run G (initialState G control s) v).info.large
    then ((GeneralCoveringLoop.program child (List.range K)).run G (initialState G control s) v).best
    else leaf.run G s v) = _
  rw [(hi.1 v).2, hi.2 v]
  rfl

theorem rounds {B q : ℕ}
    (leaf : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (control : Program V (GeneralCoveringResidual.Input V B q) (SearchControl.Output V B))
    (child : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B))) (K : ℕ) :
    (program leaf control child K).rounds = leaf.rounds + control.rounds + K * child.rounds := by
  simp only [program, prepareLeaf, prepareControl, initializeLoop, finish, Program.rounds,
    ProgramMemory.rounds, GeneralCoveringLoop.rounds, List.length_range, Nat.zero_add, Nat.add_zero]
  omega

theorem maxBits {B q : ℕ}
    (leaf : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (control : Program V (GeneralCoveringResidual.Input V B q) (SearchControl.Output V B))
    (child : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B))) (K : ℕ) :
    (program leaf control child K).maxBits ≤ max leaf.maxBits (max control.maxBits child.maxBits) := by
  simp only [program, prepareLeaf, prepareControl, initializeLoop, finish, Program.maxBits,
    ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  apply max_le (le_max_left _ _)
  apply max_le ((le_max_left _ _).trans (le_max_right _ _))
  exact (GeneralCoveringLoop.maxBits child (List.range K)).trans ((le_max_right _ _).trans (le_max_right _ _))
end Paper.GeneralCoveringParent
