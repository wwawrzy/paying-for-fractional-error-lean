import Paper.Solver.LocalSearch.SearchControlCorrect
import Paper.Solver.LocalSearch.SearchControlBudget
import Paper.Solver.LocalSearch.SearchResidual
import Paper.Preliminaries.BestWord

/-! Fixed padded sequence of actual recursive branch calls. Missing list
slots still run the child but contribute no proposal. Parent private input
and shared control are preserved without additional communication. -/
namespace Paper.BranchLoop
open BroadcastModel
variable {V : Type} [DecidableEq V]

structure State (V : Type) (B q : ℕ) where
  input : TerminalProtocol.Input V B q
  info : SearchControl.Output V B
  best : Option (SolutionWord.Word V B)

def childInput {B q : ℕ} (j : ℕ) (v : V) (N : Finset V) (s : State V B q) :=
  match s.info.candidates[j]? with
  | none => s.input
  | some t => SearchResidual.localUpdate v N (SolutionWord.id t) s.input

def proposal {B : ℕ} (t : Option (CostTag.Tag V B)) (w : Option (SolutionWord.Word V B)) :=
  t.bind (fun t => w.map (fun w => t :: w))

def prepare (B q j : ℕ) : Program V (State V B q) (TerminalProtocol.Input V B q × State V B q) :=
  .local fun v N s => (childInput j v N s, s)

def finish (B q j : ℕ) : Program V (Option (SolutionWord.Word V B) × State V B q) (State V B q) :=
  .local fun _ _ s => ⟨s.2.input, s.2.info,
    BestWord.better s.2.best (proposal s.2.info.candidates[j]? s.1)⟩

def step {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) : Program V (State V B q) (State V B q) :=
  .seq (prepare B q j) (.seq (ProgramMemory.carry P) (finish B q j))

def program {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B))) :
    List ℕ → Program V (State V B q) (State V B q)
  | [] => .local fun _ _ s => s
  | j :: js => .seq (step P j) (program P js)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def childState {B q : ℕ} (j : ℕ) (s : V → State V B q) (v : V) :=
  childInput j v (G.neighborFinset v) (s v)

def choice {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) (s : V → State V B q) (v : V) :=
  proposal (s v).info.candidates[j]? (P.run G (childState G j s) v)

theorem run_step {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) (s : V → State V B q) :
    (step P j).run G s = fun v => ⟨(s v).input, (s v).info,
      BestWord.better (s v).best (choice G P j s v)⟩ := by
  change (finish B q j).run G ((ProgramMemory.carry P).run G
    (fun v => (childInput j v (G.neighborFinset v) (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem metadata {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) (s : V → State V B q) : ∀ v,
    ((step P j).run G s v).input = (s v).input ∧ ((step P j).run G s v).info = (s v).info := by
  intro v
  rw [run_step]
  exact ⟨rfl, rfl⟩

theorem choices_eq {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (s t : V → State V B q) (h : ∀ v, (s v).input = (t v).input ∧ (s v).info = (t v).info) :
    ∀ j v, choice G P j s v = choice G P j t v := by
  intro j v
  have hc : childState G j s = childState G j t := by
    funext u
    dsimp only [childState, childInput]
    rw [(h u).1, (h u).2]
  dsimp only [choice]
  rw [(h v).2, hc]

theorem invariant {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (js : List ℕ) (s : V → State V B q) :
    (∀ v, ((program P js).run G s v).input = (s v).input ∧
      ((program P js).run G s v).info = (s v).info) ∧
    (∀ v, ((program P js).run G s v).best = BestWord.fold (s v).best
      (js.map (fun j => choice G P j s v))) := by
  induction js generalizing s with
  | nil => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  | cons j js ih =>
    let t := (step P j).run G s
    have ht : ∀ v, (t v).input = (s v).input ∧ (t v).info = (s v).info := metadata G P j s
    obtain ⟨hm, hb⟩ := ih t
    refine ⟨fun v => ⟨(hm v).1.trans (ht v).1, (hm v).2.trans (ht v).2⟩, ?_⟩
    intro v
    have htbest : (t v).best = BestWord.better (s v).best (choice G P j s v) := by
      change ((step P j).run G s v).best = _
      rw [run_step]
    change ((program P js).run G t v).best = _
    rw [hb v, htbest]
    simp only [choices_eq G P t s ht, List.map_cons, BestWord.fold]

theorem rounds {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (js : List ℕ) : (program P js).rounds = js.length * P.rounds := by
  induction js with
  | nil => simp [program, Program.rounds]
  | cons j js ih =>
    simp only [program, step, prepare, finish, Program.rounds, ProgramMemory.rounds, ih,
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero]
    omega

theorem maxBits {B q : ℕ} (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (js : List ℕ) : (program P js).maxBits ≤ P.maxBits := by
  induction js with
  | nil => exact Nat.zero_le _
  | cons j js ih =>
    apply max_le ?_ ih
    simp only [step, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
    exact le_rfl
end Paper.BranchLoop
