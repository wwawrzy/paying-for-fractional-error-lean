import Paper.Averaging.Tasks.TaskQueries
import Paper.Preliminaries.MinimumList

/-! Actual repeated-minimum program state and local transformations. The
eligible flag and previously selected IDs are private local state. -/
namespace Paper.SelectProtocol
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  active : Bool
  eligible : Bool
  chosen : List V

def localInput (v : V) (s : State V) : Bool × MinimumPayload.Data V :=
  (s.active, if s.active = true ∧ s.eligible = true ∧ v ∉ s.chosen then
    MinimumPayload.singleton v else 0)

def prepare : Program V (State V) ((Bool × MinimumPayload.Data V) × State V) :=
  .local fun v _ s => (localInput v s, s)

def finishLocal (answer : PayloadFlood.State (MinimumPayload.Data V)) (s : State V) : State V :=
  ⟨s.active, s.eligible, match answer.2 with
    | none => s.chosen
    | some a => match a.value with
      | none => s.chosen
      | some u => s.chosen ++ [u]⟩

def finish : Program V (PayloadFlood.State (MinimumPayload.Data V) × State V) (State V) :=
  .local fun _ _ s => finishLocal s.1 s.2

def step {b : ℕ} (C : BitCode V b) (D : ℕ) : Program V (State V) (State V) :=
  .seq prepare (.seq (ProgramMemory.carry (TaskQueries.minimumProgram C D)) finish)

def start : Program V (Bool × Bool) (State V) :=
  .local fun _ _ s => ⟨s.1, s.2, []⟩

def program {b : ℕ} (C : BitCode V b) (D n : ℕ) : Program V (Bool × Bool) (State V) :=
  .seq start ((step C D).iterate n)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_step {b : ℕ} (C : BitCode V b) (D : ℕ) (s : V → State V) :
    (step C D).run G s = fun v => finishLocal
      ((TaskQueries.minimumProgram C D).run G (fun u => localInput u (s u)) v) (s v) := by
  change finish.run G ((ProgramMemory.carry (TaskQueries.minimumProgram C D)).run G
    (fun v => (localInput v (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem metadata {b : ℕ} (C : BitCode V b) (D : ℕ) (s : V → State V) (v : V) :
    ((step C D).run G s v).active = (s v).active ∧
    ((step C D).run G s v).eligible = (s v).eligible := by
  rw [run_step]
  exact ⟨rfl, rfl⟩

theorem run_succ {b : ℕ} (C : BitCode V b) (D n : ℕ) (s : V → Bool × Bool) :
    (program C D (n + 1)).run G s = (step C D).run G ((program C D n).run G s) := rfl
end Paper.SelectProtocol
