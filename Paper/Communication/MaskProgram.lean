import Paper.Averaging.Tasks.MaskedTaskGraph
import Paper.Communication.ProgramMemory

/-! Actual graph-free compiler for a public-ID masked task/zone graph.
A single participation-bit broadcast learns its exact local neighbors. -/
namespace Paper.MaskProgram
open BroadcastModel
variable {V : Type} [DecidableEq V]

structure Env (V : Type) where
  active : Bool
  neighbors : Finset V

def prepare : Program V Bool (Env V) := .broadcast 1 BitCode.bool {
  send := fun _ _ s => s
  update := fun _ N s incoming => ⟨s,
    if s then (N.attach.filter (fun u => incoming u = true)).image Subtype.val else ∅⟩ }

def simulateRound {In Out Msg : Type} {w : ℕ} (P : BitCode Msg w) (R : Round V In Out Msg) :
    Program V (In × Env V) (Out × Env V) := .broadcast w P {
  send := fun v _ s => R.send v s.2.neighbors s.1
  update := fun v N s incoming =>
    (R.update v (N ∩ s.2.neighbors) s.1
      (fun u => incoming ⟨u.val, (Finset.mem_inter.mp u.property).1⟩), s.2) }

def translate {In Out : Type} : Program V In Out → Program V (In × Env V) (Out × Env V)
  | .local f => .local fun v _ s => (f v s.2.neighbors s.1, s.2)
  | .broadcast _ P R => simulateRound P R
  | .seq P Q => .seq (translate P) (translate Q)

def execute {In Out : Type} (P : Program V In Out) : Program V (Bool × In) (Out × Env V) :=
  .seq (ProgramMemory.carry prepare) (.seq (.local fun _ _ s => (s.2, s.1)) (translate P))

theorem rounds {In Out : Type} (P : Program V In Out) : (translate P).rounds = P.rounds := by
  induction P with
  | «local» _ => rfl
  | broadcast _ _ _ => rfl
  | seq P Q ihP ihQ => exact congrArg₂ (· + ·) ihP ihQ

theorem maxBits {In Out : Type} (P : Program V In Out) : (translate P).maxBits = P.maxBits := by
  induction P with
  | «local» _ => rfl
  | broadcast _ _ _ => rfl
  | seq P Q ihP ihQ => exact congrArg₂ max ihP ihQ

theorem execute_rounds {In Out : Type} (P : Program V In Out) : (execute P).rounds = 1 + P.rounds := by
  simp only [execute, Program.rounds, ProgramMemory.rounds, rounds, Nat.zero_add]
  rfl

theorem execute_maxBits {In Out : Type} (P : Program V In Out) :
    (execute P).maxBits = max 1 P.maxBits := by
  simp only [execute, Program.maxBits, ProgramMemory.maxBits, maxBits, Nat.zero_max]
  rfl

theorem logarithmic_bits {In Out : Type} (P : Program V In Out) (n d : ℕ)
    (hmsg : P.maxBits ≤ d * Nat.clog 2 (n + 2)) :
    (execute P).maxBits ≤ (d + 1) * Nat.clog 2 (n + 2) := by
  rw [execute_maxBits]
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  apply max_le <;> nlinarith
end Paper.MaskProgram
