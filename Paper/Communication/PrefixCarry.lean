import Paper.Communication.PrefixProgram

/-! Preserve a private local register while executing a finite-string
program. The register is not transmitted and adds neither rounds nor bits. -/
namespace Paper.PrefixBroadcast.Program
open BroadcastModel

def carry {V In Out : Type} (A : Type) :
    Program V In Out → Program V (In × A) (Out × A)
  | .local f => .local (fun v N s => (f v N s.1, s.2))
  | .broadcast P => .broadcast {
      send := fun v N s => P.send v N s.1
      update := fun v N s msg => (P.update v N s.1 msg, s.2) }
  | .seq P Q => .seq (carry A P) (carry A Q)

theorem carry_rounds {V In Out A : Type} (P : Program V In Out) :
    (P.carry A).rounds = P.rounds := by
  induction P with
  | «local» f => rfl
  | broadcast P => rfl
  | seq P Q ihP ihQ => exact congrArg₂ (· + ·) ihP ihQ

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem carry_run {In Out A : Type} (P : Program V In Out) (s : V → In × A) :
    (P.carry A).run G s = fun v => (P.run G (fun u => (s u).1) v, (s v).2) := by
  induction P with
  | «local» f => rfl
  | broadcast P => rfl
  | seq P Q ihP ihQ =>
    change (Q.carry A).run G ((P.carry A).run G s) = _
    rw [ihQ, ihP]
    rfl

theorem carry_bits {In Out A : Type} (P : Program V In Out) (s : V → In × A) :
    (P.carry A).maxBits G s = P.maxBits G (fun u => (s u).1) := by
  induction P with
  | «local» f => rfl
  | broadcast P => rfl
  | seq P Q ihP ihQ =>
    change max ((P.carry A).maxBits G s)
      ((Q.carry A).maxBits G ((P.carry A).run G s)) = _
    rw [ihP, ihQ, carry_run]
    rfl

end Paper.PrefixBroadcast.Program
#print axioms Paper.PrefixBroadcast.Program.carry_run
#print axioms Paper.PrefixBroadcast.Program.carry_bits
