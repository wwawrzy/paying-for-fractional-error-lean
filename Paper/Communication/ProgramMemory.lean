import Paper.Communication.BroadcastModel

/-! Preserve any private local input through an actual broadcast program
without sending additional bits or adding rounds. -/
namespace Paper.ProgramMemory
open BroadcastModel

def carry {V In Out X : Type} : Program V In Out → Program V (In × X) (Out × X)
  | .local f => .local fun v N s => (f v N s.1, s.2)
  | .broadcast b C R => .broadcast b C {
      send := fun v N s => R.send v N s.1
      update := fun v N s incoming => (R.update v N s.1 incoming, s.2) }
  | .seq P Q => .seq (carry P) (carry Q)

theorem run {V In Out X : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Program V In Out) :
    ∀ (s : V → In) (x : V → X),
      (carry P).run G (fun v => (s v, x v)) = fun v => (P.run G s v, x v) := by
  induction P with
  | «local» f => intro s x; rfl
  | broadcast b C R => intro s x; rfl
  | seq P Q ihP ihQ =>
    intro s x
    change (carry Q).run G ((carry P).run G (fun v => (s v, x v))) = _
    rw [ihP]
    exact ihQ _ x

theorem rounds {V In Out X : Type} (P : Program V In Out) :
    (carry (X := X) P).rounds = P.rounds := by
  induction P with
  | «local» f => rfl
  | broadcast b C R => rfl
  | seq P Q ihP ihQ => exact congrArg₂ (· + ·) ihP ihQ

theorem maxBits {V In Out X : Type} (P : Program V In Out) :
    (carry (X := X) P).maxBits = P.maxBits := by
  induction P with
  | «local» f => rfl
  | broadcast b C R => rfl
  | seq P Q ihP ihQ => exact congrArg₂ max ihP ihQ
end Paper.ProgramMemory
