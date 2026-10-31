import Paper.Communication.BroadcastModel

namespace Paper.FixedMappedProgram
open BroadcastModel
variable {V In Out Y : Type}

def program (P : Program V In Out) (input : In) (f : Out → Y) : Program V Unit Y :=
  .seq (.local fun _ _ _ => input) (.seq P (.local fun _ _ s => f s))

theorem run [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Program V In Out) (input : In) (f : Out → Y) :
    (program P input f).run G (fun _ => ()) = fun v => f (P.run G (fun _ => input) v) := rfl

theorem rounds (P : Program V In Out) (input : In) (f : Out → Y) :
    (program P input f).rounds = P.rounds := by simp only [program, Program.rounds, zero_add, add_zero]

theorem maxBits (P : Program V In Out) (input : In) (f : Out → Y) :
    (program P input f).maxBits = P.maxBits := by simp only [program, Program.maxBits, Nat.zero_max, Nat.max_zero]

end Paper.FixedMappedProgram
