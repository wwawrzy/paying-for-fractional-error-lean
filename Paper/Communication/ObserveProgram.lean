import Paper.Communication.ClosedBitProgram
import Paper.Communication.ProgramMemory

/-! One-bit selected-neighborhood observation preserving all own state. -/
namespace Paper.ObserveProgram
open BroadcastModel SevenFoundation
variable {V S : Type} [DecidableEq V]

def program (flag : S → Bool) (update : V → S → Finset V → S) : Program V S S :=
  .seq (.local fun _ _ st => (flag st, st))
    (.seq (ProgramMemory.carry ClosedBitProgram.program)
      (.local fun v _ st => update v st.2 st.1))

theorem run [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (flag : S → Bool) (update : V → S → Finset V → S) (st : V → S)
    (A : Finset V) (hf : (fun v => flag (st v)) = fun v => decide (v ∈ A)) :
    (program flag update).run G st = fun v => update v (st v) (closed G v ∩ A) := by
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G ClosedBitProgram.program, hf, ClosedBitProgram.correct]

theorem rounds (flag : S → Bool) (update : V → S → Finset V → S) :
    (program flag update).rounds = 1 := rfl

theorem maxBits (flag : S → Bool) (update : V → S → Finset V → S) :
    (program flag update).maxBits = 1 := rfl

end Paper.ObserveProgram
