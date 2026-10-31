import Paper.Communication.ProgramMemory

namespace Paper.InitializedProgram
open BroadcastModel
variable {V C Out : Type}

def program (P : Program V Bool Bool) (F : Program V ((Bool × Bool) × C) Out) :
    Program V (Bool × C) Out :=
  .seq (.local fun _ _ st => (st.1, st))
    (.seq (ProgramMemory.carry P)
      (.seq (.local fun _ _ st => ((st.1, st.2.1), st.2.2)) F))

theorem run [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Program V Bool Bool) (F : Program V ((Bool × Bool) × C) Out)
    (st : V → Bool × C) :
    (program P F).run G st = F.run G
      (fun u => ((P.run G (fun v => (st v).1) u, (st u).1), (st u).2)) := by
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G P]

theorem rounds (P : Program V Bool Bool) (F : Program V ((Bool × Bool) × C) Out) :
    (program P F).rounds = P.rounds + F.rounds := by
  simp only [program, Program.rounds, ProgramMemory.rounds, zero_add]

theorem maxBits (P : Program V Bool Bool) (F : Program V ((Bool × Bool) × C) Out) :
    (program P F).maxBits = max P.maxBits F.maxBits := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]

end Paper.InitializedProgram
