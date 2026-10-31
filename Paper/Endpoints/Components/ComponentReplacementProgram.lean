import Paper.Endpoints.Components.SmallComponentProgram

/-! Actual sequential replacement keeps both algorithms' original private input.
No graph, component partition or optimum is given to the constructor. -/
namespace Paper.ComponentReplacementProgram
open BroadcastModel

def program {V In : Type} (A0 : Program V In Bool) (A1 : Program V In (Bool × Bool)) :
    Program V In Bool :=
  .seq (.local (fun _ _ x => (x, x)))
    (.seq (ProgramMemory.carry A0)
      (.seq (.local (fun _ _ x => (x.2, x.1)))
        (.seq (ProgramMemory.carry A1)
          (.local (fun _ _ x => if x.1.1 then x.1.2 else x.2)))))

theorem replacement_program_equations
    {V In : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A0 : Paper.BroadcastModel.Program V In Bool)
    (A1 : Paper.BroadcastModel.Program V In (Bool × Bool))
    (s : V → In) :
    let P : Paper.BroadcastModel.Program V In Bool :=
      .seq (.local (fun _ _ x => (x, x)))
        (.seq (Paper.ProgramMemory.carry A0)
          (.seq (.local (fun _ _ x => (x.2, x.1)))
            (.seq (Paper.ProgramMemory.carry A1)
              (.local (fun _ _ x => if x.1.1 then x.1.2 else x.2)))))
    (∀ v, P.runEncoded G s v =
      if (A1.runEncoded G s v).1 then (A1.runEncoded G s v).2 else A0.runEncoded G s v) ∧
    P.rounds = A0.rounds + A1.rounds ∧
    P.maxBits = max A0.maxBits A1.maxBits := by
  dsimp only
  simp only [Paper.BroadcastModel.Program.runEncoded_eq_run,
    Paper.BroadcastModel.Program.run, Paper.ProgramMemory.run,
    Paper.BroadcastModel.Program.rounds, Paper.ProgramMemory.rounds,
    Paper.BroadcastModel.Program.maxBits, Paper.ProgramMemory.maxBits,
    Nat.zero_add, Nat.add_zero, Nat.zero_max, Nat.max_zero]
  simp

theorem run_encoded
    {V In : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A0 : Program V In Bool) (A1 : Program V In (Bool × Bool)) (s : V → In) :
    (program A0 A1).runEncoded G s = fun v =>
      if (A1.runEncoded G s v).1 then (A1.runEncoded G s v).2 else A0.runEncoded G s v := by
  funext v
  exact (replacement_program_equations G A0 A1 s).1 v

theorem rounds {V In : Type} (A0 : Program V In Bool) (A1 : Program V In (Bool × Bool)) :
    (program A0 A1).rounds = A0.rounds + A1.rounds := by
  simp [program, Program.rounds, ProgramMemory.rounds]

theorem maxBits {V In : Type} (A0 : Program V In Bool) (A1 : Program V In (Bool × Bool)) :
    (program A0 A1).maxBits = max A0.maxBits A1.maxBits := by
  simp [program, Program.maxBits, ProgramMemory.maxBits]

end Paper.ComponentReplacementProgram

#print axioms Paper.ComponentReplacementProgram.replacement_program_equations

#print axioms Paper.ComponentReplacementProgram.run_encoded
#print axioms Paper.ComponentReplacementProgram.rounds
#print axioms Paper.ComponentReplacementProgram.maxBits
