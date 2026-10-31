import Paper.Communication.ZoneProgram
import Paper.Communication.MaskProgramCorrect

/-! A graph-independent compiler feeds the computed zone/demand/weight
bits to any public-ID program on the exact masked zone graph. -/
namespace Paper.ZoneSolveProgram
open BroadcastModel SevenFoundation
variable {V Out : Type} [DecidableEq V]

def program (d : ℕ) (P : Program V (Bool × Fin (d + 2)) Out) (zero : Out) :
    Program V Unit (Out × ZoneProgram.Env d) :=
  .seq (ZoneProgram.program d)
    (.seq (.local fun _ _ e => ((e.zone, (e.demand, e.cost)), e))
      (.seq (ProgramMemory.carry (MaskProgram.execute P))
        (.local fun _ _ st => (if st.2.zone then st.1.1 else zero, st.2))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run (d : ℕ) (P : Program V (Bool × Fin (d + 2)) Out) (zero : Out) :
    (program d P zero).run G (fun _ => ()) = fun v =>
      (if v ∈ WeightedBudget.zone G d then
        P.run (MaskedTaskGraph.graph G (WeightedBudget.zone G d))
          (fun u => (decide (u ∈ WeightedBudget.initialDemands G d), (ZoneProgram.expected G d u).cost)) v
        else zero, ZoneProgram.expected G d v) := by
  dsimp only [program, Program.run]
  rw [ZoneProgram.correct, ProgramMemory.run G (MaskProgram.execute P)]
  dsimp only [ZoneProgram.expected]
  rw [MaskProgramCorrect.execute_correct]
  funext v
  simp only [decide_eq_true_eq]

theorem rounds (d : ℕ) (P : Program V (Bool × Fin (d + 2)) Out) (zero : Out) :
    (program d P zero).rounds = 4 + P.rounds := by
  simp only [program, Program.rounds, ZoneProgram.rounds, ProgramMemory.rounds,
    MaskProgram.execute_rounds, zero_add, add_zero]
  omega

theorem maxBits (d : ℕ) (P : Program V (Bool × Fin (d + 2)) Out) (zero : Out) :
    (program d P zero).maxBits = max 1 P.maxBits := by
  simp only [program, Program.maxBits, ZoneProgram.maxBits, ProgramMemory.maxBits,
    MaskProgram.execute_maxBits, Nat.zero_max, Nat.max_zero]
  omega

end Paper.ZoneSolveProgram
