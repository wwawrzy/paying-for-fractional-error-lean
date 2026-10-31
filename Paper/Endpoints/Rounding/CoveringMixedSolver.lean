import Paper.Endpoints.Rounding.CoveringMixedFeasible
import Paper.Communication.ProgramMemory

/-! Preserve private covering incidences through an actual fractional solver,
then execute the single mixed-threshold rule in four additional rounds. -/
namespace Paper.CoveringMixedSolver
open BroadcastModel
variable {V S O : Type} [LinearOrder V]

def program {b B : ℕ} (I : BitCode V b) (a q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdFlags.Input V B)
    (numerator : O → ℕ) : Program V S GeneralCoveringRequests.Output :=
  .seq (.local fun _ _ s => (s, s))
    (.seq (ProgramMemory.carry solver)
      (.seq (.local fun _ _ s => { read s.2 with numerator := numerator s.1 })
        (CoveringThresholdFlags.roundedProgram I B a q)))

theorem rounds {b B : ℕ} (I : BitCode V b) (a q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdFlags.Input V B)
    (numerator : O → ℕ) :
    (program I a q solver read numerator).rounds = solver.rounds + 4 := by
  simp only [program, Program.rounds, ProgramMemory.rounds,
    CoveringThresholdFlags.rounded_rounds, Nat.zero_add]

theorem maxBits {b B : ℕ} (I : BitCode V b) (a q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdFlags.Input V B)
    (numerator : O → ℕ) :
    (program I a q solver read numerator).maxBits ≤ max solver.maxBits (max (B + 2) (b + 1)) := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]
  exact max_le_max_left _ (CoveringThresholdFlags.rounded_maxBits I B a q)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def input {B : ℕ} (solver : Program V S O)
    (read : S → CoveringThresholdFlags.Input V B) (numerator : O → ℕ) (s : V → S) :
    V → CoveringThresholdFlags.Input V B :=
  fun v => { read (s v) with numerator := numerator (solver.runEncoded G s v) }

theorem run {b B : ℕ} (I : BitCode V b) (a q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdFlags.Input V B)
    (numerator : O → ℕ) (s : V → S) :
    (program I a q solver read numerator).runEncoded G s =
      (CoveringThresholdFlags.roundedProgram I B a q).runEncoded G (input G solver read numerator s) := by
  change (program I a q solver read numerator).runEncoded G s =
    (CoveringThresholdFlags.roundedProgram I B a q).runEncoded G
      (fun v => { read (s v) with numerator := numerator (solver.runEncoded G s v) })
  simp only [program, Program.runEncoded_eq_run, Program.run]
  rw [ProgramMemory.run]

theorem output_eq {b B : ℕ} (I : BitCode V b) (a q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdFlags.Input V B)
    (numerator : O → ℕ) (s : V → S) :
    Finset.univ.filter (fun v => ((program I a q solver read numerator).runEncoded G s v).selected = true) =
      CoveringMixedCost.output G I a q (input G solver read numerator s) := by
  rw [run]
  rfl

end Paper.CoveringMixedSolver

#print axioms Paper.CoveringMixedSolver.rounds
#print axioms Paper.CoveringMixedSolver.maxBits
#print axioms Paper.CoveringMixedSolver.run
#print axioms Paper.CoveringMixedSolver.output_eq
