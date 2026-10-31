import Paper.Endpoints.Rounding.CoveringThresholdCost
import Paper.Communication.ProgramMemory

/-! Compose an executed fractional solver with numerical rounding while
preserving the original private covering input locally. -/
namespace Paper.CoveringSolverRounding

open BroadcastModel
variable {V S O : Type} [LinearOrder V]

def program {b B : ℕ} (ids : BitCode V b) (t q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdInput.Input V B)
    (numerator : O → ℕ) : Program V S GeneralCoveringRequests.Output :=
  .seq (.local (fun _ _ s => (s, s)))
    (.seq (ProgramMemory.carry solver)
      (.seq (.local (fun _ _ s => { read s.2 with numerator := numerator s.1 }))
        (CoveringThresholdInput.program ids B t q)))

theorem rounds {b B : ℕ} (ids : BitCode V b) (t q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdInput.Input V B)
    (numerator : O → ℕ) :
    (program ids t q solver read numerator).rounds = solver.rounds + 3 := by
  simp only [program, Program.rounds, ProgramMemory.rounds,
    CoveringThresholdInput.rounds, Nat.zero_add]

theorem maxBits {b B : ℕ} (ids : BitCode V b) (t q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdInput.Input V B)
    (numerator : O → ℕ) :
    (program ids t q solver read numerator).maxBits ≤
      max solver.maxBits (max (B + 2) (b + 1)) := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]
  exact max_le_max_left _ (CoveringThresholdInput.maxBits ids B t q)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def input {B : ℕ} (solver : Program V S O)
    (read : S → CoveringThresholdInput.Input V B) (numerator : O → ℕ) (s : V → S) :
    V → CoveringThresholdInput.Input V B :=
  fun v => { read (s v) with numerator := numerator (solver.runEncoded G s v) }

theorem run {b B : ℕ} (ids : BitCode V b) (t q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdInput.Input V B)
    (numerator : O → ℕ) (s : V → S) :
    (program ids t q solver read numerator).runEncoded G s =
      (CoveringThresholdInput.program ids B t q).runEncoded G
        (input G solver read numerator s) := by
  change (program ids t q solver read numerator).runEncoded G s =
    (CoveringThresholdInput.program ids B t q).runEncoded G
      (fun v => { read (s v) with numerator := numerator (solver.runEncoded G s v) })
  simp only [program, Program.runEncoded_eq_run, Program.run]
  rw [ProgramMemory.run]

theorem output_eq {b B : ℕ} (ids : BitCode V b) (t q : ℕ)
    (solver : Program V S O) (read : S → CoveringThresholdInput.Input V B)
    (numerator : O → ℕ) (s : V → S) :
    (Finset.univ.filter (fun v =>
      ((program ids t q solver read numerator).runEncoded G s v).selected = true)) =
        CoveringThresholdCost.output G ids t q (input G solver read numerator s) := by
  rw [run]
  rfl

end Paper.CoveringSolverRounding

#print axioms Paper.CoveringSolverRounding.rounds
#print axioms Paper.CoveringSolverRounding.maxBits
#print axioms Paper.CoveringSolverRounding.run
#print axioms Paper.CoveringSolverRounding.output_eq
