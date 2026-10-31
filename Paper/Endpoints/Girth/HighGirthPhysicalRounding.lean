import Paper.Endpoints.Girth.HighGirthPhysicalSolverCorrect

/-! Execute physical solver output and then the exact Boolean rounding.
Only local integer arithmetic is used to threshold the capped value. -/
namespace Paper.HighGirthPhysicalRounding
open BroadcastModel (BitCode)
variable {V : Type} [LinearOrder V]

def squeeze (D : Nat) {N : Nat} (st : Bool × Fin N) : Fin 2 :=
  if st.1 && decide (D < 2 * st.2.val) then ⟨1, by decide⟩ else ⟨0, by decide⟩

def program {N b : Nat} (C : BitCode V b)
    (P : BroadcastModel.Program V (Bool × Fin 4) (Fin N)) (D : Nat) :
    PortBroadcastModel.Program V Unit Bool :=
  .seq (HighGirthPhysicalSolver.core C P)
    (.seq (.local fun _ _ st => squeeze D st) HighGirthFullProgram.program)

theorem rounds {N b : Nat} (C : BitCode V b)
    (P : BroadcastModel.Program V (Bool × Fin 4) (Fin N)) (D : Nat) :
    (program C P D).rounds = 11 + P.rounds := by
  simp only [program, HighGirthPhysicalSolver.core, HighGirthPhysicalSolver.kernel,
    PortBroadcastModel.Program.rounds, HighGirthInitializationProgram.rounds,
    HighGirthFullProgram.rounds, KT0Compiler.program_rounds,
    BroadcastModel.Program.rounds, MaskProgram.execute_rounds]
  omega

theorem maxBits {N b : Nat} (C : BitCode V b)
    (P : BroadcastModel.Program V (Bool × Fin 4) (Fin N)) (D : Nat) :
    (program C P D).maxBits = max 1 (max b P.maxBits) := by
  simp only [program, HighGirthPhysicalSolver.core, HighGirthPhysicalSolver.kernel,
    PortBroadcastModel.Program.maxBits, HighGirthInitializationProgram.maxBits,
    HighGirthFullProgram.maxBits, KT0Compiler.program_maxBits,
    BroadcastModel.Program.maxBits, MaskProgram.execute_maxBits]
  omega

theorem threshold_cap (D n : Nat) (hD : 0 < D) :
    (1 : Real)/2 < min 1 ((n : Real)/D) ↔ D < 2*n := by
  rw [lt_min_iff]
  norm_num only [one_div, inv_pos, Nat.ofNat_pos, and_true, true_and]
  exact (HighGirthSelectionProgram.threshold D n hD).symm

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem squeeze_correct {N : Nat} (p : V → Fin N) (D : Nat) (hD : 0 < D) :
    (fun v => squeeze D (decide (v ∈ HighGirthTransformation.zone G), p v)) =
      HighGirthFullProgram.thresholdBit
        (HighGirthMaskedInput.capped G (fun v => ((p v).val : Real)/D)) := by
  classical
  funext v
  by_cases hv : v ∈ HighGirthTransformation.zone G
  · have ht := threshold_cap D (p v).val hD
    apply Fin.ext
    simp only [squeeze, decide_eq_true hv, Bool.true_and,
      HighGirthFullProgram.thresholdBit, HighGirthMaskedInput.capped,
      HighGirthAuxiliary.restrict, if_pos hv, PartialOptimum.cap]
    simp only [decide_eq_true_eq, ht]
  · apply Fin.ext
    norm_num [squeeze, hv, HighGirthFullProgram.thresholdBit, HighGirthMaskedInput.capped,
      HighGirthAuxiliary.restrict]

end Paper.HighGirthPhysicalRounding
#print axioms Paper.HighGirthPhysicalRounding.rounds
#print axioms Paper.HighGirthPhysicalRounding.maxBits
#print axioms Paper.HighGirthPhysicalRounding.threshold_cap
#print axioms Paper.HighGirthPhysicalRounding.squeeze_correct
