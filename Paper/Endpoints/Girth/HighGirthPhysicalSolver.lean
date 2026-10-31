import Paper.Endpoints.Girth.HighGirthSolverParameters
import Paper.Averaging.Tasks.KT0Compiler
import Paper.Communication.MaskProgramCorrect

/-! Physical original-graph KT0 execution of the weighted solver on Z.
Initialization computes all private participation, demand and weight data. -/
namespace Paper.HighGirthPhysicalSolver
open BroadcastModel (BitCode)
variable {V : Type} [LinearOrder V]

def inputWeight (st : HighGirthSelectionProgram.Input 1) : Fin 4 :=
  if st.zone then ⟨min st.cost 3, by omega⟩ else ⟨1, by decide⟩

def payload (st : HighGirthSelectionProgram.Input 1) : Bool × (Bool × Fin 4) :=
  (st.zone, (st.demand, inputWeight st))

def kernel {Out : Type} (P : BroadcastModel.Program V (Bool × Fin 4) Out) :
    BroadcastModel.Program V (HighGirthSelectionProgram.Input 1) (Bool × Out) :=
  .seq (.local fun _ _ st => payload st)
    (.seq (MaskProgram.execute P) (.local fun _ _ st => (st.2.active, st.1)))

def masked {b : Nat} (C : BitCode V b) (A L Δ r k t Q T s q M : Nat) (hQ : 0 < Q) :=
  kernel (GeneralFractionalBroadcast.program C A L Δ r k t Q T s 3 q M hQ)

def core {Out : Type} {b : Nat} (C : BitCode V b)
    (P : BroadcastModel.Program V (Bool × Fin 4) Out) : PortBroadcastModel.Program V Unit (Bool × Out) :=
  .seq (.local fun _ _ _ => (0 : Fin 1))
    (.seq (HighGirthInitializationProgram.program 1) (KT0Compiler.program C (kernel P)))

def program {b : Nat} (C : BitCode V b) (A L Δ r k t Q T s q M : Nat) (hQ : 0 < Q) :
    PortBroadcastModel.Program V Unit
      (Bool × Fin (PartialFractionalProgram.bound L Δ k Q T s q M + 1)) :=
  core C (GeneralFractionalBroadcast.program C A L Δ r k t Q T s 3 q M hQ)

theorem rounds {b : Nat} (C : BitCode V b) (A L Δ r k t Q T s q M : Nat) (hQ : 0 < Q) :
    (program C A L Δ r k t Q T s q M hQ).rounds =
      5 + (GeneralFractionalBroadcast.program C A L Δ r k t Q T s 3 q M hQ).rounds := by
  simp only [program, core, PortBroadcastModel.Program.rounds,
    HighGirthInitializationProgram.rounds, KT0Compiler.program_rounds,
    kernel, BroadcastModel.Program.rounds, MaskProgram.execute_rounds]
  omega

theorem maxBits {b : Nat} (C : BitCode V b) (A L Δ r k t Q T s q M : Nat) (hQ : 0 < Q) :
    (program C A L Δ r k t Q T s q M hQ).maxBits =
      max 1 (max b (GeneralFractionalBroadcast.program C A L Δ r k t Q T s 3 q M hQ).maxBits) := by
  simp only [program, core, PortBroadcastModel.Program.maxBits,
    HighGirthInitializationProgram.maxBits, KT0Compiler.program_maxBits,
    kernel, BroadcastModel.Program.maxBits, MaskProgram.execute_maxBits]
  omega

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inputWeight_correct (p : V → Fin 1) (v : V) :
    inputWeight (HighGirthSelectionProgram.input G p v) = HighGirthMaskedInput.weight G v := by
  classical
  by_cases hv : v ∈ HighGirthTransformation.zone G
  · have hc := (HighGirthCostBounds.candidate_cost_bounds G v hv).2.1
    apply Fin.ext
    simp [inputWeight, HighGirthSelectionProgram.input, HighGirthMaskedInput.weight, hv, min_eq_left hc]
  · simp [inputWeight, HighGirthSelectionProgram.input, HighGirthMaskedInput.weight, hv]

end Paper.HighGirthPhysicalSolver
#print axioms Paper.HighGirthPhysicalSolver.rounds
#print axioms Paper.HighGirthPhysicalSolver.maxBits
#print axioms Paper.HighGirthPhysicalSolver.inputWeight_correct
