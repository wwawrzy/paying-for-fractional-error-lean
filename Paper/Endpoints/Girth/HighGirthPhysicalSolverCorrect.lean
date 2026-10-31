import Paper.Endpoints.Girth.HighGirthPhysicalSolver
namespace Paper.HighGirthPhysicalSolverCorrect
open HighGirthPhysicalSolver
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem kernel_correct {Out : Type} (P : BroadcastModel.Program V (Bool × Fin 4) Out) :
    (kernel P).run G (HighGirthSelectionProgram.input G (fun _ => (0 : Fin 1))) =
      fun v => (decide (v ∈ HighGirthTransformation.zone G),
        P.run (HighGirthMaskedInput.graph G)
          (fun u => (decide (u ∈ HighGirthTransformation.demands G), HighGirthMaskedInput.weight G u)) v) := by
  change (fun v => let st := (MaskProgram.execute P).run G (fun u => payload (HighGirthSelectionProgram.input G (fun _ => (0 : Fin 1)) u)) v; (st.2.active, st.1)) = _
  have he : (fun u => payload (HighGirthSelectionProgram.input G (fun _ => (0 : Fin 1)) u)) =
      (fun u => (decide (u ∈ HighGirthTransformation.zone G),
        (decide (u ∈ HighGirthTransformation.demands G), HighGirthMaskedInput.weight G u))) := by
    funext u
    change (decide (u ∈ HighGirthTransformation.zone G),
      (decide (u ∈ HighGirthTransformation.demands G), inputWeight (HighGirthSelectionProgram.input G (fun _ => (0 : Fin 1)) u))) = _
    rw [inputWeight_correct]
  rw [he, MaskProgramCorrect.execute_correct G P (HighGirthTransformation.zone G)]
  funext v
  dsimp only
  rw [MaskProgramCorrect.active]
  rfl

theorem core_correct {Out : Type} {b : Nat} (C : BroadcastModel.BitCode V b)
    (P : BroadcastModel.Program V (Bool × Fin 4) Out) (ports : PortBroadcastModel.Numbering G) :
    (core C P).runEncoded G ports (fun _ => ()) =
      fun v => (decide (v ∈ HighGirthTransformation.zone G),
        P.runEncoded (HighGirthMaskedInput.graph G)
          (fun u => (decide (u ∈ HighGirthTransformation.demands G), HighGirthMaskedInput.weight G u)) v) := by
  change (KT0Compiler.program C (kernel P)).runEncoded G ports
    ((HighGirthInitializationProgram.program 1).runEncoded G ports (fun _ => (0 : Fin 1))) = _
  rw [(HighGirthInitializationCorrect.encoded_initialization_correct G ports 1 (fun _ => (0 : Fin 1))).1]
  rw [KT0Compiler.program_encoded_correct G C (kernel P) ports]
  simpa only [BroadcastModel.Program.runEncoded_eq_run] using kernel_correct G P

theorem physical_solver_encoded_correct
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G)
    {b : Nat} (C : Paper.BroadcastModel.BitCode V b)
    (A L Δ r k t Q T s q M : Nat) (hQ : 0 < Q) :
    (Paper.HighGirthPhysicalSolver.program C A L Δ r k t Q T s q M hQ).runEncoded G ports (fun _ => ()) =
      (fun v => (decide (v ∈ Paper.HighGirthTransformation.zone G),
        (Paper.GeneralFractionalBroadcast.program C A L Δ r k t Q T s 3 q M hQ).runEncoded
          (Paper.HighGirthMaskedInput.graph G)
          (fun u => (decide (u ∈ Paper.HighGirthTransformation.demands G),
            Paper.HighGirthMaskedInput.weight G u)) v)) := by
  exact core_correct G C (GeneralFractionalBroadcast.program C A L Δ r k t Q T s 3 q M hQ) ports
end Paper.HighGirthPhysicalSolverCorrect
#print axioms Paper.HighGirthPhysicalSolverCorrect.kernel_correct
#print axioms Paper.HighGirthPhysicalSolverCorrect.core_correct
#print axioms Paper.HighGirthPhysicalSolverCorrect.physical_solver_encoded_correct
