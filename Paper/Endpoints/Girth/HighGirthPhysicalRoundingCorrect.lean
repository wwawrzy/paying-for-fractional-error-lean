import Paper.Endpoints.Girth.HighGirthPhysicalRounding
import Paper.Endpoints.Girth.HighGirthFullOutput
set_option maxHeartbeats 200000
namespace Paper.HighGirthPhysicalRoundingCorrect

theorem physical_rounding_encoded_correct
    {V : Type} [Fintype V] [LinearOrder V] {N b : Nat}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G)
    (C : Paper.BroadcastModel.BitCode V b)
    (P : Paper.BroadcastModel.Program V (Bool × Fin 4) (Fin N))
    (D : Nat) (hD : 0 < D) :
    let raw := fun v => (((P.runEncoded (Paper.HighGirthMaskedInput.graph G)
      (fun u => (decide (u ∈ Paper.HighGirthTransformation.demands G),
        Paper.HighGirthMaskedInput.weight G u)) v).val : Real) / D)
    let x := Paper.HighGirthMaskedInput.capped G raw
    (Paper.HighGirthPhysicalRounding.program C P D).runEncoded G ports (fun _ => ()) =
      (fun v => decide (v ∈ Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x)) ∧
    (Paper.HighGirthPhysicalRounding.program C P D).rounds = 11 + P.rounds ∧
    (Paper.HighGirthPhysicalRounding.program C P D).maxBits = max 1 (max b P.maxBits) := by
  classical
    dsimp only
    refine ⟨?_, Paper.HighGirthPhysicalRounding.rounds C P D, Paper.HighGirthPhysicalRounding.maxBits C P D⟩
    change Paper.HighGirthFullProgram.program.runEncoded G ports
      (fun v => Paper.HighGirthPhysicalRounding.squeeze D
        ((Paper.HighGirthPhysicalSolver.core C P).runEncoded G ports (fun _ => ()) v)) = _
    rw [Paper.HighGirthPhysicalSolverCorrect.core_correct G C P ports]
    rw [Paper.HighGirthPhysicalRounding.squeeze_correct G
      (fun v => P.runEncoded (Paper.HighGirthMaskedInput.graph G)
        (fun u => (decide (u ∈ Paper.HighGirthTransformation.demands G), Paper.HighGirthMaskedInput.weight G u)) v) D hD]
    exact Paper.HighGirthFullOutput.encoded_output G ports _

end Paper.HighGirthPhysicalRoundingCorrect

#print axioms Paper.HighGirthPhysicalRoundingCorrect.physical_rounding_encoded_correct
