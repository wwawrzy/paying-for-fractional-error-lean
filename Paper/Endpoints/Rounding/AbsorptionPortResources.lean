import Paper.Endpoints.Components.ComponentReplacementProgram
import Paper.Averaging.Tasks.KT0Compiler
set_option maxHeartbeats 200000
namespace Paper.AbsorptionPortResources

theorem absorption_port_resources
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G)
    (a B K : Nat) (hB : 1 ≤ B) {bits : Nat}
    (ids : Paper.BroadcastModel.BitCode V bits)
    (A0 : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (n cid C : Nat)
    (hids : bits ≤ cid * Nat.clog 2 (n + 2))
    (hA0 : A0.maxBits ≤ C * Nat.clog 2 (n + 2)) :
    let Q := Paper.ComponentReplacementProgram.program A0
      (Paper.SmallComponentProgram.program ids a B K hB)
    let P := Paper.KT0Compiler.program ids Q
    P.runEncoded G ports s = Q.runEncoded G s ∧
      P.rounds = 1 + (A0.rounds + Paper.SmallComponentProgram.roundBound a K) ∧
      P.maxBits ≤ max cid (max C (Paper.SmallComponentProgram.messageConstant a B K cid)) *
        Nat.clog 2 (n + 2) := by
  dsimp only
  refine ⟨Paper.KT0Compiler.program_encoded_correct G ids _ ports s, ?_, ?_⟩
  · rw [Paper.KT0Compiler.program_rounds, Paper.ComponentReplacementProgram.rounds,
      Paper.SmallComponentProgram.rounds]
  · apply Paper.KT0Compiler.logarithmic_bits ids _ n cid
      (max C (Paper.SmallComponentProgram.messageConstant a B K cid)) hids
    rw [Paper.ComponentReplacementProgram.maxBits]
    have hs := Paper.SmallComponentProgram.logarithmic_bits ids a B K hB n cid hids
    exact (max_le_max hA0 hs).trans_eq (by rw [max_mul_mul_right])

end Paper.AbsorptionPortResources

#print axioms Paper.AbsorptionPortResources.absorption_port_resources
