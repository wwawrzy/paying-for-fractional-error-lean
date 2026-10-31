import Paper.Endpoints.Girth.HighGirthFullProgram
namespace Paper.HighGirthFullOutput
variable {V : Type} [Fintype V] [DecidableEq V]
theorem encoded_output
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G) (x : V → Real) :
    Paper.HighGirthFullProgram.program.runEncoded G ports (Paper.HighGirthFullProgram.thresholdBit x) =
      fun v => decide (v ∈ Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x) := by
  classical
  change (fun v => let st := (Paper.HighGirthFullProgram.selectionState 1 2).runEncoded G ports ((Paper.HighGirthInitializationProgram.program 2).runEncoded G ports (Paper.HighGirthFullProgram.thresholdBit x)) v; !st.zone || st.first || st.high || st.last) = _
  rw [(Paper.HighGirthInitializationCorrect.encoded_initialization_correct G ports 2 (Paper.HighGirthFullProgram.thresholdBit x)).1,
    Paper.HighGirthFullProgram.selection_state_correct G ports 1 2 (by decide) (Paper.HighGirthFullProgram.thresholdBit x)]
  rw [← Paper.HighGirthFullProgram.output_threshold_eq G x]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [Paper.HighGirthSelectionProgram.expected, Paper.HighGirthTransformation.far, Paper.HighGirthRounding.output, or_assoc]
end Paper.HighGirthFullOutput
#print axioms Paper.HighGirthFullOutput.encoded_output
