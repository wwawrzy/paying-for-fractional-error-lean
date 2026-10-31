import Paper.Endpoints.Girth.HighGirthFullProgram
set_option maxHeartbeats 200000
namespace Paper.HighGirthThreeEndpoint

theorem coefficient_three_encoded
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G) (x : V → Real)
    (a : Rat) (ha : 1 ≤ a) (ha_upper : a < 8/7)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (hcap : ∀ v ∈ Paper.HighGirthTransformation.zone G, x v ≤ 1)
    (hden : Paper.Incidence.InducedDensityBound G (a : Real))
    (hsolver : Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x ≤
      (1 + (Paper.HighGirthSlackParameter.delta a : Real)) * Paper.HighGirthAuxiliary.number G) :
    0 < Paper.HighGirthSlackParameter.delta a ∧
    Paper.HighGirthSlackParameter.delta (17/15) = 5/8482 ∧
    (Finset.univ.filter (fun v =>
      (Paper.HighGirthFullProgram.program.runEncoded G ports
        (Paper.HighGirthFullProgram.thresholdBit x) v) = true)) = Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x ∧
    Paper.SevenFoundation.dominates G (Finset.univ.filter (fun v =>
      (Paper.HighGirthFullProgram.program.runEncoded G ports
        (Paper.HighGirthFullProgram.thresholdBit x) v) = true)) ∧
    ((Finset.univ.filter (fun v =>
      (Paper.HighGirthFullProgram.program.runEncoded G ports
        (Paper.HighGirthFullProgram.thresholdBit x) v) = true)).card : Real) ≤ 3 * Paper.SevenFoundation.fractionalNumber G ∧
    (Paper.HighGirthFullProgram.program (V := V)).rounds = 6 ∧
    (Paper.HighGirthFullProgram.program (V := V)).maxBits = 1 := by
  classical
    have hrun : Paper.HighGirthFullProgram.program.runEncoded G ports (Paper.HighGirthFullProgram.thresholdBit x) =
        fun v => decide (v ∈ Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x) := by
      change (fun v => let st := (Paper.HighGirthFullProgram.selectionState 1 2).runEncoded G ports ((Paper.HighGirthInitializationProgram.program 2).runEncoded G ports (Paper.HighGirthFullProgram.thresholdBit x)) v; !st.zone || st.first || st.high || st.last) = _
      rw [(Paper.HighGirthInitializationCorrect.encoded_initialization_correct G ports 2 (Paper.HighGirthFullProgram.thresholdBit x)).1,
        Paper.HighGirthFullProgram.selection_state_correct G ports 1 2 (by decide) (Paper.HighGirthFullProgram.thresholdBit x)]
      rw [← Paper.HighGirthFullProgram.output_threshold_eq G x]
      funext v
      apply Bool.eq_iff_iff.mpr
      simp [Paper.HighGirthSelectionProgram.expected, Paper.HighGirthTransformation.far, Paper.HighGirthRounding.output, or_assoc]
    have hset : Finset.univ.filter (fun v => Paper.HighGirthFullProgram.program.runEncoded G ports (Paper.HighGirthFullProgram.thresholdBit x) v = true) =
        Paper.HighGirthTransformation.far G ∪ Paper.HighGirthRounding.output G x := by
      ext v
      simp [hrun]
    obtain ⟨hd, h17, hD, hdom, hcard⟩ := Paper.HighGirthStaticThree.coefficient_three_static G x a ha ha_upper hx hcap hden hsolver
    refine ⟨hd, h17, hset, ?_, ?_, rfl, rfl⟩
    · rw [hset]
      exact hdom
    · rw [hset]
      exact hcard

end Paper.HighGirthThreeEndpoint

#print axioms Paper.HighGirthThreeEndpoint.coefficient_three_encoded
