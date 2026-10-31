import Paper.Endpoints.Girth.HighGirthSelectionProgram
namespace Paper.HighGirthSelectionCorrect
theorem encoded_three_round_selection_correct
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G)
    (D N : Nat) (hD : 0 < D) (p : V → Fin N) :
    (Paper.HighGirthSelectionProgram.program D N).runEncoded G ports
        (Paper.HighGirthSelectionProgram.input G p) =
      (fun v => decide (v ∈ Paper.HighGirthRounding.output G
        (fun u => ((p u).val : Real) / D))) ∧
    (Paper.HighGirthSelectionProgram.program (V := V) D N).rounds = 3 ∧
    (Paper.HighGirthSelectionProgram.program (V := V) D N).maxBits = 1 := by
  classical
  refine ⟨?_, rfl, rfl⟩
  let x : V → Real := fun u => ((p u).val : Real) / D
  have h1 : Paper.HighGirthSelectionProgram.removeFirst.runEncoded G ports (Paper.HighGirthSelectionProgram.expected G x 0) = Paper.HighGirthSelectionProgram.expected G x 1 := by
    rw [Paper.HighGirthSelectionProgram.removeFirst, (Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct G ports _ _ _
      (Paper.HighGirthRounding.first G x) (by intro v; rfl)).1]
    funext v
    apply Paper.HighGirthSelectionProgram.State.ext <;> try rfl
    apply Bool.eq_iff_iff.mpr
    have hz : Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.first G x = ∅ ↔ v ∉ Paper.SevenFoundation.covered G (Paper.HighGirthRounding.first G x) := by
      rw [← Finset.card_eq_zero]
      exact Paper.HighGirthSelectionProgram.count_zero_iff G _ v
    simp [Paper.HighGirthSelectionProgram.expected, Paper.HighGirthRounding.residual, hz]
  have h2 : Paper.HighGirthSelectionProgram.selectHigh.runEncoded G ports (Paper.HighGirthSelectionProgram.expected G x 1) = Paper.HighGirthSelectionProgram.expected G x 2 := by
    rw [Paper.HighGirthSelectionProgram.selectHigh, (Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct G ports _ _ _
      (Paper.HighGirthRounding.residual G x) (by intro v; rfl)).1]
    funext v
    apply Paper.HighGirthSelectionProgram.State.ext <;> try rfl
    apply Bool.eq_iff_iff.mpr
    simp [Paper.HighGirthSelectionProgram.expected, Paper.HighGirthRounding.high, Paper.HighGirthRounding.hits, and_assoc]
  have h3 : Paper.HighGirthSelectionProgram.removeHigh.runEncoded G ports (Paper.HighGirthSelectionProgram.expected G x 2) = Paper.HighGirthSelectionProgram.expected G x 3 := by
    rw [Paper.HighGirthSelectionProgram.removeHigh, (Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct G ports _ _ _
      (Paper.HighGirthRounding.high G x) (by intro v; rfl)).1]
    funext v
    apply Paper.HighGirthSelectionProgram.State.ext <;> try rfl
    apply Bool.eq_iff_iff.mpr
    have hz : Paper.SevenFoundation.closed G v ∩ Paper.HighGirthRounding.high G x = ∅ ↔ v ∉ Paper.SevenFoundation.covered G (Paper.HighGirthRounding.high G x) := by
      rw [← Finset.card_eq_zero]
      exact Paper.HighGirthSelectionProgram.count_zero_iff G _ v
    simp [Paper.HighGirthSelectionProgram.expected, Paper.HighGirthRounding.last, hz]
  change (fun v => let st := Paper.HighGirthSelectionProgram.removeHigh.runEncoded G ports   (Paper.HighGirthSelectionProgram.selectHigh.runEncoded G ports (Paper.HighGirthSelectionProgram.removeFirst.runEncoded G ports     ((Paper.HighGirthSelectionProgram.start D N).runEncoded G ports (Paper.HighGirthSelectionProgram.input G p)))) v;   st.first || st.high || st.last) = _
  rw [Paper.HighGirthSelectionProgram.start_correct G ports D N hD p, h1, h2, h3]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [Paper.HighGirthSelectionProgram.expected, Paper.HighGirthRounding.output, x, or_assoc]
end Paper.HighGirthSelectionCorrect
#print axioms Paper.HighGirthSelectionCorrect.encoded_three_round_selection_correct
