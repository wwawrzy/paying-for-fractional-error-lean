import Paper.Endpoints.Girth.HighGirthInitializationProgram
namespace Paper.HighGirthInitializationCorrect
theorem encoded_initialization_correct
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G)
    (N : Nat) (p : V → Fin N) :
    (Paper.HighGirthInitializationProgram.program N).runEncoded G ports p =
      Paper.HighGirthSelectionProgram.input G p ∧
    (Paper.HighGirthInitializationProgram.program (V := V) N).rounds = 3 ∧
    (Paper.HighGirthInitializationProgram.program (V := V) N).maxBits = 1 := by
  classical
  refine ⟨?_,rfl,rfl⟩
  have h1 : (Paper.HighGirthInitializationProgram.findNear N).runEncoded G ports (Paper.HighGirthInitializationProgram.expected G p 0) = Paper.HighGirthInitializationProgram.expected G p 1 := by
    rw [Paper.HighGirthInitializationProgram.findNear, (Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct G ports _ _ _ (Paper.HighGirthTransformation.branches G) (by intro v; rfl)).1]
    funext v
    have hn : (Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.branches G).Nonempty ↔ v ∈ Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.branches G) := by
      rw [← Finset.card_pos]
      exact Paper.HighGirthInitializationProgram.count_pos_iff G _ v
    apply Paper.HighGirthInitializationProgram.State.ext <;> try rfl
    simp [Paper.HighGirthInitializationProgram.expected, hn]
  have h2 : (Paper.HighGirthInitializationProgram.findZone N).runEncoded G ports (Paper.HighGirthInitializationProgram.expected G p 1) = Paper.HighGirthInitializationProgram.expected G p 2 := by
    rw [Paper.HighGirthInitializationProgram.findZone, (Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct G ports _ _ _ (Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.branches G)) (by intro v; rfl)).1]
    funext v
    have hn : (Paper.SevenFoundation.closed G v ∩ Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.branches G)).Nonempty ↔ v ∈ Paper.HighGirthTransformation.zone G := by
      rw [← Finset.card_pos]
      exact Paper.HighGirthInitializationProgram.count_pos_iff G _ v
    apply Paper.HighGirthInitializationProgram.State.ext <;> try rfl
    all_goals simp [Paper.HighGirthInitializationProgram.expected, Paper.HighGirthTransformation.far, hn]
  have h3 : (Paper.HighGirthInitializationProgram.findDemandCost N).runEncoded G ports (Paper.HighGirthInitializationProgram.expected G p 2) = Paper.HighGirthInitializationProgram.expected G p 3 := by
    rw [Paper.HighGirthInitializationProgram.findDemandCost, (Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct G ports _ _ _ (Paper.HighGirthTransformation.far G) (by intro v; rfl)).1]
    funext v
    have hz : Paper.SevenFoundation.closed G v ∩ Paper.HighGirthTransformation.far G = ∅ ↔ v ∉ Paper.SevenFoundation.covered G (Paper.HighGirthTransformation.far G) := by
      rw [← Finset.card_eq_zero]
      exact Paper.HighGirthSelectionProgram.count_zero_iff G _ v
    apply Paper.HighGirthInitializationProgram.State.ext <;> try rfl
    · apply Bool.eq_iff_iff.mpr
      simp [Paper.HighGirthInitializationProgram.expected, Paper.HighGirthTransformation.demands, hz]
    · simp [Paper.HighGirthInitializationProgram.expected, Paper.HighGirthTransformation.candidateCost, Paper.HighGirthInitializationProgram.closed_count]
  change (fun v => let st := (Paper.HighGirthInitializationProgram.findDemandCost N).runEncoded G ports ((Paper.HighGirthInitializationProgram.findZone N).runEncoded G ports ((Paper.HighGirthInitializationProgram.findNear N).runEncoded G ports ((Paper.HighGirthInitializationProgram.start N).runEncoded G ports p))) v; (⟨st.zone, st.demand, st.cost, st.numerator⟩ : Paper.HighGirthSelectionProgram.Input N)) = _
  rw [Paper.HighGirthInitializationProgram.start_correct G ports N p, h1, h2, h3]
  rfl
end Paper.HighGirthInitializationCorrect
#print axioms Paper.HighGirthInitializationCorrect.encoded_initialization_correct
