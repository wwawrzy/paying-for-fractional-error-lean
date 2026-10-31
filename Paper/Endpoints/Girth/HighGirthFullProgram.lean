import Paper.Endpoints.Girth.HighGirthInitializationCorrect

/-! Composition of initialization and rounding, with local threshold bits
for arbitrary real input. No numeric value is sent as a message. -/
namespace Paper.HighGirthFullProgram
open PortBroadcastModel SevenFoundation
variable {V : Type}

def selectionState (D N : Nat) : Program V (HighGirthSelectionProgram.Input N) HighGirthSelectionProgram.State :=
  .seq (HighGirthSelectionProgram.start D N)
    (.seq HighGirthSelectionProgram.removeFirst
      (.seq HighGirthSelectionProgram.selectHigh HighGirthSelectionProgram.removeHigh))

def program : Program V (Fin 2) Bool :=
  .seq (HighGirthInitializationProgram.program 2)
    (.seq (selectionState 1 2)
      (.local fun _ _ st => !st.zone || st.first || st.high || st.last))

theorem rounds : (program (V := V)).rounds = 6 := rfl

theorem maxBits : (program (V := V)).maxBits = 1 := rfl

noncomputable def thresholdBit (x : V → Real) (v : V) : Fin 2 := by
  classical
  exact if (1 : Real)/2 < x v then ⟨1, by decide⟩ else ⟨0, by decide⟩

theorem thresholdBit_correct (x : V → Real) (v : V) :
    (1 : Real)/2 < ((thresholdBit x v).val : Real) / 1 ↔ (1 : Real)/2 < x v := by
  classical
  by_cases h : (1 : Real)/2 < x v
  · simp only [thresholdBit, if_pos h]
    norm_num <;> linarith
  · simp only [thresholdBit, if_neg h]
    norm_num <;> linarith

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem selection_state_correct (ports : Numbering G)
    (D N : Nat) (hD : 0 < D) (p : V → Fin N) :
    (selectionState D N).runEncoded G ports (HighGirthSelectionProgram.input G p) =
      HighGirthSelectionProgram.expected G (fun v => ((p v).val : Real)/D) 3 := by
  classical
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
  change Paper.HighGirthSelectionProgram.removeHigh.runEncoded G ports
    (Paper.HighGirthSelectionProgram.selectHigh.runEncoded G ports
      (Paper.HighGirthSelectionProgram.removeFirst.runEncoded G ports
        ((Paper.HighGirthSelectionProgram.start D N).runEncoded G ports
          (Paper.HighGirthSelectionProgram.input G p)))) = _
  rw [Paper.HighGirthSelectionProgram.start_correct G ports D N hD p, h1, h2, h3]

theorem first_threshold_eq (x : V → Real) :
    HighGirthRounding.first G (fun v => ((thresholdBit x v).val : Real)/1) =
      HighGirthRounding.first G x := by
  classical
  ext v
  simp only [HighGirthRounding.first, Finset.mem_filter, thresholdBit_correct]

theorem output_threshold_eq (x : V → Real) :
    HighGirthRounding.output G (fun v => ((thresholdBit x v).val : Real)/1) =
      HighGirthRounding.output G x := by
  simp only [HighGirthRounding.output, HighGirthRounding.high, HighGirthRounding.hits,
    HighGirthRounding.last, HighGirthRounding.residual, first_threshold_eq]
  rfl

end Paper.HighGirthFullProgram
#print axioms Paper.HighGirthFullProgram.rounds
#print axioms Paper.HighGirthFullProgram.maxBits
#print axioms Paper.HighGirthFullProgram.thresholdBit_correct
#print axioms Paper.HighGirthFullProgram.selection_state_correct
#print axioms Paper.HighGirthFullProgram.first_threshold_eq
#print axioms Paper.HighGirthFullProgram.output_threshold_eq
