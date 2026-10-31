import Paper.Endpoints.Components.ComponentReplacementProgram

namespace Paper.ComponentReplacementOutputSet

theorem replacement_output_set
    {V In : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A0 : Paper.BroadcastModel.Program V In Bool)
    (A1 : Paper.BroadcastModel.Program V In (Bool × Bool))
    (s : V → In) :
    let D0 := Finset.univ.filter (fun v => A0.runEncoded G s v = true)
    let D1 := Finset.univ.filter (fun v => (A1.runEncoded G s v).2 = true)
    let D := Finset.univ.filter (fun v =>
      (Paper.ComponentReplacementProgram.program A0 A1).runEncoded G s v = true)
    D = (D0 ∪ D1).filter (fun v =>
      if (A1.runEncoded G s v).1 then v ∈ D1 else v ∈ D0) := by
  dsimp only
  rw [Paper.ComponentReplacementProgram.run_encoded]
  apply Finset.ext
  intro v
  cases h : (A1.runEncoded G s v).1 <;> simp [h]
  · exact fun ha => Or.inl ha
  · exact fun ha => Or.inr ha

end Paper.ComponentReplacementOutputSet

#print axioms Paper.ComponentReplacementOutputSet.replacement_output_set
