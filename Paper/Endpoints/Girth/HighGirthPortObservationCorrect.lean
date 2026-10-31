import Paper.Endpoints.Girth.HighGirthPortObservation

namespace Paper.HighGirthPortObservationCorrect
theorem encoded_closed_observation_correct
    {V S : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ports : Paper.PortBroadcastModel.Numbering G)
    (flag : S → Bool) (update : V → Nat → S → Nat → S) (st : V → S)
    (A : Finset V) (hf : ∀ v, flag (st v) = decide (v ∈ A)) :
    (Paper.HighGirthPortObservation.program flag update).runEncoded G ports st =
      (fun v => update v (G.degree v) (st v) ((Paper.SevenFoundation.closed G v ∩ A).card)) ∧
    (Paper.HighGirthPortObservation.program flag update).rounds = 1 ∧
    (Paper.HighGirthPortObservation.program flag update).maxBits = 1 := by
  classical
  refine ⟨?_,rfl,rfl⟩
  rw [Paper.PortBroadcastModel.Program.runEncoded_eq_run]
  funext v
  change update v (G.degree v) (st v)
      ((if flag (st v) then 1 else 0) +
        (Finset.univ.filter (fun i : Fin (G.degree v) => flag (st (ports v i).val) = true)).card) = _
  apply congrArg (update v (G.degree v) (st v))
  have hfilter : (Finset.univ.filter (fun i : Fin (G.degree v) => flag (st (ports v i).val) = true)) =
      Finset.univ.filter (fun i : Fin (G.degree v) => (ports v i).val ∈ A) := by
    ext i
    simp [hf]
  rw [hfilter,Paper.HighGirthPortObservation.port_neighbor_count G ports A v]
  have hown : (if flag (st v) then 1 else 0) = (if v ∈ A then 1 else 0) := by simp [hf]
  rw [hown]
  have hclosed : Paper.SevenFoundation.closed G v = insert v (G.neighborFinset v) := by
    ext u
    simp [Paper.SevenFoundation.closed,SimpleGraph.mem_neighborFinset]
  rw [hclosed]
  by_cases hv : v ∈ A
  · rw [if_pos hv,Finset.insert_inter_of_mem hv]
    have hn : v ∉ G.neighborFinset v ∩ A := by simp
    rw [Finset.card_insert_of_notMem hn]
    omega
  · rw [if_neg hv,Finset.insert_inter_of_notMem hv]
    omega

end Paper.HighGirthPortObservationCorrect
#print axioms Paper.HighGirthPortObservationCorrect.encoded_closed_observation_correct
