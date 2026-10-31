import Paper.Endpoints.Girth.HighGirthAttachmentEdges
set_option maxHeartbeats 200000
namespace Paper.HighGirthInducedDegree

theorem residual_induced_degree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    ∀ v : {u // u ∈ Paper.HighGirthRounding.last G x},
      (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).degree v ≤ 2 := by
  classical
  intro v
  let U := Paper.HighGirthRounding.last G x
  have hr := Paper.HighGirthResidualDegree.residual_neighbor_degree G x v.val
    (Finset.mem_sdiff.mp v.property).1 (Or.inl v.property)
  have hsub : G.neighborFinset v.val ∩ U ⊆
      G.neighborFinset v.val ∩ Paper.HighGirthRounding.residual G x := by
    intro u hu
    obtain ⟨hun,huU⟩ := Finset.mem_inter.mp hu
    exact Finset.mem_inter.mpr ⟨hun,(Finset.mem_sdiff.mp huU).1⟩
  have hc : (G.neighborFinset v.val ∩ U).card ≤ 2 := (Finset.card_le_card hsub).trans hr
  have heq : ((G.induce (↑U : Set V)).neighborFinset v).map
      (.subtype (· ∈ (↑U : Set V))) = G.neighborFinset v.val ∩ U := by
    ext a
    simp
  have hcard := congrArg Finset.card heq
  have hdeg : (G.induce (↑U : Set V)).degree v = (G.neighborFinset v.val ∩ U).card := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hcard
  exact hdeg.trans_le hc

end Paper.HighGirthInducedDegree

#print axioms Paper.HighGirthInducedDegree.residual_induced_degree
