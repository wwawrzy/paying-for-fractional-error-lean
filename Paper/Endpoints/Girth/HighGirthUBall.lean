import Paper.Endpoints.Girth.HighGirthAccessSets
set_option maxHeartbeats 200000
namespace Paper.HighGirthUBall

theorem u_ball_two_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (a : V) (ha : a ∈ Paper.HighGirthRounding.last G x) :
    (Paper.HighGirthAccessSets.uBallTwo G x a).card ≤ 5 := by
  classical
  let N := Paper.HighGirthAccessSets.neighborsU G x
  have hdegree : ∀ v ∈ Paper.HighGirthRounding.last G x, (N v).card ≤ 2 := by
    intro v hv
    have hr := Paper.HighGirthResidualDegree.residual_neighbor_degree G x v
      (Finset.mem_sdiff.mp hv).1 (Or.inl hv)
    have hsub : N v ⊆ G.neighborFinset v ∩ Paper.HighGirthRounding.residual G x := by
      intro u hu
      obtain ⟨hun, huU⟩ := Finset.mem_inter.mp hu
      exact Finset.mem_inter.mpr ⟨hun, (Finset.mem_sdiff.mp huU).1⟩
    exact (Finset.card_le_card hsub).trans hr
  have hNa := hdegree a ha
  have hsecond : ∀ p ∈ N a, (N p \ {a}).card ≤ 1 := by
    intro p hp
    obtain ⟨hpa, hpU⟩ := Finset.mem_inter.mp hp
    have haN : a ∈ N p := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p a).mpr
      (((G.mem_neighborFinset a p).mp hpa).symm), ha⟩
    have hsplit := Finset.card_sdiff_add_card_inter (N p) {a}
    have hinter : N p ∩ {a} = {a} :=
      Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr haN)
    rw [hinter, Finset.card_singleton] at hsplit
    have hpdeg := hdegree p hpU
    omega
  have htwo : ((N a).biUnion (fun p => N p \ {a})).card ≤ (N a).card := by
    calc
      _ ≤ ∑ p ∈ N a, (N p \ {a}).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ N a, 1 := Finset.sum_le_sum hsecond
      _ = (N a).card := by simp
  change (insert a (N a ∪ (N a).biUnion (fun p => N p \ {a}))).card ≤ 5
  have hUnion := Finset.card_union_le (N a) ((N a).biUnion (fun p => N p \ {a}))
  have hInsert := Finset.card_insert_le a (N a ∪ (N a).biUnion (fun p => N p \ {a}))
  omega

end Paper.HighGirthUBall

#print axioms Paper.HighGirthUBall.u_ball_two_card
