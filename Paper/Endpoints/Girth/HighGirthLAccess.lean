import Paper.Endpoints.Girth.HighGirthUBall
set_option maxHeartbeats 200000
namespace Paper.HighGirthLAccess

theorem l_access_two_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (l : V) (hl : l ∈ Paper.HighGirthRounding.middle G x) :
    (Paper.HighGirthAccessSets.lAccessTwo G x l).card ≤ 4 := by
  classical
  let N := Paper.HighGirthAccessSets.neighborsU G x
  have hlR : l ∈ Paper.HighGirthRounding.residual G x := (Finset.mem_sdiff.mp hl).1
  have hlU : l ∉ Paper.HighGirthRounding.last G x :=
    fun hu => (Finset.mem_sdiff.mp hl).2 (Finset.mem_union_right _ hu)
  have hfirst : (N l).card ≤ 2 := by
    by_cases hz : (N l).card = 0
    · omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (N l).card by omega)
    obtain ⟨hpn, hpU⟩ := Finset.mem_inter.mp hp
    have hpAdj : G.Adj l p := (G.mem_neighborFinset l p).mp hpn
    have hr := Paper.HighGirthResidualDegree.residual_neighbor_degree G x l hlR (Or.inr ⟨p, hpU, hpAdj⟩)
    have hsub : N l ⊆ G.neighborFinset l ∩ Paper.HighGirthRounding.residual G x := by
      intro u hu
      obtain ⟨hun, huU⟩ := Finset.mem_inter.mp hu
      exact Finset.mem_inter.mpr ⟨hun, (Finset.mem_sdiff.mp huU).1⟩
    exact (Finset.card_le_card hsub).trans hr
  have hsecond : ∀ p ∈ N l, (N p).card ≤ 1 := by
    intro p hp
    obtain ⟨hpn, hpU⟩ := Finset.mem_inter.mp hp
    have hpAdj : G.Adj l p := (G.mem_neighborFinset l p).mp hpn
    have hr := Paper.HighGirthResidualDegree.residual_neighbor_degree G x p
      (Finset.mem_sdiff.mp hpU).1 (Or.inl hpU)
    have hlNotN : l ∉ N p := fun h => hlU (Finset.mem_inter.mp h).2
    have hsub : insert l (N p) ⊆ G.neighborFinset p ∩ Paper.HighGirthRounding.residual G x := by
      intro u hu
      rcases Finset.mem_insert.mp hu with heq | huN
      · subst u
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p l).mpr hpAdj.symm, hlR⟩
      · obtain ⟨hun, huU⟩ := Finset.mem_inter.mp huN
        exact Finset.mem_inter.mpr ⟨hun, (Finset.mem_sdiff.mp huU).1⟩
    have hc := (Finset.card_le_card hsub).trans hr
    rw [Finset.card_insert_of_notMem hlNotN] at hc
    omega
  have htwo : ((N l).biUnion N).card ≤ (N l).card := by
    calc
      _ ≤ ∑ p ∈ N l, (N p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ N l, 1 := Finset.sum_le_sum hsecond
      _ = (N l).card := by simp
  change (N l ∪ (N l).biUnion N).card ≤ 4
  have hc := Finset.card_union_le (N l) ((N l).biUnion N)
  omega

end Paper.HighGirthLAccess

#print axioms Paper.HighGirthLAccess.l_access_two_card
