import Paper.TotalDomination.HighGirthFreeComponents
set_option maxHeartbeats 200000
namespace Paper.TotalDomination.HighGirthSetup

theorem free_short_access
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree K)
    (u : V) (huK : u ∈ componentMembers G x identifier hfree K) :
    let U := core G x identifier hfree
    let H := G.induce (↑U : Set V)
    (∃ b ∈ B G ∩ componentMembers G x identifier hfree K,
      ∃ hb : b ∈ U, ∃ hu : u ∈ U, ∃ q : H.Walk ⟨u,hu⟩ ⟨b,hb⟩,
        q.IsPath ∧ q.length ≤ 3 ∧ ∀ a ∈ q.support, a.val ∈ componentMembers G x identifier hfree K) ∨
    (∃ b ∈ attachments G x identifier hfree ∩ componentMembers G x identifier hfree K,
      ∃ hb : b ∈ U, ∃ hu : u ∈ U, ∃ q : H.Walk ⟨u,hu⟩ ⟨b,hb⟩,
        q.IsPath ∧ q.length ≤ 2 ∧ ∀ a ∈ q.support, a.val ∈ componentMembers G x identifier hfree K) := by
  classical
    dsimp only
    obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp huK).2
    let U := core G x identifier hfree
    let H := G.induce (↑U : Set V)
    have hmem : ∀ a : {v // v ∈ U}, H.connectedComponentMk a = H.connectedComponentMk ⟨u,huU⟩ →
        a.val ∈ componentMembers G x identifier hfree K := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.property,ha.trans huComp⟩
    rcases component_access G x identifier hfree u huU with
      ⟨b,hbB,hbU,q,hq,hlen,hs⟩ | ⟨b,hbA,hbU,q,hq,hlen,hs⟩ | ⟨l,hl,w,hw,hlen,hs⟩
    · left
      have hbK := hmem ⟨b,hbU⟩ (hs _ q.end_mem_support)
      exact ⟨b,Finset.mem_inter.mpr ⟨hbB,hbK⟩,hbU,huU,q,hq,hlen,fun a ha => hmem a (hs a ha)⟩
    · right
      have hbK := hmem ⟨b,hbU⟩ (hs _ q.end_mem_support)
      exact ⟨b,Finset.mem_inter.mpr ⟨hbA,hbK⟩,hbU,huU,q,hq,hlen,fun a ha => hmem a (hs a ha)⟩
    · have hlU : l ∉ U := served_not_core G x identifier hfree hl
      have hul : u ≠ l := fun heq => hlU (heq ▸ huU)
      have hn : ¬ w.Nil := SimpleGraph.Walk.not_nil_of_ne hul
      have hadj : G.Adj w.penultimate l := SimpleGraph.Walk.adj_penultimate hn
      have hpSupport : w.penultimate ∈ w.support :=
        List.mem_of_mem_dropLast (SimpleGraph.Walk.penultimate_mem_dropLast_support hn)
      obtain ⟨hpU,hpComp⟩ := hs _ hpSupport hadj.ne
      have hpK := hmem ⟨w.penultimate,hpU⟩ hpComp
      exact False.elim ((hC _ hpK).2 ((Paper.TotalDomination.mem_neighbors G).mpr ⟨l,hl,hadj⟩))

end Paper.TotalDomination.HighGirthSetup

#print axioms Paper.TotalDomination.HighGirthSetup.free_short_access
