import Paper.Endpoints.Girth.HighGirthFreeInner
set_option maxHeartbeats 200000
namespace Paper.HighGirthFreeAccess

theorem free_short_access
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K)
    (u : V) (huK : u ∈ Paper.HighGirthFreePaths.members G x K) :
    let U := Paper.HighGirthRounding.last G x
    let H := G.induce (↑U : Set V)
    (∃ b ∈ Paper.HighGirthTransformation.branches G ∩ Paper.HighGirthFreePaths.members G x K,
      ∃ hb : b ∈ U, ∃ hu : u ∈ U, ∃ q : H.Walk ⟨u,hu⟩ ⟨b,hb⟩,
        q.IsPath ∧ q.length ≤ 2 ∧ ∀ a ∈ q.support, a.val ∈ Paper.HighGirthFreePaths.members G x K) ∨
    (∃ b ∈ Paper.HighGirthAttachments.vertices G x ∩ Paper.HighGirthFreePaths.members G x K,
      ∃ hb : b ∈ U, ∃ hu : u ∈ U, ∃ q : H.Walk ⟨u,hu⟩ ⟨b,hb⟩,
        q.IsPath ∧ q.length ≤ 1 ∧ ∀ a ∈ q.support, a.val ∈ Paper.HighGirthFreePaths.members G x K) := by
  classical
    dsimp only
    obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp huK).2
    let U := Paper.HighGirthRounding.last G x
    let H := G.induce (↑U : Set V)
    have hmem : ∀ a : {v // v ∈ U}, H.connectedComponentMk a = H.connectedComponentMk ⟨u,huU⟩ →
        a.val ∈ Paper.HighGirthFreePaths.members G x K := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.property,ha.trans huComp⟩
    rcases Paper.HighGirthComponentAccess.residual_component_access G x u huU with
      ⟨b,hbB,hbU,q,hq,hlen,hs⟩ | ⟨b,hbA,hbU,q,hq,hlen,hs⟩ | ⟨l,hl,w,hw,hlen,hs⟩
    · left
      have hbK := hmem ⟨b,hbU⟩ (hs _ q.end_mem_support)
      exact ⟨b,Finset.mem_inter.mpr ⟨hbB,hbK⟩,hbU,huU,q,hq,hlen,fun a ha => hmem a (hs a ha)⟩
    · right
      have hbK := hmem ⟨b,hbU⟩ (hs _ q.end_mem_support)
      exact ⟨b,Finset.mem_inter.mpr ⟨hbA,hbK⟩,hbU,huU,q,hq,hlen,fun a ha => hmem a (hs a ha)⟩
    · have hlU : l ∉ U := fun h => (Finset.mem_sdiff.mp hl).2 (Finset.mem_union_right _ h)
      have hul : u ≠ l := fun heq => hlU (heq ▸ huU)
      have hn : ¬ w.Nil := SimpleGraph.Walk.not_nil_of_ne hul
      have hadj : G.Adj w.penultimate l := SimpleGraph.Walk.adj_penultimate hn
      have hpSupport : w.penultimate ∈ w.support :=
        List.mem_of_mem_dropLast (SimpleGraph.Walk.penultimate_mem_dropLast_support hn)
      obtain ⟨hpU,hpComp⟩ := hs _ hpSupport hadj.ne
      have hpK := hmem ⟨w.penultimate,hpU⟩ hpComp
      exact False.elim (hfree _ hpK l hl hadj)

end Paper.HighGirthFreeAccess

#print axioms Paper.HighGirthFreeAccess.free_short_access
