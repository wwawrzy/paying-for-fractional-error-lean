import Paper.Endpoints.Girth.HighGirthExteriorComponent
set_option maxHeartbeats 200000
namespace Paper.HighGirthComponentAccess

theorem residual_component_access
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (u : V) (hu : u ∈ Paper.HighGirthRounding.last G x) :
    let U := Paper.HighGirthRounding.last G x
    let H := G.induce (↑U : Set V)
    (∃ b ∈ Paper.HighGirthTransformation.branches G, ∃ hb : b ∈ U,
      ∃ q : H.Walk ⟨u, hu⟩ ⟨b, hb⟩, q.IsPath ∧ q.length ≤ 2 ∧
        ∀ a ∈ q.support, H.connectedComponentMk a = H.connectedComponentMk ⟨u, hu⟩) ∨
    (∃ b ∈ Paper.HighGirthAttachments.vertices G x, ∃ hb : b ∈ U,
      ∃ q : H.Walk ⟨u, hu⟩ ⟨b, hb⟩, q.IsPath ∧ q.length ≤ 1 ∧
        ∀ a ∈ q.support, H.connectedComponentMk a = H.connectedComponentMk ⟨u, hu⟩) ∨
    (∃ l ∈ Paper.HighGirthRounding.middle G x, ∃ w : G.Walk u l,
      w.IsPath ∧ w.length ≤ 2 ∧ ∀ a ∈ w.support, a ≠ l → ∃ ha : a ∈ U,
        H.connectedComponentMk ⟨a, ha⟩ = H.connectedComponentMk ⟨u, hu⟩) := by
  classical
    dsimp only
    let U := Paper.HighGirthRounding.last G x
    let H := G.induce (↑U : Set V)
    have hcomp : ∀ {a b : {v // v ∈ U}} (q : H.Walk a b),
        ∀ v ∈ q.support, H.connectedComponentMk v = H.connectedComponentMk a := by
      intro a b q v hv
      exact (SimpleGraph.ConnectedComponent.sound (q.takeUntil v hv).reachable).symm
    rcases Paper.HighGirthResidualPaths.residual_short_paths G x u hu with
      ⟨b, hb, w, hw, hlen, hs⟩ | ⟨b, hb, w, hw, hlen, hs⟩ | ⟨l, hl, w, hw, hlen, hs⟩
    · left
      have hbU := (Finset.mem_inter.mp hb).2
      obtain ⟨q, hq, hqlen, hmap⟩ := Paper.HighGirthInducedPaths.lift_internal_path G U u b hu hbU w hw hs
      exact ⟨b, (Finset.mem_inter.mp hb).1, hbU, q, hq, hqlen.trans_le hlen, hcomp q⟩
    · right
      left
      have hbU := (Finset.mem_filter.mp hb).1
      obtain ⟨q, hq, hqlen, hmap⟩ := Paper.HighGirthInducedPaths.lift_internal_path G U u b hu hbU w hw hs
      exact ⟨b, hb, hbU, q, hq, hqlen.trans_le hlen, hcomp q⟩
    · right
      right
      have hlU : l ∉ U := fun h => (Finset.mem_sdiff.mp hl).2 (Finset.mem_union_right _ h)
      exact ⟨l, hl, w, hw, hlen,
        Paper.HighGirthExteriorComponent.exterior_path_component G U u l hu hlU w hw hs⟩

end Paper.HighGirthComponentAccess

#print axioms Paper.HighGirthComponentAccess.residual_component_access
