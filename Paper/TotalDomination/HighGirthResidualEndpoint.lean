import Paper.Endpoints.Girth.HighGirthExteriorComponent
import Paper.TotalDomination.HighGirthResidualSize
set_option maxHeartbeats 200000
namespace Paper.TotalDomination.HighGirthSetup

theorem component_access
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (u : V) (hu : u ∈ core G x identifier hfree) :
    let U := core G x identifier hfree
    let H := G.induce (↑U : Set V)
    (∃ b ∈ B G, ∃ hb : b ∈ U,
      ∃ q : H.Walk ⟨u, hu⟩ ⟨b, hb⟩, q.IsPath ∧ q.length ≤ 3 ∧
        ∀ a ∈ q.support, H.connectedComponentMk a = H.connectedComponentMk ⟨u, hu⟩) ∨
    (∃ b ∈ attachments G x identifier hfree, ∃ hb : b ∈ U,
      ∃ q : H.Walk ⟨u, hu⟩ ⟨b, hb⟩, q.IsPath ∧ q.length ≤ 2 ∧
        ∀ a ∈ q.support, H.connectedComponentMk a = H.connectedComponentMk ⟨u, hu⟩) ∨
    (∃ l ∈ served G (I G x identifier hfree), ∃ w : G.Walk u l,
      w.IsPath ∧ w.length ≤ 3 ∧ ∀ a ∈ w.support, a ≠ l → ∃ ha : a ∈ U,
        H.connectedComponentMk ⟨a, ha⟩ = H.connectedComponentMk ⟨u, hu⟩) := by
  classical
    dsimp only
    let U := core G x identifier hfree
    let H := G.induce (↑U : Set V)
    have hcomp : ∀ {a b : {v // v ∈ U}} (q : H.Walk a b),
        ∀ v ∈ q.support, H.connectedComponentMk v = H.connectedComponentMk a := by
      intro a b q v hv
      exact (SimpleGraph.ConnectedComponent.sound (q.takeUntil v hv).reachable).symm
    rcases short_access G x identifier hfree hu with
      ⟨b, hb, w, hw, hlen, hs⟩ | ⟨b, hb, w, hw, hlen, hs⟩ | ⟨l, hl, w, hw, hlen, hs⟩
    · left
      have hbU := (Finset.mem_inter.mp hb).2
      obtain ⟨q, hq, hqlen, hmap⟩ := Paper.HighGirthInducedPaths.lift_internal_path G U u b hu hbU w hw hs
      exact ⟨b, (Finset.mem_inter.mp hb).1, hbU, q, hq, hqlen.trans_le hlen, hcomp q⟩
    · right
      left
      have hbU := (Finset.mem_inter.mp hb).1
      obtain ⟨q, hq, hqlen, hmap⟩ := Paper.HighGirthInducedPaths.lift_internal_path G U u b hu hbU w hw hs
      exact ⟨b, hb, hbU, q, hq, hqlen.trans_le hlen, hcomp q⟩
    · right
      right
      have hlU : l ∉ U := served_not_core G x identifier hfree hl
      have hs' : ∀ a ∈ w.support, a ∈ insert l U := by
        intro a ha
        rcases hs a ha with rfl | ha
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem ha
      exact ⟨l, hl, w, hw, hlen,
        Paper.HighGirthExteriorComponent.exterior_path_component G U u l hu hlU w hw hs'⟩

end Paper.TotalDomination.HighGirthSetup

#print axioms Paper.TotalDomination.HighGirthSetup.component_access
