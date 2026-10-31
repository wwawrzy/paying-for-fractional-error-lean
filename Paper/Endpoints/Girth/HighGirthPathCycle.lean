import Paper.Endpoints.Girth.HighGirthPathEdges
set_option maxHeartbeats 200000
namespace Paper.HighGirthPathCycle

theorem connected_path_or_cycle
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hd : ∀ z, G.degree z ≤ 2) :
    (∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ (∀ z : V, z ∈ p.support) ∧
      G = p.toSubgraph.spanningCoe) ∨
    (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (∀ z : V, z ∈ c.support) ∧
      G = c.toSubgraph.spanningCoe) := by
  classical
    obtain ⟨u,v,p,hp,hspan⟩ := Paper.HighGirthSpanningPath.connected_spanning_path G hconn hd
    have hedge := Paper.HighGirthPathEdges.spanning_path_extra_edges G hd u v p hp hspan
    by_cases hextra : G.Adj u v ∧ ¬p.toSubgraph.Adj u v
    · right
      let c : G.Walk v v := SimpleGraph.Walk.cons hextra.1.symm p
      have hswap : s(v,u) = s(u,v) := Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)
      have hnot : s(v,u) ∉ p.edges := by
        intro he
        rw [hswap] at he
        exact hextra.2 (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he)
      have hcycle : c.IsCycle := (SimpleGraph.Walk.cons_isCycle_iff p hextra.1.symm).mpr ⟨hp,hnot⟩
      have hcEnd : c.toSubgraph.Adj u v := by
        rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
        simp [c,hswap]
      refine ⟨v,c,hcycle,?_,?_⟩
      · intro z
        exact List.mem_cons_of_mem v (hspan z)
      · ext a b
        constructor
        · intro hab
          rcases hedge a b hab with habp | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact Or.inr habp
          · exact hcEnd
          · exact hcEnd.symm
        · intro hab
          exact c.toSubgraph.adj_sub hab
    · left
      refine ⟨u,v,p,hp,hspan,?_⟩
      ext a b
      constructor
      · intro hab
        rcases hedge a b hab with habp | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact habp
        · by_contra hn
          exact hextra ⟨hab,hn⟩
        · by_contra hn
          exact hextra ⟨hab.symm,fun h => hn h.symm⟩
      · intro hab
        exact p.toSubgraph.adj_sub hab

end Paper.HighGirthPathCycle

#print axioms Paper.HighGirthPathCycle.connected_path_or_cycle
