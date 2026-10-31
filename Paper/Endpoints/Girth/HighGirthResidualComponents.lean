import Paper.Endpoints.Girth.HighGirthPathCycle
set_option maxHeartbeats 200000
namespace Paper.HighGirthResidualComponents

theorem residual_components_path_or_cycle
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    ∀ K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent,
      (∃ (a b : K) (p : K.toSimpleGraph.Walk a b), p.IsPath ∧
        (∀ z : K, z ∈ p.support) ∧ K.toSimpleGraph = p.toSubgraph.spanningCoe) ∨
      (∃ (a : K) (c : K.toSimpleGraph.Walk a a), c.IsCycle ∧
        (∀ z : K, z ∈ c.support) ∧ K.toSimpleGraph = c.toSubgraph.spanningCoe) := by
  classical
  intro K
  let U := Paper.HighGirthRounding.last G x
  let H := G.induce (↑U : Set V)
  letI : Fintype K := Fintype.ofFinite K
  have hH : ∀ v : {u // u ∈ U}, H.degree v ≤ 2 :=
    Paper.HighGirthInducedDegree.residual_induced_degree G x
  have hK : ∀ z : K, K.toSimpleGraph.degree z ≤ 2 := by
    intro z
    let f : K.toSimpleGraph.neighborSet z → H.neighborSet z.val :=
      fun a => ⟨a.val.val, a.property⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : H.neighborSet z.val => a.val) hab
    have hle := Fintype.card_le_of_injective f hf
    have hle' : K.toSimpleGraph.degree z ≤ H.degree z.val := by
      simpa only [SimpleGraph.card_neighborSet_eq_degree] using hle
    exact hle'.trans (hH z.val)
  exact Paper.HighGirthPathCycle.connected_path_or_cycle K.toSimpleGraph K.connected_toSimpleGraph hK

end Paper.HighGirthResidualComponents

#print axioms Paper.HighGirthResidualComponents.residual_components_path_or_cycle
