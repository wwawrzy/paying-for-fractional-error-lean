import Paper.Endpoints.Girth.HighGirthResidualComponents

/-! All four original claims of fv:hg:residual, with the actual branch-based
transformation, genuine induced component paths/cycles, and an explicit bridge
from oriented attachment pairs to the original unordered edge count.
This is a static structural lemma, not a distributed algorithm theorem. -/
namespace Paper.HighGirthResidual

theorem residual_endpoint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (∀ v ∈ Paper.HighGirthRounding.residual G x,
      (v ∈ Paper.HighGirthRounding.last G x ∨ ∃ u ∈ Paper.HighGirthRounding.last G x, G.Adj v u) →
      (G.neighborFinset v ∩ Paper.HighGirthRounding.residual G x).card ≤ 2) ∧
    (∀ K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent,
      (∃ (a b : K) (p : K.toSimpleGraph.Walk a b), p.IsPath ∧
        (∀ z : K, z ∈ p.support) ∧ K.toSimpleGraph = p.toSubgraph.spanningCoe) ∨
      (∃ (a : K) (c : K.toSimpleGraph.Walk a a), c.IsCycle ∧
        (∀ z : K, z ∈ c.support) ∧ K.toSimpleGraph = c.toSubgraph.spanningCoe)) ∧
    ((∀ u ∈ Paper.HighGirthRounding.last G x,
      ∀ v ∈ Paper.HighGirthTransformation.demands G \ Paper.HighGirthRounding.residual G x,
        G.Adj u v → v ∈ Paper.HighGirthAttachments.connectors G x) ∧
    (∀ u ∈ Paper.HighGirthTransformation.branches G ∩ Paper.HighGirthRounding.last G x,
      u ∈ Paper.HighGirthAttachments.vertices G x)) ∧
    (∀ (u : V) (hu : u ∈ Paper.HighGirthRounding.last G x),
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
        H.connectedComponentMk ⟨a, ha⟩ = H.connectedComponentMk ⟨u, hu⟩)) ∧
    ((Paper.HighGirthRounding.last G x).card ≤
      5 * Paper.HighGirthAttachments.count G x +
      4 * (Paper.HighGirthRounding.middle G x).card) ∧
    (let E := (Paper.HighGirthAttachments.pairs G x).image (fun p => s(p.1, p.2))
    E.card = Paper.HighGirthAttachments.count G x ∧
    ∀ u t : V, s(u, t) ∈ E ↔ G.Adj u t ∧
      ((u ∈ Paper.HighGirthRounding.last G x ∧ t ∈ Paper.HighGirthAttachments.connectors G x) ∨
       (t ∈ Paper.HighGirthRounding.last G x ∧ u ∈ Paper.HighGirthAttachments.connectors G x))) := by
  exact ⟨fun v hv hnear => HighGirthResidualDegree.residual_neighbor_degree G x v hv hnear,
    HighGirthResidualComponents.residual_components_path_or_cycle G x,
    HighGirthResidualAttachments.residual_attachments G x,
    fun u hu => HighGirthComponentAccess.residual_component_access G x u hu,
    HighGirthResidualSize.residual_size_bound G x,
    HighGirthAttachmentEdges.attachment_edge_correspondence G x⟩

end Paper.HighGirthResidual

#print axioms Paper.HighGirthResidual.residual_endpoint
