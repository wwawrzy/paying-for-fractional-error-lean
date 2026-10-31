import Paper.Endpoints.Girth.HighGirthPathNeighborCounts

/-! All four original structural claims of fv:hg:free for genuine free path
components of G[U], including true path end/inner interpretation. -/
namespace Paper.HighGirthFree

theorem actual_path_vertices
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : K.toSimpleGraph = p.toSubgraph.spanningCoe) :
    a.val.val ∈ Paper.HighGirthRounding.positive G x ∧
    b.val.val ∈ Paper.HighGirthRounding.positive G x ∧
    ∀ i : Nat, i ≠ 0 → i < p.length →
      (p.getVert i).val.val ∉ Paper.HighGirthAttachments.vertices G x →
      ∀ y, G.Adj (p.getVert i).val.val y → y ∈ Paper.HighGirthFreePaths.members G x K := by
  classical
  have hm : ∀ z : K, z.val.val ∈ Paper.HighGirthFreePaths.members G x K := by
    intro z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.val.property,z.property⟩
  have hc := Paper.HighGirthPathNeighborCounts.path_component_neighbor_counts G x K a b p hp hgraph
  refine ⟨Paper.HighGirthFreeEndpoints.free_endpoint_positive G x K hfree _ (hm a) hc.1,
    Paper.HighGirthFreeEndpoints.free_endpoint_positive G x K hfree _ (hm b) hc.2.1,?_⟩
  intro i hi hiL hn y hadj
  exact (Paper.HighGirthFreeInner.free_branch_and_inner_neighbors G x K hfree).2 _
    (hm (p.getVert i)) (hc.2.2 i hi hiL) hn y hadj

theorem free_path_endpoint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hK : Paper.HighGirthFreePaths.isFreePath G x K) :
    (∀ u ∈ Paper.HighGirthFreePaths.members G x K, ∀ y,
      y ∉ Paper.HighGirthFreePaths.members G x K → G.Adj u y →
      y ∉ Paper.HighGirthRounding.residual G x ∧
      y ∈ Paper.HighGirthTransformation.zone G ∧
      (y ∈ Paper.HighGirthTransformation.demands G → y ∈ Paper.HighGirthAttachments.connectors G x) ∧
      (y ∉ Paper.HighGirthTransformation.demands G →
        y ∈ Paper.HighGirthRounding.positive G x ∧ Paper.HighGirthRounding.hits G x y ≤ 1)) ∧
    ((∀ u ∈ Paper.HighGirthFreePaths.members G x K, 3 ≤ G.degree u →
      u ∈ Paper.HighGirthTransformation.branches G ∧
      ∀ y, y ∉ Paper.HighGirthFreePaths.members G x K → G.Adj u y →
        y ∈ Paper.HighGirthAttachments.connectors G x) ∧
    (∀ u ∈ Paper.HighGirthFreePaths.members G x K,
      (G.neighborFinset u ∩ Paper.HighGirthFreePaths.members G x K).card = 2 →
      u ∉ Paper.HighGirthAttachments.vertices G x →
      ∀ y, G.Adj u y → y ∈ Paper.HighGirthFreePaths.members G x K)) ∧
    (∀ (u : V) (huK : u ∈ Paper.HighGirthFreePaths.members G x K),
      let U := Paper.HighGirthRounding.last G x
    let H := G.induce (↑U : Set V)
    (∃ b ∈ Paper.HighGirthTransformation.branches G ∩ Paper.HighGirthFreePaths.members G x K,
      ∃ hb : b ∈ U, ∃ hu : u ∈ U, ∃ q : H.Walk ⟨u,hu⟩ ⟨b,hb⟩,
        q.IsPath ∧ q.length ≤ 2 ∧ ∀ a ∈ q.support, a.val ∈ Paper.HighGirthFreePaths.members G x K) ∨
    (∃ b ∈ Paper.HighGirthAttachments.vertices G x ∩ Paper.HighGirthFreePaths.members G x K,
      ∃ hb : b ∈ U, ∃ hu : u ∈ U, ∃ q : H.Walk ⟨u,hu⟩ ⟨b,hb⟩,
        q.IsPath ∧ q.length ≤ 1 ∧ ∀ a ∈ q.support, a.val ∈ Paper.HighGirthFreePaths.members G x K)) ∧
    ((∀ u ∈ HighGirthTransformation.branches G ∩ HighGirthFreePaths.members G x K,
      u ∈ HighGirthAttachments.vertices G x) ∧
    (∃ u ∈ HighGirthFreePaths.members G x K, u ∈ HighGirthAttachments.vertices G x)) ∧
    ((∀ u ∈ Paper.HighGirthFreePaths.members G x K, x u ≤ (1 : Real) / 2) ∧
      (∀ t ∈ Paper.HighGirthAttachments.connectors G x,
        t ∈ Paper.HighGirthRounding.other G x ∧
        (t ∈ Paper.HighGirthRounding.positive G x ∨ x t ≤ (1 : Real) / 2))) ∧
    (∃ (a b : K) (p : K.toSimpleGraph.Walk a b), p.IsPath ∧
      (∀ z : K, z ∈ p.support) ∧ K.toSimpleGraph = p.toSubgraph.spanningCoe ∧
    a.val.val ∈ Paper.HighGirthRounding.positive G x ∧
    b.val.val ∈ Paper.HighGirthRounding.positive G x ∧
    ∀ i : Nat, i ≠ 0 → i < p.length →
      (p.getVert i).val.val ∉ Paper.HighGirthAttachments.vertices G x →
      ∀ y, G.Adj (p.getVert i).val.val y → y ∈ Paper.HighGirthFreePaths.members G x K) := by
  classical
  have hfree := hK.2
  refine ⟨Paper.HighGirthFreeExternal.free_external_neighbors G x K hfree,
    Paper.HighGirthFreeInner.free_branch_and_inner_neighbors G x K hfree,
    fun u huK => Paper.HighGirthFreeAccess.free_short_access G x K hfree u huK,
    Paper.HighGirthFreeAttachments.branches_and_attachment_exists G x K hfree,?_,?_⟩
  · have ht := Paper.HighGirthFreeCoordinates.residual_threshold_coordinates G x
    refine ⟨?_,ht.2⟩
    intro u huK
    obtain ⟨huU,huComp⟩ := (Finset.mem_filter.mp huK).2
    exact ht.1 u huU
  · obtain ⟨a,b,p,hp,hspan,hgraph⟩ := hK.1
    exact ⟨a,b,p,hp,hspan,hgraph,actual_path_vertices G x K hfree a b p hp hgraph⟩

end Paper.HighGirthFree

#print axioms Paper.HighGirthFree.actual_path_vertices
#print axioms Paper.HighGirthFree.free_path_endpoint
