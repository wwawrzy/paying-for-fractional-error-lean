import Paper.Endpoints.Girth.HighGirthPathTree

/-! Actual component path metric and attachment radius, for trimming in fv:hg:count. -/
namespace Paper.HighGirthPathMetric
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

theorem path_length_eq_distance
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hpath : HighGirthFreePaths.isPathComponent G x K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath) :
    p.length = K.toSimpleGraph.dist a b := by
  obtain ⟨q,hq,hqlen⟩ := K.connected_toSimpleGraph.exists_path_of_dist a b
  have ht := HighGirthPathTree.path_component_is_tree G x K hpath
  have he : p = q := congrArg Subtype.val (ht.isAcyclic.path_unique ⟨p,hp⟩ ⟨q,hq⟩)
  exact he ▸ hqlen

theorem attachment_radius_two
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.free G x K) (u : K) :
    ∃ v : K, v.val.val ∈ HighGirthAttachments.vertices G x ∧ K.toSimpleGraph.dist u v ≤ 2 := by
  classical
  rcases HighGirthMetricAccess.free_component_metric_access G x K hfree u with ⟨v,hvB,hd⟩ | ⟨v,hvA,hd⟩
  · have hvK : v.val.val ∈ HighGirthFreePaths.members G x K :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.val.property,v.property⟩
    exact ⟨v,(HighGirthFreeAttachments.branches_and_attachment_exists G x K hfree).1 v.val.val
      (Finset.mem_inter.mpr ⟨hvB,hvK⟩),hd⟩
  · exact ⟨v,hvA,by omega⟩

end Paper.HighGirthPathMetric

#print axioms Paper.HighGirthPathMetric.path_length_eq_distance
#print axioms Paper.HighGirthPathMetric.attachment_radius_two
