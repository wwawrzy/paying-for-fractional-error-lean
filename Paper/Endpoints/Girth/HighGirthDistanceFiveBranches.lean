import Paper.Endpoints.Girth.HighGirthMetricAccess
set_option maxHeartbeats 200000
namespace Paper.HighGirthDistanceFiveBranches

theorem distance_five_attachments_are_branches
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.isFreePath G x K)
    (hcount : Paper.HighGirthComponentAttachments.count G x K = 2)
    (a b : K)
    (haA : a.val.val ∈ Paper.HighGirthAttachments.vertices G x)
    (hbA : b.val.val ∈ Paper.HighGirthAttachments.vertices G x)
    (hdist : K.toSimpleGraph.dist a b = 5) :
    a.val.val ∈ Paper.HighGirthTransformation.branches G ∧
    b.val.val ∈ Paper.HighGirthTransformation.branches G := by
  classical
    have hone : ∀ (a b : K),
        a.val.val ∈ Paper.HighGirthAttachments.vertices G x →
        b.val.val ∈ Paper.HighGirthAttachments.vertices G x →
        K.toSimpleGraph.dist a b = 5 →
        a.val.val ∈ Paper.HighGirthTransformation.branches G := by
      intro a b haA hbA hdist
      by_contra haB
      have haK : a.val.val ∈ Paper.HighGirthFreePaths.members G x K :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩
      have hbK : b.val.val ∈ Paper.HighGirthFreePaths.members G x K :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,b.val.property,b.property⟩
      have hab : a.val.val ≠ b.val.val := by
        intro h
        have he : a = b := Subtype.ext (Subtype.ext h)
        subst b
        simpa using hdist
      obtain ⟨p,hp,hplen⟩ := K.connected_toSimpleGraph.exists_path_of_dist a b
      let u := p.getVert 2
      have hua : K.toSimpleGraph.dist u a = 2 := by
        have hh := SimpleGraph.length_eq_dist_of_subwalk hplen (p.isSubwalk_take 2)
        have he : 2 = K.toSimpleGraph.dist a u := by simpa [SimpleGraph.Walk.take_length,hplen,hdist,u] using hh
        simpa only [SimpleGraph.dist_comm] using he.symm
      have hub : K.toSimpleGraph.dist u b = 3 := by
        have hh := SimpleGraph.length_eq_dist_of_subwalk hplen (p.isSubwalk_drop 2)
        have he : 3 = K.toSimpleGraph.dist u b := by simpa [SimpleGraph.Walk.drop_length,hplen,hdist,u] using hh
        exact he.symm
      have hex : ∀ v : K, v.val.val ∈ Paper.HighGirthAttachments.vertices G x → v = a ∨ v = b := by
        intro v hv
        have hvK : v.val.val ∈ Paper.HighGirthFreePaths.members G x K :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.val.property,v.property⟩
        rcases Paper.HighGirthAttachmentVertices.attachment_vertices_exhausted G x K (by omega) a.val.val b.val.val haK hbK hab haA hbA v.val.val hvK hv with h | h
        · exact Or.inl (Subtype.ext (Subtype.ext h))
        · exact Or.inr (Subtype.ext (Subtype.ext h))
      rcases Paper.HighGirthMetricAccess.free_component_metric_access G x K hfree.2 u with ⟨v,hvB,hd⟩ | ⟨v,hvA,hd⟩
      · have hvK : v.val.val ∈ Paper.HighGirthFreePaths.members G x K :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.val.property,v.property⟩
        have hvA := (Paper.HighGirthFreeAttachments.branches_and_attachment_exists G x K hfree.2).1 v.val.val (Finset.mem_inter.mpr ⟨hvB,hvK⟩)
        rcases hex v hvA with rfl | rfl
        · exact haB hvB
        · omega
      · rcases hex v hvA with rfl | rfl
        · omega
        · omega
    exact ⟨hone a b haA hbA hdist,hone b a hbA haA (by simpa only [SimpleGraph.dist_comm] using hdist)⟩

end Paper.HighGirthDistanceFiveBranches

#print axioms Paper.HighGirthDistanceFiveBranches.distance_five_attachments_are_branches
