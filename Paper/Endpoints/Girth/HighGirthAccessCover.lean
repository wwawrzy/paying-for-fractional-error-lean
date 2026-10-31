import Paper.Endpoints.Girth.HighGirthLAccess
set_option maxHeartbeats 200000
namespace Paper.HighGirthAccessCover

theorem residual_access_cover
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    Paper.HighGirthRounding.last G x ⊆
      ((Paper.HighGirthAttachments.vertices G x).biUnion (Paper.HighGirthAccessSets.uBallTwo G x)) ∪
      ((Paper.HighGirthRounding.middle G x).biUnion (Paper.HighGirthAccessSets.lAccessTwo G x)) := by
  classical
    let U := Paper.HighGirthRounding.last G x
    let N := Paper.HighGirthAccessSets.neighborsU G x
    have hball : ∀ b ∈ U, ∀ p ∈ U, ∀ u ∈ U,
        u ∈ Paper.SevenFoundation.closed G p → p ∈ Paper.SevenFoundation.closed G b →
        u ∈ Paper.HighGirthAccessSets.uBallTwo G x b := by
      intro b hb p hp u hu hup hpb
      change u ∈ insert b (N b ∪ (N b).biUnion (fun p => N p \ {b}))
      by_cases hub : u = b
      · exact Finset.mem_insert.mpr (Or.inl hub)
      apply Finset.mem_insert.mpr
      right
      by_cases hpbEq : p = b
      · subst p
        exact Finset.mem_union_left _ (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset b u).mpr (((Paper.SevenFoundation.mem_closed G u b).mp hup).resolve_left hub), hu⟩)
      have hpN : p ∈ N b := Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset b p).mpr (((Paper.SevenFoundation.mem_closed G p b).mp hpb).resolve_left hpbEq), hp⟩
      by_cases hupEq : u = p
      · subst u
        exact Finset.mem_union_left _ hpN
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨p, hpN, Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p u).mpr
          (((Paper.SevenFoundation.mem_closed G u p).mp hup).resolve_left hupEq), hu⟩,
          by simpa using hub⟩⟩
    have hlAccess : ∀ l ∈ Paper.HighGirthRounding.middle G x, ∀ u ∈ U,
        (u ∈ Paper.SevenFoundation.closed G l ∨ ∃ p ∈ U,
          u ∈ Paper.SevenFoundation.closed G p ∧ p ∈ Paper.SevenFoundation.closed G l) →
        u ∈ Paper.HighGirthAccessSets.lAccessTwo G x l := by
      intro l hl u hu hpath
      have hlU : l ∉ U := fun h => (Finset.mem_sdiff.mp hl).2 (Finset.mem_union_right _ h)
      have first : ∀ v ∈ U, v ∈ Paper.SevenFoundation.closed G l → v ∈ N l := by
        intro v hv hvl
        have hne : v ≠ l := by intro heq; subst v; exact hlU hv
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset l v).mpr
          (((Paper.SevenFoundation.mem_closed G v l).mp hvl).resolve_left hne), hv⟩
      change u ∈ N l ∪ (N l).biUnion N
      rcases hpath with hul | ⟨p, hp, hup, hpl⟩
      · exact Finset.mem_union_left _ (first u hu hul)
      · have hpN := first p hp hpl
        by_cases heq : u = p
        · subst u
          exact Finset.mem_union_left _ hpN
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hpN,
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p u).mpr
              (((Paper.SevenFoundation.mem_closed G u p).mp hup).resolve_left heq), hu⟩⟩)
    intro u hu
    rcases Paper.HighGirthShortAccess.short_access_witness G x u hu with
      ⟨b, hb, p, hp, hup, hpb⟩ | ⟨b, hb, hub⟩ | ⟨l, hl, hpath⟩
    · have hbA := (Paper.HighGirthResidualAttachments.residual_attachments G x).2 b hb
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨b, hbA, hball b (Finset.mem_inter.mp hb).2 p hp u hu hup hpb⟩)
    · have hbU := (Finset.mem_filter.mp hb).1
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨b, hb, hball b hbU b hbU u hu hub (Paper.SevenFoundation.self_mem_closed G b)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l, hl, hlAccess l hl u hu hpath⟩)

end Paper.HighGirthAccessCover

#print axioms Paper.HighGirthAccessCover.residual_access_cover
