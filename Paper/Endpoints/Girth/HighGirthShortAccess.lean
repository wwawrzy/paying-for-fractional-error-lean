import Paper.Endpoints.Girth.HighGirthAttachmentCounts
set_option maxHeartbeats 200000
namespace Paper.HighGirthShortAccess

theorem short_access_witness
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (u : V) (hu : u ∈ Paper.HighGirthRounding.last G x) :
    (∃ b ∈ Paper.HighGirthTransformation.branches G ∩ Paper.HighGirthRounding.last G x,
      ∃ p ∈ Paper.HighGirthRounding.last G x,
        u ∈ Paper.SevenFoundation.closed G p ∧ p ∈ Paper.SevenFoundation.closed G b) ∨
    (∃ b ∈ Paper.HighGirthAttachments.vertices G x, u ∈ Paper.SevenFoundation.closed G b) ∨
    (∃ l ∈ Paper.HighGirthRounding.middle G x,
      u ∈ Paper.SevenFoundation.closed G l ∨
      ∃ p ∈ Paper.HighGirthRounding.last G x,
        u ∈ Paper.SevenFoundation.closed G p ∧ p ∈ Paper.SevenFoundation.closed G l) := by
  classical
    have hexit : ∀ v ∈ Paper.HighGirthRounding.last G x,
        ∀ p ∈ Paper.HighGirthTransformation.demands G,
          G.Adj v p → p ∉ Paper.HighGirthRounding.last G x →
          p ∈ Paper.HighGirthRounding.middle G x ∨ p ∈ Paper.HighGirthAttachments.connectors G x := by
      intro v hv p hp hadj hpU
      by_cases hpR : p ∈ Paper.HighGirthRounding.residual G x
      · left
        apply Finset.mem_sdiff.mpr
        refine ⟨hpR, ?_⟩
        intro hbad
        rcases Finset.mem_union.mp hbad with hpH | hpLast
        · exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨p, hpH,
            (Paper.SevenFoundation.mem_closed G v p).mpr (Or.inr hadj.symm)⟩)
        · exact hpU hpLast
      · right
        exact (Paper.HighGirthResidualAttachments.residual_attachments G x).1 v hv p
          (Finset.mem_sdiff.mpr ⟨hp, hpR⟩) hadj
    have huR0 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu).1).1
    have huZ := (Finset.mem_sdiff.mp huR0).1
    obtain ⟨p, hpNear, huP⟩ := Finset.mem_biUnion.mp huZ
    obtain ⟨b, hb, hpB⟩ := Finset.mem_biUnion.mp hpNear
    have hnearR0 := (Paper.HighGirthFirstSelection.first_selection_geometry G).2
    have hpR0 := hnearR0 hpNear
    have hbR0 := hnearR0 (Paper.SevenFoundation.subset_covered G _ hb)
    by_cases hpU : p ∈ Paper.HighGirthRounding.last G x
    · by_cases hbU : b ∈ Paper.HighGirthRounding.last G x
      · left
        exact ⟨b, Finset.mem_inter.mpr ⟨hb, hbU⟩, p, hpU, huP, hpB⟩
      · have hne : p ≠ b := by
          intro heq
          subst p
          exact hbU hpU
        have hadj : G.Adj p b := (((Paper.SevenFoundation.mem_closed G p b).mp hpB).resolve_left hne).symm
        rcases hexit p hpU b hbR0 hadj hbU with hbL | hbT
        · right
          right
          exact ⟨b, hbL, Or.inr ⟨p, hpU, huP, hpB⟩⟩
        · right
          left
          exact ⟨p, Finset.mem_filter.mpr ⟨hpU, ⟨b, hbT, hadj⟩⟩, huP⟩
    · have hne : u ≠ p := by
        intro heq
        subst p
        exact hpU hu
      have hadj : G.Adj u p := (((Paper.SevenFoundation.mem_closed G u p).mp huP).resolve_left hne).symm
      rcases hexit u hu p hpR0 hadj hpU with hpL | hpT
      · right
        right
        exact ⟨p, hpL, Or.inl huP⟩
      · right
        left
        exact ⟨u, Finset.mem_filter.mpr ⟨hu, ⟨p, hpT, hadj⟩⟩, Paper.SevenFoundation.self_mem_closed G u⟩

end Paper.HighGirthShortAccess

#print axioms Paper.HighGirthShortAccess.short_access_witness
