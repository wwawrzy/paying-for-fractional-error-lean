import Paper.Endpoints.Girth.HighGirthResidualAttachments
set_option maxHeartbeats 200000
namespace Paper.HighGirthAttachmentCounts

theorem attachment_count_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    Disjoint (Paper.HighGirthRounding.last G x) (Paper.HighGirthAttachments.connectors G x) ∧
      (Paper.HighGirthAttachments.vertices G x).card ≤ Paper.HighGirthAttachments.count G x ∧
      (Paper.HighGirthAttachments.connectors G x).card ≤ Paper.HighGirthAttachments.count G x := by
  classical
    have hdisjoint : Disjoint (Paper.HighGirthRounding.last G x) (Paper.HighGirthAttachments.connectors G x) := by
      apply Finset.disjoint_left.mpr
      intro u hu huT
      obtain ⟨_, ⟨w, hw, hadj⟩, _⟩ := (Finset.mem_filter.mp huT).2
      have huR := (Finset.mem_sdiff.mp hu).1
      exact (Finset.mem_sdiff.mp huR).2 (Finset.mem_biUnion.mpr ⟨w, hw,
        (Paper.SevenFoundation.mem_closed G u w).mpr (Or.inr hadj.symm)⟩)
    have hvertices : Paper.HighGirthAttachments.vertices G x =
        (Paper.HighGirthAttachments.pairs G x).image Prod.fst := by
      ext u
      constructor
      · intro hu
        obtain ⟨huU, t, ht, hadj⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_image.mpr ⟨(u, t), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨huU, ht⟩, hadj⟩, rfl⟩
      · intro hu
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hu
        subst u
        obtain ⟨hpProd, hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨huU, ht⟩ := Finset.mem_product.mp hpProd
        exact Finset.mem_filter.mpr ⟨huU, ⟨p.2, ht, hadj⟩⟩
    have hconnectors : Paper.HighGirthAttachments.connectors G x =
        (Paper.HighGirthAttachments.pairs G x).image Prod.snd := by
      ext t
      constructor
      · intro ht
        obtain ⟨_, _, u, huU, hadj⟩ := (Finset.mem_filter.mp ht).2
        exact Finset.mem_image.mpr ⟨(u, t), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨huU, ht⟩, hadj.symm⟩, rfl⟩
      · intro ht
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp ht
        subst t
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    refine ⟨hdisjoint, ?_, ?_⟩
    · change (Paper.HighGirthAttachments.vertices G x).card ≤ (Paper.HighGirthAttachments.pairs G x).card
      rw [hvertices]
      exact Finset.card_image_le
    · change (Paper.HighGirthAttachments.connectors G x).card ≤ (Paper.HighGirthAttachments.pairs G x).card
      rw [hconnectors]
      exact Finset.card_image_le

end Paper.HighGirthAttachmentCounts

#print axioms Paper.HighGirthAttachmentCounts.attachment_count_bounds
