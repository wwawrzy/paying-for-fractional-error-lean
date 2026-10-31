import Paper.Endpoints.Girth.HighGirthComponentAccess
set_option maxHeartbeats 200000
namespace Paper.HighGirthAttachmentEdges

theorem attachment_edge_correspondence
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    let E := (Paper.HighGirthAttachments.pairs G x).image (fun p => s(p.1, p.2))
    E.card = Paper.HighGirthAttachments.count G x ∧
    ∀ u t : V, s(u, t) ∈ E ↔ G.Adj u t ∧
      ((u ∈ Paper.HighGirthRounding.last G x ∧ t ∈ Paper.HighGirthAttachments.connectors G x) ∨
       (t ∈ Paper.HighGirthRounding.last G x ∧ u ∈ Paper.HighGirthAttachments.connectors G x)) := by
  classical
    dsimp only
    have hd := (Paper.HighGirthAttachmentCounts.attachment_count_bounds G x).1
    have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) (Paper.HighGirthAttachments.pairs G x) := by
      intro p hp q hq heq
      rcases Sym2.mk_eq_mk_iff.mp heq with heq | heq
      · exact heq
      · have hpU := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        have hqT := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
        have hswap : p.1 = q.2 := congrArg Prod.fst heq
        exact False.elim ((Finset.disjoint_left.mp hd) hpU (hswap.symm ▸ hqT))
    constructor
    · exact Finset.card_image_of_injOn hinj
    · intro u t
      constructor
      · intro he
        obtain ⟨⟨a,b⟩, hp, heq⟩ := Finset.mem_image.mp he
        obtain ⟨hprod, hab⟩ := Finset.mem_filter.mp hp
        obtain ⟨haU,hbT⟩ := Finset.mem_product.mp hprod
        rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hab, Or.inl ⟨haU,hbT⟩⟩
        · exact ⟨hab.symm, Or.inr ⟨haU,hbT⟩⟩
      · rintro ⟨hadj, hcase⟩
        rcases hcase with ⟨hu,ht⟩ | ⟨ht,hu⟩
        · exact Finset.mem_image.mpr ⟨(u,t), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hu,ht⟩, hadj⟩, rfl⟩
        · refine Finset.mem_image.mpr ⟨(t,u), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨ht,hu⟩, hadj.symm⟩, ?_⟩
          exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)

end Paper.HighGirthAttachmentEdges

#print axioms Paper.HighGirthAttachmentEdges.attachment_edge_correspondence
