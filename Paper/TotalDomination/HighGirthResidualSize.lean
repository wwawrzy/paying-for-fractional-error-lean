import Paper.TotalDomination.HighGirthResidualAccess
import Paper.Preliminaries.DegreeTwoBalls

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem core_neighbor_degree : ∀ v ∈ core G x identifier hfree,
    (DegreeTwoBalls.neighbors G (core G x identifier hfree) v).card ≤ 2 := by
  intro v hv
  have hh := low_residual_degree G x identifier hfree (core_residual G x identifier hfree hv) (Or.inl hv)
  exact (Finset.card_le_card (Finset.inter_subset_inter_left (core_residual G x identifier hfree))).trans hh

theorem served_not_core {y : V} (hy : y ∈ served G (I G x identifier hfree)) :
    y ∉ core G x identifier hfree := fun hc =>
  (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hc).1).2 hy

theorem served_access_card {y : V} (hy : y ∈ served G (I G x identifier hfree)) :
    (DegreeTwoBalls.accessThree G (core G x identifier hfree) y).card ≤ 6 := by
  classical
  let S := core G x identifier hfree
  have hN : (DegreeTwoBalls.neighbors G S y).card ≤ 2 := by
    by_cases hn : (DegreeTwoBalls.neighbors G S y).Nonempty
    · obtain ⟨u,hu⟩ := hn
      have huS := (Finset.mem_inter.mp hu).2
      have ha := (G.mem_neighborFinset y u).mp (Finset.mem_inter.mp hu).1
      have hh := low_residual_degree G x identifier hfree (Finset.mem_inter.mp hy).1 (Or.inr ⟨u,huS,ha⟩)
      exact (Finset.card_le_card (Finset.inter_subset_inter_left (core_residual G x identifier hfree))).trans hh
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  apply DegreeTwoBalls.card_accessThree G S (core_neighbor_degree G x identifier hfree) y hN
  intro p hp
  have hpS := (Finset.mem_inter.mp hp).2
  have hap := (G.mem_neighborFinset y p).mp (Finset.mem_inter.mp hp).1
  have hlow := low_residual_degree G x identifier hfree (core_residual G x identifier hfree hpS) (Or.inl hpS)
  have hsub : insert y (DegreeTwoBalls.neighbors G S p) ⊆
      G.neighborFinset p ∩ residual G (I G x identifier hfree) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p z).mpr hap.symm,(Finset.mem_inter.mp hy).1⟩
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
        core_residual G x identifier hfree (Finset.mem_inter.mp hz).2⟩
  have hnot : y ∉ DegreeTwoBalls.neighbors G S p := fun hh => served_not_core G x identifier hfree hy (Finset.mem_inter.mp hh).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hc
  change (G.neighborFinset p ∩ residual G (I G x identifier hfree)).card ≤ 2 at hlow
  omega

theorem core_access_cover : core G x identifier hfree ⊆
    (attachments G x identifier hfree).biUnion (DegreeTwoBalls.ballThree G (core G x identifier hfree)) ∪
    (served G (I G x identifier hfree)).biUnion (DegreeTwoBalls.accessThree G (core G x identifier hfree)) := by
  intro u hu
  rcases short_access G x identifier hfree hu with
    ⟨b,hb,q,hq,hql,hs⟩ | ⟨b,hb,q,hq,hql,hs⟩ | ⟨y,hy,q,hq,hql,hs⟩
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨b,branch_attachment G x identifier hfree hb,?_⟩
    apply DegreeTwoBalls.endpoint_mem_ballThree G (core G x identifier hfree) q.reverse
    · simpa using hql
    · intro v hv
      exact hs v (by simpa using hv)
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨b,hb,?_⟩
    apply DegreeTwoBalls.endpoint_mem_ballThree G (core G x identifier hfree) q.reverse
    · simpa using (show q.length ≤ 3 by omega)
    · intro v hv
      exact hs v (by simpa using hv)
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨y,hy,?_⟩
    apply DegreeTwoBalls.endpoint_mem_accessThree G (core G x identifier hfree) q.reverse
    · simpa using hql
    · exact hu
    · exact served_not_core G x identifier hfree hy
    · intro v hv
      exact hs v (by simpa using hv)

theorem residual_size_vertices : (core G x identifier hfree).card ≤
    7*(attachments G x identifier hfree).card + 6*(served G (I G x identifier hfree)).card := by
  have hA : ((attachments G x identifier hfree).biUnion
      (DegreeTwoBalls.ballThree G (core G x identifier hfree))).card ≤ 7*(attachments G x identifier hfree).card := by
    calc
      _ ≤ ∑ a ∈ attachments G x identifier hfree, (DegreeTwoBalls.ballThree G (core G x identifier hfree) a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ attachments G x identifier hfree, 7 := Finset.sum_le_sum fun a ha =>
        DegreeTwoBalls.card_ballThree G _ (core_neighbor_degree G x identifier hfree) (Finset.mem_inter.mp ha).1
      _ = _ := by simp [Nat.mul_comm]
  have hY : ((served G (I G x identifier hfree)).biUnion
      (DegreeTwoBalls.accessThree G (core G x identifier hfree))).card ≤ 6*(served G (I G x identifier hfree)).card := by
    calc
      _ ≤ ∑ y ∈ served G (I G x identifier hfree), (DegreeTwoBalls.accessThree G (core G x identifier hfree) y).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ served G (I G x identifier hfree), 6 := Finset.sum_le_sum fun y hy => served_access_card G x identifier hfree hy
      _ = _ := by simp [Nat.mul_comm]
  have hc := Finset.card_le_card (core_access_cover G x identifier hfree)
  have hU := Finset.card_union_le
    ((attachments G x identifier hfree).biUnion (DegreeTwoBalls.ballThree G (core G x identifier hfree)))
    ((served G (I G x identifier hfree)).biUnion (DegreeTwoBalls.accessThree G (core G x identifier hfree)))
  omega

noncomputable def attachmentPairs : Finset (V × V) := by
  classical
  exact ((core G x identifier hfree) ×ˢ (connectors G x identifier hfree)).filter (fun p => G.Adj p.1 p.2)
noncomputable def attachmentEdges : Finset (Sym2 V) :=
  (attachmentPairs G x identifier hfree).image (fun p => s(p.1,p.2))

theorem core_connectors_disjoint : Disjoint (core G x identifier hfree) (connectors G x identifier hfree) := by
  apply Finset.disjoint_left.mpr
  intro v hc ht
  exact (Finset.mem_sdiff.mp (core_residual G x identifier hfree hc)).2 (Finset.mem_filter.mp ht).2.2.1

theorem attachment_vertices_le_pairs : (attachments G x identifier hfree).card ≤
    (attachmentPairs G x identifier hfree).card := by
  classical
  have heq : (attachmentPairs G x identifier hfree).image Prod.fst = attachments G x identifier hfree := by
    ext v
    simp only [attachmentPairs,attachments,Finset.mem_image,Finset.mem_filter,Finset.mem_product,Finset.mem_inter,mem_neighbors]
    constructor
    · rintro ⟨⟨a,b⟩,⟨⟨ha,hb⟩,hab⟩,rfl⟩
      exact ⟨ha,b,hb,hab⟩
    · rintro ⟨hv,b,hb,hab⟩
      exact ⟨(v,b),⟨⟨hv,hb⟩,hab⟩,rfl⟩
  rw [← heq]
  exact Finset.card_image_le

theorem attachment_edges_card : (attachmentEdges G x identifier hfree).card =
    (attachmentPairs G x identifier hfree).card := by
  classical
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  rcases Sym2.mk_eq_mk_iff.mp heq with heq | heq
  · exact heq
  · have hpU := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hqT := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
    have hswap : p.1 = q.2 := congrArg Prod.fst heq
    exact False.elim (Finset.disjoint_left.mp (core_connectors_disjoint G x identifier hfree) hpU (hswap.symm ▸ hqT))

theorem residual_size_edges : (core G x identifier hfree).card ≤
    7*(attachmentEdges G x identifier hfree).card + 6*(served G (I G x identifier hfree)).card := by
  rw [attachment_edges_card G x identifier hfree]
  exact (residual_size_vertices G x identifier hfree).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 7 (attachment_vertices_le_pairs G x identifier hfree)) _)

theorem attachment_edge_correspondence
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    let E := (attachmentPairs G x identifier hfree).image (fun p => s(p.1, p.2))
    E.card = (attachmentPairs G x identifier hfree).card ∧
    ∀ u t : V, s(u, t) ∈ E ↔ G.Adj u t ∧
      ((u ∈ core G x identifier hfree ∧ t ∈ connectors G x identifier hfree) ∨
       (t ∈ core G x identifier hfree ∧ u ∈ connectors G x identifier hfree)) := by
  classical
    dsimp only
    have hd := core_connectors_disjoint G x identifier hfree
    have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) (attachmentPairs G x identifier hfree) := by
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

end Paper.TotalDomination.HighGirthSetup
