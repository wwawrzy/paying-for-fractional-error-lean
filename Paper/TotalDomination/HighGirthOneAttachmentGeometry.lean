import Paper.TotalDomination.HighGirthAttachmentGeometry

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem one_attachment_witness
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hone : (componentAttachmentPairs G x identifier hfree C).card = 1) :
    ∃ b t, componentAttachmentPairs G x identifier hfree C = {(b,t)} ∧
      b ∈ componentMembers G x identifier hfree C ∧ t ∈ connectors G x identifier hfree ∧ G.Adj b t := by
  classical
  obtain ⟨⟨b,t⟩,he⟩ := Finset.card_eq_one.mp hone
  have hm : (b,t) ∈ componentAttachmentPairs G x identifier hfree C := by simp [he]
  have hpair := (Finset.mem_filter.mp hm).1
  exact ⟨b,t,he,(Finset.mem_filter.mp hm).2,
    (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).2,(Finset.mem_filter.mp hpair).2⟩

theorem one_attachment_distinct
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hone : (componentAttachmentPairs G x identifier hfree C).card = 1) :
    Set.InjOn (fun q : V × V => q.1) (componentAttachmentPairs G x identifier hfree C) := by
  classical
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hone
  intro a ha b hb _
  have ha' : a = q := Finset.mem_singleton.mp (hq ▸ ha)
  have hb' : b = q := Finset.mem_singleton.mp (hq ▸ hb)
  exact ha'.trans hb'.symm

theorem one_attachment_vertex_unique
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (b t : V) (hone : componentAttachmentPairs G x identifier hfree C = {(b,t)})
    {u : V} (hu : u ∈ componentMembers G x identifier hfree C)
    (hA : u ∈ attachments G x identifier hfree) : u = b := by
  classical
  obtain ⟨v,hv,ha⟩ := (mem_neighbors G).mp (Finset.mem_inter.mp hA).2
  have hm : (u,v) ∈ componentAttachmentPairs G x identifier hfree C := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨component_subset_core G x identifier hfree C hu,hv⟩,ha⟩,hu⟩
  rw [hone] at hm
  exact congrArg Prod.fst (Finset.mem_singleton.mp hm)

theorem unique_attachment_radius
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (z : C)
    (huniq : ∀ v : C, v.val.val ∈ attachments G x identifier hfree → v = z) :
    (∀ u : C, C.toSimpleGraph.dist u z ≤ 3) ∧
    (z.val.val ∉ B G → ∀ u : C, C.toSimpleGraph.dist u z ≤ 2) := by
  constructor
  · intro u
    rcases free_component_metric_access G x identifier hfree C hC u with ⟨v,hB,hd⟩ | ⟨v,hA,hd⟩
    · have hA := branch_attachment G x identifier hfree (Finset.mem_inter.mpr ⟨hB,v.val.property⟩)
      simpa only [huniq v hA] using hd
    · have he := huniq v hA
      rw [he] at hd
      omega
  · intro hnB u
    rcases free_component_metric_access G x identifier hfree C hC u with ⟨v,hB,hd⟩ | ⟨v,hA,hd⟩
    · have hA := branch_attachment G x identifier hfree (Finset.mem_inter.mpr ⟨hB,v.val.property⟩)
      exact False.elim (hnB ((huniq v hA) ▸ hB))
    · simpa only [huniq v hA] using hd

theorem one_attachment_position_bounds
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (hone : (componentAttachmentPairs G x identifier hfree C).card = 1) :
    ∃ j, j ≤ p.length ∧ (p.getVert j).val.val ∈ attachments G x identifier hfree ∧
      (∀ k, k ≤ p.length → k ≠ j → (p.getVert k).val.val ∉ attachments G x identifier hfree) ∧
      j ≤ 3 ∧ p.length ≤ j+3 ∧ ((j = 0 ∨ j = p.length) → p.length ≤ 2) := by
  classical
  obtain ⟨v,t,hpairs,hvC,ht,ha⟩ := one_attachment_witness G x identifier hfree C hone
  obtain ⟨hvcore,hvcomp⟩ := (Finset.mem_filter.mp hvC).2
  let z : C := ⟨⟨v,hvcore⟩,hvcomp⟩
  have hzA : z.val.val ∈ attachments G x identifier hfree :=
    Finset.mem_inter.mpr ⟨hvcore,(mem_neighbors G).mpr ⟨t,ht,ha⟩⟩
  have huniq : ∀ w : C, w.val.val ∈ attachments G x identifier hfree → w = z := by
    intro w hw
    have hwC : w.val.val ∈ componentMembers G x identifier hfree C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,w.val.property,w.property⟩
    exact Subtype.ext (Subtype.ext (one_attachment_vertex_unique G x identifier hfree C v t hpairs hwC hw))
  obtain ⟨j,hzj,hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
  have hpath : isPathComponent G x identifier hfree C := ⟨a,b,p,hp,hcover,hgraph⟩
  have hradius := unique_attachment_radius G x identifier hfree C hC z huniq
  have hd0 : C.toSimpleGraph.dist (p.getVert 0) (p.getVert j) ≤ 3 := by
    simpa only [SimpleGraph.Walk.getVert_zero,hzj] using hradius.1 a
  have hdL : C.toSimpleGraph.dist (p.getVert p.length) (p.getVert j) ≤ 3 := by
    simpa only [SimpleGraph.Walk.getVert_length,hzj] using hradius.1 b
  have h0 := path_index_distance_bound G x identifier hfree C hpath a b p hp 0 j 3 (by omega) hj hd0
  have hL := path_index_distance_bound G x identifier hfree C hpath a b p hp p.length j 3 le_rfl hj hdL
  refine ⟨j,hj,by simpa only [hzj] using hzA,?_,by omega,by omega,?_⟩
  · intro k hk hne hA
    have he := huniq (p.getVert k) hA
    have he' : p.getVert k = p.getVert j := he.trans hzj.symm
    exact hne (hp.getVert_injOn hk hj he')
  · intro hend
    have hdistinct := one_attachment_distinct G x identifier hfree C hone
    have hma : a.val.val ∈ componentMembers G x identifier hfree C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩
    have hmb : b.val.val ∈ componentMembers G x identifier hfree C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,b.val.property,b.property⟩
    have hna := free_end_not_branch G x identifier hfree C hC a b p hp hgraph
      (attachment_fiber_le_one G x identifier hfree C hdistinct hma)
    have hnb := free_end_not_branch G x identifier hfree C hC b a p.reverse hp.reverse
      (by simpa only [SimpleGraph.Walk.toSubgraph_reverse] using hgraph)
      (attachment_fiber_le_one G x identifier hfree C hdistinct hmb)
    rcases hend with he | he
    · have hza : z = a := by simpa only [he,SimpleGraph.Walk.getVert_zero] using hzj.symm
      have hd : C.toSimpleGraph.dist (p.getVert p.length) (p.getVert j) ≤ 2 := by
        simpa only [SimpleGraph.Walk.getVert_length,hzj] using hradius.2 (by simpa only [hza] using hna) b
      have hbnd := path_index_distance_bound G x identifier hfree C hpath a b p hp p.length j 2 le_rfl hj hd
      omega
    · have hzb : z = b := by simpa only [he,SimpleGraph.Walk.getVert_length] using hzj.symm
      have hd : C.toSimpleGraph.dist (p.getVert 0) (p.getVert j) ≤ 2 := by
        simpa only [SimpleGraph.Walk.getVert_zero,hzj] using hradius.2 (by simpa only [hzb] using hnb) a
      have hbnd := path_index_distance_bound G x identifier hfree C hpath a b p hp 0 j 2 (by omega) hj hd
      omega

end Paper.TotalDomination.HighGirthSetup
