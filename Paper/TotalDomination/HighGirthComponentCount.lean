import Paper.TotalDomination.HighGirthRetainedSize

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def middleIncident (y : V) : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent := by
  classical
  exact (pathComponents G x identifier hfree).filter
    (fun C => ∃ u ∈ componentMembers G x identifier hfree C, G.Adj y u)
noncomputable def linkedIncident (u : V) : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent := by
  classical
  exact (pathComponents G x identifier hfree).filter (fun C => u ∈ componentMembers G x identifier hfree C)

theorem linked_incident_card (u : V) : (linkedIncident G x identifier hfree u).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro C hC D hD
  exact component_member_unique G x identifier hfree C D (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2

theorem middle_incident_card {y : V} (hy : y ∈ served G (I G x identifier hfree)) :
    (middleIncident G x identifier hfree y).card ≤ 2 := by
  classical
  let F := middleIncident G x identifier hfree y
  by_cases hF : F.Nonempty
  · have hex : ∀ C : F, ∃ u ∈ componentMembers G x identifier hfree C.val, G.Adj y u :=
      fun C => (Finset.mem_filter.mp C.property).2
    let f : F → (↑(G.neighborFinset y ∩ core G x identifier hfree) : Set V) := fun C =>
      ⟨Classical.choose (hex C),Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y _).mpr (Classical.choose_spec (hex C)).2,
          component_subset_core G x identifier hfree C.val (Classical.choose_spec (hex C)).1⟩⟩
    have hinj : Function.Injective f := by
      intro C D he
      have he' : Classical.choose (hex C) = Classical.choose (hex D) := congrArg Subtype.val he
      apply Subtype.ext
      apply component_member_unique G x identifier hfree C.val D.val (Classical.choose_spec (hex C)).1
      rw [he']
      exact (Classical.choose_spec (hex D)).1
    have hc := Fintype.card_le_of_injective f hinj
    have hc' : F.card ≤ (G.neighborFinset y ∩ core G x identifier hfree).card := by simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hc
    obtain ⟨C,hC⟩ := hF
    obtain ⟨u,hu,ha⟩ := (Finset.mem_filter.mp hC).2
    have huS := component_subset_core G x identifier hfree C hu
    have hlow := low_residual_degree G x identifier hfree (Finset.mem_inter.mp hy).1 (Or.inr ⟨u,huS,ha⟩)
    have hn : (G.neighborFinset y ∩ core G x identifier hfree).card ≤ 2 :=
      (Finset.card_le_card (Finset.inter_subset_inter_left (core_residual G x identifier hfree))).trans hlow
    exact hc'.trans hn
  · change F.card ≤ 2
    simp [Finset.not_nonempty_iff_eq_empty.mp hF]

noncomputable def componentCover : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent := by
  classical
  exact freeComponents G x identifier hfree ∪
      (served G (I G x identifier hfree)).biUnion (middleIncident G x identifier hfree) ∪
      (linkedLast G x identifier hfree).biUnion (linkedIncident G x identifier hfree)

theorem path_components_cover : pathComponents G x identifier hfree ⊆ componentCover G x identifier hfree := by
  classical
  unfold componentCover
  intro C hC
  by_cases hf : C ∈ freeComponents G x identifier hfree
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hf)
  have hn : ¬freeComponent G x identifier hfree C := by
    intro hfreeC
    apply hf
    exact Finset.mem_filter.mpr ⟨(by simp only [Finset.mem_univ]),(Finset.mem_filter.mp hC).2,hfreeC⟩
  have hex : ∃ u, u ∈ componentMembers G x identifier hfree C ∧
      (u ∈ neighbors G (F G) ∨ u ∈ neighbors G (served G (I G x identifier hfree))) := by
    simpa only [freeComponent,not_forall,_root_.not_imp,not_and_or,not_not,exists_prop] using hn
  obtain ⟨u,hu,hF | hY⟩ := hex
  · have huS := component_subset_core G x identifier hfree C hu
    have hlink : u ∈ linkedLast G x identifier hfree := Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp huS).1,hF⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨u,hlink,Finset.mem_filter.mpr ⟨hC,hu⟩⟩)
  · obtain ⟨y,hy,ha⟩ := (mem_neighbors G).mp hY
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨y,hy,Finset.mem_filter.mpr ⟨hC,u,hu,ha.symm⟩⟩))

theorem path_component_count : (pathComponents G x identifier hfree).card ≤
    (freeComponents G x identifier hfree).card + 2*(served G (I G x identifier hfree)).card +
      (linkedLast G x identifier hfree).card := by
  classical
  have hY : ((served G (I G x identifier hfree)).biUnion (middleIncident G x identifier hfree)).card ≤
      2*(served G (I G x identifier hfree)).card := by
    calc
      _ ≤ ∑ y ∈ served G (I G x identifier hfree), (middleIncident G x identifier hfree y).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ served G (I G x identifier hfree), 2 := Finset.sum_le_sum fun y hy => middle_incident_card G x identifier hfree hy
      _ = _ := by simp [Nat.mul_comm]
  have hF : ((linkedLast G x identifier hfree).biUnion (linkedIncident G x identifier hfree)).card ≤
      (linkedLast G x identifier hfree).card := by
    calc
      _ ≤ ∑ u ∈ linkedLast G x identifier hfree, (linkedIncident G x identifier hfree u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ linkedLast G x identifier hfree, 1 := Finset.sum_le_sum fun u _ => linked_incident_card G x identifier hfree u
      _ = _ := by simp
  have hc := Finset.card_le_card (path_components_cover G x identifier hfree)
  unfold componentCover at hc
  have hU := Finset.card_union_le (freeComponents G x identifier hfree)
    ((served G (I G x identifier hfree)).biUnion (middleIncident G x identifier hfree))
  have hU' := Finset.card_union_le
    (freeComponents G x identifier hfree ∪ (served G (I G x identifier hfree)).biUnion (middleIncident G x identifier hfree))
    ((linkedLast G x identifier hfree).biUnion (linkedIncident G x identifier hfree))
  omega

theorem free_component_attachments_positive
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : isFreePathComponent G x identifier hfree C) :
    0 < (componentAttachmentPairs G x identifier hfree C).card := by
  obtain ⟨hpath,hfreeC⟩ := hC
  obtain ⟨a,b,p,hp,hcover,hgraph⟩ := hpath
  have hh := attachment_positions_count G x identifier hfree C hfreeC a b p hp hcover
  have hp := Finset.card_pos.mpr hh.1
  omega

theorem free_component_attachment_bound : 2*(freeComponents G x identifier hfree).card ≤
    (attachmentEdges G x identifier hfree).card + (badComponents G x identifier hfree).card := by
  classical
  let F := freeComponents G x identifier hfree
  have hpoint : ∀ C ∈ F, 4 ≤ 2*(componentAttachmentPairs G x identifier hfree C).card + badCorrection G x identifier hfree C := by
    intro C hC
    have hf : isFreePathComponent G x identifier hfree C := (Finset.mem_filter.mp hC).2
    have hp := free_component_attachments_positive G x identifier hfree C hf
    by_cases hb : Bad G x identifier hfree C
    · simp only [badCorrection,if_pos hb]
      omega
    · have hn : (componentAttachmentPairs G x identifier hfree C).card ≠ 1 := by
        intro hone
        exact hb ⟨hf.2,hf.1,Or.inl hone⟩
      simp only [badCorrection,if_neg hb,Nat.add_zero]
      omega
  have hh := Finset.sum_le_sum hpoint
  have hsum : 4*F.card ≤ 2*(∑ C ∈ F, (componentAttachmentPairs G x identifier hfree C).card) +
      2*(badComponents G x identifier hfree).card := by
    simpa only [F,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,
      free_bad_correction_sum,Nat.mul_comm] using hh
  have hbudget := nonfree_and_free_attachment_budget G x identifier hfree
  rw [attachment_edges_card G x identifier hfree]
  change 2*F.card ≤ _
  change (nonfreeAttachments G x identifier hfree).card+
      (∑ C ∈ F, (componentAttachmentPairs G x identifier hfree C).card) ≤ (attachmentPairs G x identifier hfree).card at hbudget
  omega

end Paper.TotalDomination.HighGirthSetup
#print axioms Paper.TotalDomination.HighGirthSetup.path_component_count
