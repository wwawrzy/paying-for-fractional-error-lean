import Paper.TotalDomination.HighGirthSingleton

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem core_neighbors_le_one {p w : V} (hd : G.degree p = 2)
    (hw : w ∈ first G (I G x identifier hfree)) (ha : G.Adj p w) :
    (G.neighborFinset p ∩ core G x identifier hfree).card ≤ 1 := by
  have hn : w ∉ G.neighborFinset p ∩ core G x identifier hfree := fun h =>
    core_not_first G x identifier hfree (Finset.mem_inter.mp h).2 hw
  have hs : insert w (G.neighborFinset p ∩ core G x identifier hfree) ⊆ G.neighborFinset p := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (G.mem_neighborFinset p v).mpr ha
    · exact (Finset.mem_inter.mp hv).1
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hn,SimpleGraph.card_neighborFinset_eq_degree,hd] at hc
  omega

theorem common_exception_neighbor_unique
    (C D : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (p w : V) (hd : G.degree p = 2) (hw : w ∈ first G (I G x identifier hfree)) (ha : G.Adj p w)
    (hC : ∃ b ∈ componentMembers G x identifier hfree C, G.Adj p b)
    (hD : ∃ b ∈ componentMembers G x identifier hfree D, G.Adj p b) : C = D := by
  classical
  obtain ⟨b,hb,hpb⟩ := hC
  obtain ⟨z,hz,hpz⟩ := hD
  have hbN : b ∈ G.neighborFinset p ∩ core G x identifier hfree :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p b).mpr hpb,component_subset_core G x identifier hfree C hb⟩
  have hzN : z ∈ G.neighborFinset p ∩ core G x identifier hfree :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p z).mpr hpz,component_subset_core G x identifier hfree D hz⟩
  have he : b = z := Finset.card_le_one.mp (core_neighbors_le_one G x identifier hfree hd hw ha) b hbN z hzN
  rw [← he] at hz
  exact component_member_unique G x identifier hfree C D hb hz

theorem weighted_neighbors_le (S : Finset V) (hx : ∀ v, 0 ≤ x v) :
    (∑ v ∈ neighbors G S, x v) ≤ ∑ r ∈ S, ∑ v ∈ G.neighborFinset r, x v := by
  classical
  rw [HighGirthSelection.open_incidence_sum]
  calc
    _ ≤ ∑ v ∈ neighbors G S, ((G.neighborFinset v ∩ S).card : ℝ)*x v := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨r,hr,ha⟩ := (mem_neighbors G).mp hv
      have hp : 0 < (G.neighborFinset v ∩ S).card := Finset.card_pos.mpr
        ⟨r,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v r).mpr ha,hr⟩⟩
      have hpR : (1:ℝ) ≤ (G.neighborFinset v ∩ S).card := by exact_mod_cast hp
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpR (hx v)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => mul_nonneg (Nat.cast_nonneg _) (hx v))

noncomputable def firstOversupply : ℝ :=
  ∑ r ∈ first G (I G x identifier hfree) ∩ residual G (I G x identifier hfree),
    ((∑ v ∈ G.neighborFinset r, x v)-1)

theorem exceptional_count
    (family : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hfamily : ∀ C ∈ family, freeComponent G x identifier hfree C)
    (hE : ∀ C ∈ family, Exceptional G x identifier hfree C)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (family.card : ℝ) ≤ (first G (I G x identifier hfree)).card + firstOversupply G x identifier hfree := by
  classical
  let W := first G (I G x identifier hfree) ∩ residual G (I G x identifier hfree)
  have hex : ∀ C : family, ∃ p, x p = 1 ∧ G.degree p = 2 ∧
      (∃ w ∈ W, G.Adj p w) ∧ ∃ b ∈ componentMembers G x identifier hfree C.val, G.Adj p b := by
    intro C
    obtain ⟨b,p,hb,hp,hd,w,hw,ha⟩ := hE C.val C.property
    obtain ⟨hxp,_,_⟩ := singleton_charge_or_exception G x identifier hfree C.val
      (hfamily C.val C.property) b p hb hp hx hcap
    have hm : (b,p) ∈ componentAttachmentPairs G x identifier hfree C.val := by simp [hp]
    have hadj : G.Adj b p := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    exact ⟨p,hxp,hd,⟨w,hw,ha⟩,b,by simp [hb],hadj.symm⟩
  let pick : family → V := fun C => Classical.choose (hex C)
  have hpick : ∀ C : family, x (pick C) = 1 ∧ G.degree (pick C) = 2 ∧
      (∃ w ∈ W, G.Adj (pick C) w) ∧ ∃ b ∈ componentMembers G x identifier hfree C.val, G.Adj (pick C) b :=
    fun C => Classical.choose_spec (hex C)
  have hinj : Function.Injective pick := by
    intro C D he
    obtain ⟨w,hw,ha⟩ := (hpick C).2.2.1
    apply Subtype.ext
    apply common_exception_neighbor_unique G x identifier hfree C.val D.val (pick C) w
      (hpick C).2.1 (Finset.mem_inter.mp hw).1 ha (hpick C).2.2.2
    rw [he]
    exact (hpick D).2.2.2
  let P := family.attach.image pick
  have hcard : P.card = family.card := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
  have hsum : (∑ p ∈ P, x p) = (family.card : ℝ) := by
    calc
      _ = ∑ _p ∈ P, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hp
        exact (hpick C).1
      _ = _ := by simp [hcard]
  have hsub : P ⊆ neighbors G W := by
    intro p hp
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w,hw,ha⟩ := (hpick C).2.2.1
    exact (mem_neighbors G).mpr ⟨w,hw,ha⟩
  have hbound : (family.card : ℝ) ≤ ∑ r ∈ W, ∑ v ∈ G.neighborFinset r, x v := by
    rw [← hsum]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hx.1 p)).trans
      (weighted_neighbors_le G x W hx.1)
  have hsplit : (∑ r ∈ W, ∑ v ∈ G.neighborFinset r, x v) = W.card + firstOversupply G x identifier hfree := by
    unfold firstOversupply
    rw [Finset.sum_sub_distrib]
    simp [W]
  have hW : (W.card : ℝ) ≤ (first G (I G x identifier hfree)).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₁ := first G (I G x identifier hfree))
      (s₂ := residual G (I G x identifier hfree)))
  rw [hsplit] at hbound
  linarith

theorem core_first_oversupply_bound
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    coreOversupply G x identifier hfree + firstOversupply G x identifier hfree ≤ oversupply G (I G x identifier hfree) := by
  classical
  let row := fun r => (∑ v ∈ G.neighborFinset r, x v)-1
  have hd : Disjoint (core G x identifier hfree)
      (first G (I G x identifier hfree) ∩ residual G (I G x identifier hfree)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hw
    exact core_not_first G x identifier hfree hu (Finset.mem_inter.mp hw).1
  have hs : core G x identifier hfree ∪
      (first G (I G x identifier hfree) ∩ residual G (I G x identifier hfree)) ⊆ residual G (I G x identifier hfree) :=
    Finset.union_subset (core_residual G x identifier hfree) Finset.inter_subset_right
  change (∑ r ∈ core G x identifier hfree, row r) +
      (∑ r ∈ first G (I G x identifier hfree) ∩ residual G (I G x identifier hfree), row r) ≤
      ∑ r ∈ residual G (I G x identifier hfree), row r
  rw [← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun r hr _ =>
    sub_nonneg.mpr (hx.2 r (Finset.mem_sdiff.mp hr).1))

/-- Full aggregation, conditional only on the local charge for each actual
nonexceptional member. The remaining fv:hg:t-bad gap is the path-case proof. -/
theorem bad_family_bound
    (family : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hfamily : ∀ C ∈ family, freeComponent G x identifier hfree C)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1)
    (hlocal : ∀ C ∈ family, ¬Exceptional G x identifier hfree C →
      (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C) :
    (family.card : ℝ) ≤ (first G (I G x identifier hfree)).card +
      3*penalty G (I G x identifier hfree) (fun v => (c G v : ℝ)) + 3*oversupply G (I G x identifier hfree) := by
  classical
  let E := family.filter (Exceptional G x identifier hfree)
  let N := family.filter (fun C => ¬Exceptional G x identifier hfree C)
  have hE := exceptional_count G x identifier hfree E
    (fun C hC => hfamily C (Finset.mem_filter.mp hC).1)
    (fun C hC => (Finset.mem_filter.mp hC).2) hx hcap
  have hN := charged_family_bound G x identifier hfree N
    (fun C hC => hfamily C (Finset.mem_filter.mp hC).1) hx
    (fun C hC => hlocal C (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hC).2)
  have hc : E.card+N.card = family.card := Finset.card_filter_add_card_filter_not _
  have hcR : (E.card:ℝ)+(N.card:ℝ) = family.card := by exact_mod_cast hc
  have hΩ := core_first_oversupply_bound G x identifier hfree hx
  have hΩW : 0 ≤ firstOversupply G x identifier hfree := by
    apply Finset.sum_nonneg
    intro r hr
    exact sub_nonneg.mpr (hx.2 r (Finset.mem_sdiff.mp (Finset.mem_inter.mp hr).2).1)
  linarith

end Paper.TotalDomination.HighGirthSetup
