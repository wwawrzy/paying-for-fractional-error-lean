import Paper.TotalDomination.HighGirthBadPaths

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def attachmentPositions
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    {a b : C} (p : C.toSimpleGraph.Walk a b) : Finset ℕ := by
  classical
  exact (Finset.range (p.length+1)).filter (fun i => (p.getVert i).val.val ∈ attachments G x identifier hfree)

theorem positions_image_pairs
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hcover : ∀ z : C, z ∈ p.support) :
    (attachmentPositions G x identifier hfree C p).image (fun i => (p.getVert i).val.val) =
      (componentAttachmentPairs G x identifier hfree C).image Prod.fst := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hA := (Finset.mem_filter.mp hi).2
    obtain ⟨t,ht,ha⟩ := (mem_neighbors G).mp (Finset.mem_inter.mp hA).2
    have hm : (p.getVert i).val.val ∈ componentMembers G x identifier hfree C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(p.getVert i).val.property,(p.getVert i).property⟩
    exact Finset.mem_image.mpr ⟨((p.getVert i).val.val,t),Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(p.getVert i).val.property,ht⟩,ha⟩,hm⟩,rfl⟩
  · intro hv
    obtain ⟨⟨u,t⟩,hu,rfl⟩ := Finset.mem_image.mp hv
    have huC := (Finset.mem_filter.mp hu).2
    have hpairs := (Finset.mem_filter.mp hu).1
    have hprod := (Finset.mem_filter.mp hpairs).1
    have ha := (Finset.mem_filter.mp hpairs).2
    obtain ⟨huS,hucomp⟩ := (Finset.mem_filter.mp huC).2
    let z : C := ⟨⟨u,huS⟩,hucomp⟩
    obtain ⟨i,hiz,hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
    have he : (p.getVert i).val.val = u := congrArg (fun z : C => z.val.val) hiz
    have hA : u ∈ attachments G x identifier hfree := Finset.mem_inter.mpr
      ⟨huS,(mem_neighbors G).mpr ⟨t,(Finset.mem_product.mp hprod).2,ha⟩⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),by simpa only [he] using hA⟩,he⟩

theorem attachment_positions_count
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath) (hcover : ∀ z : C, z ∈ p.support) :
    (attachmentPositions G x identifier hfree C p).Nonempty ∧
      (attachmentPositions G x identifier hfree C p).card =
        ((componentAttachmentPairs G x identifier hfree C).image Prod.fst).card ∧
      (attachmentPositions G x identifier hfree C p).card ≤ (componentAttachmentPairs G x identifier hfree C).card := by
  classical
  have hne : (attachmentPositions G x identifier hfree C p).Nonempty := by
    obtain ⟨u⟩ := C.connected_toSimpleGraph.nonempty
    have hex : ∃ z : C, z.val.val ∈ attachments G x identifier hfree := by
      rcases free_component_metric_access G x identifier hfree C hC u with ⟨z,hB,_⟩ | ⟨z,hA,_⟩
      · exact ⟨z,branch_attachment G x identifier hfree (Finset.mem_inter.mpr ⟨hB,z.val.property⟩)⟩
      · exact ⟨z,hA⟩
    obtain ⟨z,hA⟩ := hex
    obtain ⟨i,hiz,hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by simpa only [hiz] using hA⟩⟩
  have hinj : Set.InjOn (fun i => (p.getVert i).val.val) (attachmentPositions G x identifier hfree C p) := by
    intro i hi j hj he
    have hiL : i ≤ p.length := by have hh := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega
    have hjL : j ≤ p.length := by have hh := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega
    exact hp.getVert_injOn hiL hjL (Subtype.ext (Subtype.ext he))
  have heq := positions_image_pairs G x identifier hfree C a b p hcover
  have hcard : (attachmentPositions G x identifier hfree C p).card =
      ((componentAttachmentPairs G x identifier hfree C).image Prod.fst).card := by
    rw [← heq,Finset.card_image_of_injOn hinj]
  exact ⟨hne,hcard,by rw [hcard]; exact Finset.card_image_le⟩

end Paper.TotalDomination.HighGirthSetup
