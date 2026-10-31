import Paper.Endpoints.Girth.HighGirthAttachmentBudget

/-! Exact c1 and c2 from fv:hg:count. The c2 family includes all free paths
with two attachment edges, unlike b2 which also requires distance five. -/
namespace Paper.HighGirthFreeAttachmentClasses
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def one : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact (HighGirthComponentCounting.freeComponents G x).filter
    (fun K => HighGirthComponentAttachments.count G x K = 1)

noncomputable def two : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact (HighGirthComponentCounting.freeComponents G x).filter
    (fun K => HighGirthComponentAttachments.count G x K = 2)

theorem attachment_positive
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hK : K ∈ HighGirthComponentCounting.freeComponents G x) :
    0 < HighGirthComponentAttachments.count G x K := by
  classical
  have hf := (Finset.mem_filter.mp hK).2
  obtain ⟨u,huK,huA⟩ := (HighGirthFreeAttachments.branches_and_attachment_exists G x K hf).2
  obtain ⟨t,htT,hut⟩ := (Finset.mem_filter.mp huA).2
  have huU := (Finset.mem_filter.mp huK).2.1
  have hp : (u,t) ∈ HighGirthComponentAttachments.pairs G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huU,htT⟩,hut⟩,huK⟩
  change 0 < (HighGirthComponentAttachments.edges G x K).card
  rw [(HighGirthComponentAttachmentCounts.component_attachment_counts G x K).1]
  exact Finset.card_pos.mpr ⟨(u,t),hp⟩

end Paper.HighGirthFreeAttachmentClasses

#print axioms Paper.HighGirthFreeAttachmentClasses.one
#print axioms Paper.HighGirthFreeAttachmentClasses.two
#print axioms Paper.HighGirthFreeAttachmentClasses.attachment_positive
