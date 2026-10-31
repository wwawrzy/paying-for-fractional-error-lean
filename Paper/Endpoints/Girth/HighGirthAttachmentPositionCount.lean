import Paper.Endpoints.Girth.HighGirthAttachmentPositions
set_option maxHeartbeats 200000
namespace Paper.HighGirthAttachmentPositionCount

theorem attachment_positions_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.isFreePath G x K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ v : K, v ∈ p.support) :
    (Paper.HighGirthAttachmentPositions.positions G x K p).Nonempty ∧
    (Paper.HighGirthAttachmentPositions.positions G x K p).card ≤
      Paper.HighGirthComponentAttachments.count G x K := by
  classical
  let S := Paper.HighGirthAttachmentPositions.positions G x K p
  constructor
  · obtain ⟨u,huK,huA⟩ := (Paper.HighGirthFreeAttachments.branches_and_attachment_exists G x K hfree.2).2
    obtain ⟨huU,huC⟩ := (Finset.mem_filter.mp huK).2
    let v : K := ⟨⟨u,huU⟩,huC⟩
    obtain ⟨i,hiv,hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover v)
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
    have hval : (p.getVert i).val.val = u := congrArg (fun z : K => z.val.val) hiv
    simpa only [hval] using huA
  · have hex : ∀ i ∈ S, ∃ t ∈ Paper.HighGirthAttachments.connectors G x, G.Adj (p.getVert i).val.val t := by
      intro i hi
      have hiA := (Finset.mem_filter.mp hi).2
      exact (Finset.mem_filter.mp hiA).2
    let f : Nat → V × V := fun i => ((p.getVert i).val.val,
      if hi : i ∈ S then Classical.choose (hex i hi) else a.val.val)
    have hf : ∀ i ∈ S, (f i).2 ∈ Paper.HighGirthAttachments.connectors G x ∧ G.Adj (p.getVert i).val.val (f i).2 := by
      intro i hi
      simpa only [f,dif_pos hi] using Classical.choose_spec (hex i hi)
    have hmaps : Set.MapsTo f (↑S : Set Nat) (↑(Paper.HighGirthComponentAttachments.pairs G x K) : Set (V × V)) := by
      intro i hi
      have hzK : (p.getVert i).val.val ∈ Paper.HighGirthFreePaths.members G x K :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(p.getVert i).val.property,(p.getVert i).property⟩
      have hzU := (Finset.mem_filter.mp hzK).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hzU,(hf i hi).1⟩,(hf i hi).2⟩,hzK⟩
    have hinj : Set.InjOn f (↑S : Set Nat) := by
      intro i hi j hj heq
      have hiL : i ≤ p.length := by have h := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega
      have hjL : j ≤ p.length := by have h := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega
      have hv : (p.getVert i).val.val = (p.getVert j).val.val := congrArg Prod.fst heq
      exact hp.getVert_injOn hiL hjL (Subtype.ext (Subtype.ext hv))
    change S.card ≤ (Paper.HighGirthComponentAttachments.edges G x K).card
    rw [(Paper.HighGirthComponentAttachmentCounts.component_attachment_counts G x K).1]
    exact Finset.card_le_card_of_injOn f hmaps hinj

end Paper.HighGirthAttachmentPositionCount

#print axioms Paper.HighGirthAttachmentPositionCount.attachment_positions_count
