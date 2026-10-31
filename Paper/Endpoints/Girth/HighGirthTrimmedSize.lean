import Paper.Endpoints.Girth.HighGirthTrimmedPath
set_option maxHeartbeats 200000
namespace Paper.HighGirthTrimmedSize

theorem trimmed_path_size_and_attachments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.isFreePath G x K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ v : K, v ∈ p.support) :
    let hS := (Paper.HighGirthAttachmentPositionCount.attachment_positions_count G x K hfree a b p hp hcover).1
    (Paper.HighGirthTrimmedPath.vertices G x K p hS).card ≤
      5 * Paper.HighGirthComponentAttachments.count G x K - 4 ∧
    ∀ u ∈ Paper.HighGirthFreePaths.members G x K,
      u ∈ Paper.HighGirthAttachments.vertices G x →
      u ∈ Paper.HighGirthTrimmedPath.vertices G x K p hS := by
  classical
    dsimp only
    let S := Paper.HighGirthAttachmentPositions.positions G x K p
    have hScount := Paper.HighGirthAttachmentPositionCount.attachment_positions_count G x K hfree a b p hp hcover
    let hS : S.Nonempty := hScount.1
    have hgap : ∀ i ∈ S, ∀ j ∈ S, i < j → (∀ k ∈ S, i < k → k < j → False) → j - i ≤ 5 := by
      intro i hi j hj hij hn
      have hiA := (Finset.mem_filter.mp hi).2
      have hjA := (Finset.mem_filter.mp hj).2
      have hjL : j ≤ p.length := by have h := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega
      apply Paper.HighGirthAttachmentGap.consecutive_attachment_gap G x K hfree a b p hp hcover i j hij hjL hiA hjA
      intro k hik hkj hkA
      have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hkA⟩
      exact hn k hkS hik hkj
    have hspan := Paper.HighGirthFiniteGapSpan.span_of_gaps S hS hgap
    have hpos : 0 < S.card := Finset.card_pos.mpr hS
    have hminmax : S.min' hS ≤ S.max' hS := Finset.min'_le S _ (Finset.max'_mem S hS)
    change (Paper.HighGirthTrimmedPath.vertices G x K p hS).card ≤ _ ∧ _
    constructor
    · have hI : (Paper.HighGirthTrimmedPath.indices G x K p hS).card ≤ 5 * Paper.HighGirthComponentAttachments.count G x K - 4 := by
        change (Finset.Icc (S.min' hS) (S.max' hS)).card ≤ _
        rw [Nat.card_Icc]
        have hc : S.card ≤ Paper.HighGirthComponentAttachments.count G x K := hScount.2
        omega
      exact (Finset.card_image_le).trans hI
    · intro u huK huA
      obtain ⟨huU,huC⟩ := (Finset.mem_filter.mp huK).2
      let v : K := ⟨⟨u,huU⟩,huC⟩
      obtain ⟨i,hiv,hiL⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover v)
      have hval : (p.getVert i).val.val = u := congrArg (fun z : K => z.val.val) hiv
      have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by simpa only [hval] using huA⟩
      have hiI : i ∈ Paper.HighGirthTrimmedPath.indices G x K p hS :=
        Finset.mem_Icc.mpr ⟨Finset.min'_le S i hiS,Finset.le_max' S i hiS⟩
      exact Finset.mem_image.mpr ⟨i,hiI,hval⟩

end Paper.HighGirthTrimmedSize

#print axioms Paper.HighGirthTrimmedSize.trimmed_path_size_and_attachments
