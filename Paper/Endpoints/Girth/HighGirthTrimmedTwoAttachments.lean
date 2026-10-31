import Paper.Endpoints.Girth.HighGirthTrimmedConnected
import Paper.Endpoints.Girth.HighGirthFewAttachments
set_option maxHeartbeats 200000
namespace Paper.HighGirthTrimmedTwoAttachments

theorem two_attachments_trimmed_size
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.isFreePath G x K)
    (hcount : Paper.HighGirthComponentAttachments.count G x K = 2)
    (hnot : K ∉ Paper.HighGirthFewAttachments.twoFamily G x)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ v : K, v ∈ p.support) :
    let hS := (Paper.HighGirthAttachmentPositionCount.attachment_positions_count G x K hfree a b p hp hcover).1
    (Paper.HighGirthTrimmedPath.vertices G x K p hS).card ≤ 5 := by
  classical
    dsimp only
    let S := Paper.HighGirthAttachmentPositions.positions G x K p
    have hScount := Paper.HighGirthAttachmentPositionCount.attachment_positions_count G x K hfree a b p hp hcover
    let hS : S.Nonempty := hScount.1
    let m := S.min' hS
    let M := S.max' hS
    change (Paper.HighGirthTrimmedPath.vertices G x K p hS).card ≤ 5
    have hm : m ∈ S := Finset.min'_mem S hS
    have hM : M ∈ S := Finset.max'_mem S hS
    have hmM : m ≤ M := Finset.min'_le S _ hM
    have hcard : S.card ≤ 2 := by simpa only [hcount] using hScount.2
    have hML : M ≤ p.length := by
      have hh := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
      omega
    have hmA : (p.getVert m).val.val ∈ Paper.HighGirthAttachments.vertices G x := (Finset.mem_filter.mp hm).2
    have hMA : (p.getVert M).val.val ∈ Paper.HighGirthAttachments.vertices G x := (Finset.mem_filter.mp hM).2
    have hspan : M-m ≤ 4 := by
      by_cases heq : m = M
      · omega
      have hlt : m < M := by omega
      have hcon : ∀ k, m < k → k < M → (p.getVert k).val.val ∉ Paper.HighGirthAttachments.vertices G x := by
        intro k hmk hkM hkA
        have hk : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hkA⟩
        have hh : 2 < S.card := Finset.two_lt_card_iff.mpr ⟨m,k,M,hm,hk,hM,by omega,by omega,by omega⟩
        omega
      have hgap := Paper.HighGirthAttachmentGap.consecutive_attachment_gap G x K hfree a b p hp hcover m M hlt hML hmA hMA hcon
      have hne : M-m ≠ 5 := by
        intro hfive
        apply hnot
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,hfree,hcount,p.getVert m,p.getVert M,hmA,hMA,?_⟩
        rw [Paper.HighGirthPathIndices.ordered_index_distance G x K hfree.1 a b p hp m M hmM hML]
        exact hfive
      omega
    have hI : (Paper.HighGirthTrimmedPath.indices G x K p hS).card ≤ 5 := by
      change (Finset.Icc m M).card ≤ 5
      rw [Nat.card_Icc]
      omega
    exact Finset.card_image_le.trans hI

end Paper.HighGirthTrimmedTwoAttachments

#print axioms Paper.HighGirthTrimmedTwoAttachments.two_attachments_trimmed_size
