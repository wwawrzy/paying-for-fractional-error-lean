import Paper.Endpoints.Girth.HighGirthTrimmedTwoAttachments

namespace Paper.HighGirthFreeTrim

theorem exists_trim
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : HighGirthFreePaths.isFreePath G x K) :
    ∃ S : Finset V, S.Nonempty ∧ S ⊆ HighGirthFreePaths.members G x K ∧
      (G.induce (↑S : Set V)).Connected ∧
      (∀ u ∈ HighGirthFreePaths.members G x K, u ∈ HighGirthAttachments.vertices G x → u ∈ S) ∧
      S.card + 4 ≤ 5 * HighGirthComponentAttachments.count G x K ∧
      (HighGirthComponentAttachments.count G x K = 2 →
        K ∉ HighGirthFewAttachments.twoFamily G x → S.card ≤ 5) := by
  classical
  obtain ⟨a,b,p,hp,hcover,_⟩ := hfree.1
  have hc := HighGirthAttachmentPositionCount.attachment_positions_count G x K hfree a b p hp hcover
  let hS := hc.1
  let S := HighGirthTrimmedPath.vertices G x K p hS
  have hs := HighGirthTrimmedSupport.trimmed_path_support G x K a b p hS
  have hb := HighGirthTrimmedSize.trimmed_path_size_and_attachments G x K hfree a b p hp hcover
  refine ⟨S,hs.1,hs.2.1,HighGirthTrimmedConnected.trimmed_path_connected G x K a b p hS,hb.2,?_,?_⟩
  · have hpos := Finset.card_pos.mpr hc.1
    have hle := hc.2
    have hb' : S.card ≤ 5 * HighGirthComponentAttachments.count G x K - 4 := hb.1
    omega
  · intro hcount hnot
    exact HighGirthTrimmedTwoAttachments.two_attachments_trimmed_size G x K hfree hcount hnot a b p hp hcover

end Paper.HighGirthFreeTrim
#print axioms Paper.HighGirthFreeTrim.exists_trim
