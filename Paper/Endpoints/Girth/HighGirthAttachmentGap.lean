import Paper.Endpoints.Girth.HighGirthPathIndices
set_option maxHeartbeats 200000
namespace Paper.HighGirthAttachmentGap

theorem consecutive_attachment_gap
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.isFreePath G x K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ v : K, v ∈ p.support)
    (i j : Nat) (hij : i < j) (hj : j ≤ p.length)
    (hiA : (p.getVert i).val.val ∈ Paper.HighGirthAttachments.vertices G x)
    (hjA : (p.getVert j).val.val ∈ Paper.HighGirthAttachments.vertices G x)
    (hconsecutive : ∀ k : Nat, i < k → k < j →
      (p.getVert k).val.val ∉ Paper.HighGirthAttachments.vertices G x) :
    j - i ≤ 5 := by
  classical
  by_contra hn
  let m := i + 3
  have hm : m ≤ p.length := by dsimp [m]; omega
  obtain ⟨v,hvA,hvnear⟩ := Paper.HighGirthPathMetric.attachment_radius_two G x K hfree.2 (p.getVert m)
  obtain ⟨k,hkv,hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover v)
  have hnear : K.toSimpleGraph.dist (p.getVert m) (p.getVert k) ≤ 2 := by
    simpa only [hkv] using hvnear
  have hbetween : i < k ∧ k < j := by
    by_cases hmk : m ≤ k
    · have hd := Paper.HighGirthPathIndices.ordered_index_distance G x K hfree.1 a b p hp m k hmk hk
      rw [hd] at hnear
      dsimp [m] at *
      omega
    · have hkm : k ≤ m := by omega
      have hd := Paper.HighGirthPathIndices.ordered_index_distance G x K hfree.1 a b p hp k m hkm hm
      rw [SimpleGraph.dist_comm,hd] at hnear
      dsimp [m] at *
      omega
  exact hconsecutive k hbetween.1 hbetween.2 (by simpa only [hkv] using hvA)

end Paper.HighGirthAttachmentGap

#print axioms Paper.HighGirthAttachmentGap.consecutive_attachment_gap
