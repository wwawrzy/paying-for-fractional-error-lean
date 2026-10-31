import Paper.Endpoints.Girth.HighGirthNonfreeRegion
import Paper.Endpoints.Girth.HighGirthResidualSize
set_option maxHeartbeats 200000
namespace Paper.HighGirthNonfreeSize

theorem nonfree_region_size_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (Paper.HighGirthNonfreeRegion.vertices G x).card ≤
      5 * (Paper.HighGirthNonfreeRegion.attachments G x).card +
      4 * (Paper.HighGirthRounding.middle G x).card := by
  classical
    let N := Paper.HighGirthNonfreeRegion.vertices G x
    let A := Paper.HighGirthNonfreeRegion.attachments G x
    let L := Paper.HighGirthRounding.middle G x
    let B := Paper.HighGirthAccessSets.uBallTwo G x
    let C := Paper.HighGirthAccessSets.lAccessTwo G x
    have hcover : N ⊆ (A.biUnion B) ∪ (L.biUnion C) := by
      intro u hu
      have huN : u ∈ Paper.HighGirthRounding.last G x ∧ u ∉ Paper.HighGirthNonfreeRegion.freeVertices G x := Finset.mem_sdiff.mp hu
      rcases Finset.mem_union.mp (Paper.HighGirthAccessCover.residual_access_cover G x huN.1) with huB | huC
      · obtain ⟨a,haA,huB⟩ := Finset.mem_biUnion.mp huB
        have haU : a ∈ Paper.HighGirthRounding.last G x := (Finset.mem_filter.mp haA).1
        have haN : a ∈ N := by
          apply Finset.mem_sdiff.mpr
          refine ⟨haU,?_⟩
          intro haF
          obtain ⟨K,hKF,haK⟩ := Finset.mem_biUnion.mp haF
          have huK := Paper.HighGirthComponentBalls.ball_stays_in_component G x K a haK huB
          exact huN.2 (Finset.mem_biUnion.mpr ⟨K,hKF,huK⟩)
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨a,Finset.mem_inter.mpr ⟨haA,haN⟩,huB⟩)
      · exact Finset.mem_union_right _ huC
    have hb : ∀ a ∈ A, (B a).card ≤ 5 := by
      intro a ha
      have haA : a ∈ Paper.HighGirthAttachments.vertices G x := (Finset.mem_inter.mp ha).1
      exact Paper.HighGirthUBall.u_ball_two_card G x a (Finset.mem_filter.mp haA).1
    have hc : ∀ l ∈ L, (C l).card ≤ 4 := by
      intro l hl
      exact Paper.HighGirthLAccess.l_access_two_card G x l hl
    have hB : (A.biUnion B).card ≤ 5 * A.card := by
      calc
        _ ≤ ∑ a ∈ A, (B a).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ A, 5 := Finset.sum_le_sum hb
        _ = 5 * A.card := by simp [Nat.mul_comm]
    have hC : (L.biUnion C).card ≤ 4 * L.card := by
      calc
        _ ≤ ∑ l ∈ L, (C l).card := Finset.card_biUnion_le
        _ ≤ ∑ _l ∈ L, 4 := Finset.sum_le_sum hc
        _ = 4 * L.card := by simp [Nat.mul_comm]
    change N.card ≤ 5 * A.card + 4 * L.card
    calc
      _ ≤ ((A.biUnion B) ∪ (L.biUnion C)).card := Finset.card_le_card hcover
      _ ≤ (A.biUnion B).card + (L.biUnion C).card := Finset.card_union_le _ _
      _ ≤ 5 * A.card + 4 * L.card := Nat.add_le_add hB hC

end Paper.HighGirthNonfreeSize

#print axioms Paper.HighGirthNonfreeSize.nonfree_region_size_bound
