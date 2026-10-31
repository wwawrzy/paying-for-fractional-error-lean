import Paper.Endpoints.Girth.HighGirthAccessCover
set_option maxHeartbeats 200000
namespace Paper.HighGirthResidualSize

theorem residual_size_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    (Paper.HighGirthRounding.last G x).card ≤
      5 * Paper.HighGirthAttachments.count G x +
      4 * (Paper.HighGirthRounding.middle G x).card := by
  classical
  let A := Paper.HighGirthAttachments.vertices G x
  let L := Paper.HighGirthRounding.middle G x
  let B := Paper.HighGirthAccessSets.uBallTwo G x
  let C := Paper.HighGirthAccessSets.lAccessTwo G x
  have hb : ∀ a ∈ A, (B a).card ≤ 5 := by
    intro a ha
    exact Paper.HighGirthUBall.u_ball_two_card G x a (Finset.mem_filter.mp ha).1
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
  have hcover := Finset.card_le_card (Paper.HighGirthAccessCover.residual_access_cover G x)
  have hUnion := Finset.card_union_le (A.biUnion B) (L.biUnion C)
  have hA : A.card ≤ Paper.HighGirthAttachments.count G x :=
    (Paper.HighGirthAttachmentCounts.attachment_count_bounds G x).2.1
  change (Paper.HighGirthRounding.last G x).card ≤
    5 * Paper.HighGirthAttachments.count G x + 4 * L.card
  calc
    _ ≤ ((A.biUnion B) ∪ (L.biUnion C)).card := hcover
    _ ≤ (A.biUnion B).card + (L.biUnion C).card := hUnion
    _ ≤ 5 * A.card + 4 * L.card := Nat.add_le_add hB hC
    _ ≤ 5 * Paper.HighGirthAttachments.count G x + 4 * L.card :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 5 hA) _

end Paper.HighGirthResidualSize

#print axioms Paper.HighGirthResidualSize.residual_size_bound
