import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskPointwise

/-! Exact deterministic finite-role numerator equals the public-coin mean
of the actual physical randomized program's retained task vector. This
uses pointwise execution equality, including its genuine private input. -/
namespace Paper.GeneralCoveringOwnerFrameTaskPhysicalMean
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open GeneralCoveringOwnerFrameTaskData GeneralCoveringOwnerFrameTaskInputs
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem mean {ids B : ℕ} (I : BitCode V ids) (L Δ a k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n q : ℕ) (hB : 1 ≤ B) (s : V → Input V B)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1)) (v : V) :
    ((((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v).1).val : ℝ) /
        GeneralCoveringOwnerFrameFractional.denominator Δ k b n q =
      (∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        (((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
          (GeneralCoveringOwnerFrameTaskPointwise.randomInput s β) v).1.2.2.1 : ℝ) / q) /
        Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := by
  rw [GeneralCoveringOwnerFrameFractionalMean.vector_mean G I L Δ a B k t b n q hB
    d.cover d.targets d.D d.R d.incidence d.local_rows s d.center d.demand d.candidates d.inverse v]
  let f := fun (β : V → ActiveFiniteBitPartition.Bits Δ k b n) (anchor : V) (mask : Fin (partSlots Δ k) → Bool) =>
    ((GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s anchor v
      (GeneralCoveringOwnerFrameTaskCandidates.candidate G I d.cover d.D d.R L Δ k t b n β anchor mask)).val : ℝ)
  let A := (frames G I L Δ k n s v).anchors
  have hswap : (∑ anchor ∈ A, ∑ mask : Fin (partSlots Δ k) → Bool,
      ∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        f β anchor mask / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n)) =
      ∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        ∑ anchor ∈ A, ∑ mask : Fin (partSlots Δ k) → Bool,
          f β anchor mask / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := by
    calc
      _ = ∑ anchor ∈ A, ∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
          ∑ mask : Fin (partSlots Δ k) → Bool,
            f β anchor mask / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := by
        apply Finset.sum_congr rfl
        intro anchor _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hpoint (β : V → ActiveFiniteBitPartition.Bits Δ k b n) :
      (∑ anchor ∈ A, ∑ mask : Fin (partSlots Δ k) → Bool, f β anchor mask) =
        (((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
          (GeneralCoveringOwnerFrameTaskPointwise.randomInput s β) v).1.2.2.1 : ℝ) := by
    dsimp only [f, A]
    exact_mod_cast GeneralCoveringOwnerFrameTaskPointwise.sum G I L Δ k hk t ht b n s d β a q hB v
  calc
    _ = ((∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        ∑ anchor ∈ A, ∑ mask : Fin (partSlots Δ k) → Bool, f β anchor mask) /
          Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n)) / q := by
      congr 1
      simpa only [GeneralCoveringOwnerFrameFractionalMean.globalMean,
        GeneralCoveringOwnerFrameTaskCandidates.candidate, f, A, Finset.sum_div] using hswap
    _ = ((∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        (((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
          (GeneralCoveringOwnerFrameTaskPointwise.randomInput s β) v).1.2.2.1 : ℝ)) /
          Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n)) / q := by
      exact congrArg (fun z : ℝ =>
        (z / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n)) / q)
          (Finset.sum_congr rfl (fun β _ => hpoint β))
    _ = ((∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        (((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
          (GeneralCoveringOwnerFrameTaskPointwise.randomInput s β) v).1.2.2.1 : ℝ)) / q) /
          Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := div_right_comm _ _ _
    _ = _ := by rw [Finset.sum_div]

end Paper.GeneralCoveringOwnerFrameTaskPhysicalMean

#print axioms Paper.GeneralCoveringOwnerFrameTaskPhysicalMean.mean
