import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairUnionNative
import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairPhysical

/-! Exact joint finite repair count equals the mean selected bit of the
unchanged actual physical randomized solver on the same original input. -/
namespace Paper.GeneralCoveringOwnerRepairPhysicalMean
open BroadcastModel
open GeneralCoveringOwnerFramePartition GeneralCoveringOwnerRepairUnion
open GeneralCoveringOwnerRepairUnionNative
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem mean {ids B : ℕ} (I : BitCode V ids) (L Δ r a k q t b n : ℕ) (hB : 1 ≤ B)
    (hr : GeneralCoveringOwnerFramePartition.radius k n ≤ r)
    (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input)
    (c : V → Fin (B + 1)) (v : V) :
    (count I k t b n (source G L Δ r input I v) (observed G L Δ r input I v) : ℝ) /
        denominator L Δ k b n r =
      (∑ β : V → Bits Δ k b n,
        ((if ((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
          (fun u => (input u, (c u, β u))) v).1.2.1.selected then 1 else 0 : ℕ) : ℝ)) /
          Fintype.card (V → Bits Δ k b n) := by
  rw [GeneralCoveringOwnerRepairUnion.mean]
  apply congrArg (fun x : ℝ => x / Fintype.card (V → Bits Δ k b n))
  apply Finset.sum_congr rfl
  intro β _
  apply congrArg Nat.cast
  rw [event_base G d.cover d.targets d.D d.R L Δ r k t b n hr
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse I v β]
  have ho : observed G L Δ r input I v =
      (GeneralCoveringOwnerRepairObserver.core I).runEncoded G
        (GeneralCoveringOwnerSimulation.learned G I L Δ input) v := by
    unfold observed
    rw [GeneralCoveringOwnerRepairFrames.environments_eq G L Δ r input I]
  rw [ho, ← GeneralCoveringOwnerRepairPhysical.selected G I L Δ a k q t b n hB input d c β v]

end Paper.GeneralCoveringOwnerRepairPhysicalMean

#print axioms Paper.GeneralCoveringOwnerRepairPhysicalMean.mean
