import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameAverage
import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskPhysicalMean
import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairPhysicalMean

/-! The entire actual deterministic numerator equals the finite mean of
the entire actual randomized numerator, over the identical original input.
Task and repair means share the public global experiment in this proof;
the executable programs enumerate only their delivered finite frames. -/
namespace Paper.GeneralCoveringOwnerFrameAverageMean
open BroadcastModel
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem product_quotient (p h A D : ℕ) (hA : 0 < A) (hD : 0 < D) :
    ((p * D + A * h : ℕ) : ℝ) / (A * D : ℕ) = (p : ℝ) / A + (h : ℝ) / D := by
  have hAr : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp [hAr, hDr]

private theorem split {ids B : ℕ} (I : BitCode V ids) (L Δ a k t b n q : ℕ) (hq : 0 < q) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwnerFrameAverage.Input V B) (v : V) :
    ((((GeneralCoveringOwnerFrameAverage.program I L Δ a B k t b n q hB).runEncoded G s v).1).val : ℝ) /
        GeneralCoveringOwnerFrameAverage.denominator L Δ k b n q =
      ((((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v).1).val : ℝ) /
        GeneralCoveringOwnerFrameFractional.denominator Δ k b n q +
      (GeneralCoveringOwnerRepairUnion.count I k t b n
        (GeneralCoveringOwnerRepairUnionNative.source G L Δ (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n)
          (fun u => (s u).1) I v)
        (GeneralCoveringOwnerRepairUnionNative.observed G L Δ (GeneralCoveringOwnerFrameTaskInputs.outerRadius k n)
          (fun u => (s u).1) I v) : ℝ) /
        GeneralCoveringOwnerFrameAverage.repairDenominator L Δ k b n := by
  rw [GeneralCoveringOwnerFrameAverage.numerator G I L Δ a B k t b n q hB s v,
    GeneralCoveringOwnerFrameAverage.task_retained G I L Δ a B k t b n q hB s v,
    GeneralCoveringOwnerFrameAverage.rootFrames_retained G I L Δ a B k t b n q hB s v,
    GeneralCoveringOwnerFrameAverage.observer_retained G I L Δ a B k t b n q hB s v]
  exact product_quotient _ _ _ _
    (GeneralCoveringOwnerFrameFractional.denominator_pos Δ k b n q hq) (FiniteLocalMean.denominator_pos _)

theorem mean {ids B : ℕ} (I : BitCode V ids) (L Δ a k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n q : ℕ) (hq : 0 < q) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwnerFrameAverage.Input V B)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun u => (s u).1)) (v : V) :
    ((((GeneralCoveringOwnerFrameAverage.program I L Δ a B k t b n q hB).runEncoded G s v).1).val : ℝ) /
        GeneralCoveringOwnerFrameAverage.denominator L Δ k b n q =
      (∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        (((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G
          (GeneralCoveringOwnerFrameTaskPointwise.randomInput s β) v).1.1 : ℝ) / q) /
          Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := by
  let r := GeneralCoveringOwnerFrameTaskInputs.outerRadius k n
  have hr : GeneralCoveringOwnerFramePartition.radius k n ≤ r := by
    dsimp only [r, GeneralCoveringOwnerFrameTaskInputs.outerRadius, GeneralCoveringOwnerFrameTaskData.frameRadius]
    omega
  have htask := GeneralCoveringOwnerFrameTaskPhysicalMean.mean G I L Δ a k hk t ht b n q hB s d v
  have hrepair := GeneralCoveringOwnerRepairPhysicalMean.mean G I L Δ r a k q t b n hB hr
    (fun u => (s u).1) d (fun u => (s u).2) v
  have hinput (β : V → ActiveFiniteBitPartition.Bits Δ k b n) :
      (fun u => ((s u).1, ((s u).2, β u))) = GeneralCoveringOwnerFrameTaskPointwise.randomInput s β := rfl
  simp only [hinput] at hrepair
  rw [split G I L Δ a k t b n q hq hB s v, htask]
  change _ + (GeneralCoveringOwnerRepairUnion.count I k t b n
    (GeneralCoveringOwnerRepairUnionNative.source G L Δ r (fun u => (s u).1) I v)
    (GeneralCoveringOwnerRepairUnionNative.observed G L Δ r (fun u => (s u).1) I v) : ℝ) /
      GeneralCoveringOwnerRepairUnion.denominator L Δ k b n r = _
  rw [hrepair, ← add_div, ← Finset.sum_add_distrib]
  apply congrArg (fun x : ℝ => x / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n))
  apply Finset.sum_congr rfl
  intro β _
  exact (GeneralCoveringOwnerRepairPhysical.quotient_decomposition G I L Δ a k q t b n hB hq
    (GeneralCoveringOwnerFrameTaskPointwise.randomInput s β) v).symm

end Paper.GeneralCoveringOwnerFrameAverageMean

#print axioms Paper.GeneralCoveringOwnerFrameAverageMean.mean
