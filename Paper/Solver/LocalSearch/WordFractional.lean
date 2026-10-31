import Paper.Solver.LocalSearch.SearchSpec
import Paper.Averaging.Tasks.TaskBenchmark

/-! Physical induced-task interpretation of an actually valid solution
word. All real arithmetic is in correctness, not in message/state codecs. -/
namespace Paper.WordFractional
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]

noncomputable def vector (H : Finset V) (q : ℕ) {B : ℕ} (w : SolutionWord.Word V B)
    (v : ↥(H : Set V)) : ℝ := (SolutionWord.copies w v.val : ℝ) / q

theorem spec (G : SimpleGraph V) [DecidableRel G.Adj] (H T : Finset V)
    {B q m : ℕ} (hq : 1 ≤ q) (c : V → Fin (B + 1)) (w : SolutionWord.Word V B)
    (hw : SearchSpec.Valid G H c (TaskBenchmark.demand (q := q) T) m w) :
    PartialOptimum.Feasible (G.induce (H : Set V)) (InducedSubsets.lift H T) (vector H q w) ∧
      PartialOptimum.objective (fun v : ↥(H : Set V) => ((c v.val).val : ℝ)) (vector H q w) =
        (SolutionWord.cost w : ℝ) / q ∧
      ∀ v, (q : ℝ) * vector H q w v = SolutionWord.copies w v.val := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hs := SearchSpec.copies_support G H c (TaskBenchmark.demand (q := q) T) m w hw
  have hcost := SearchSpec.exact_cost G H c (TaskBenchmark.demand (q := q) T) m w hw
  refine ⟨⟨fun v => div_nonneg (Nat.cast_nonneg _) hqp.le, ?_⟩, ?_, ?_⟩
  · intro r hr
    have hrT : r.val ∈ T := Finset.mem_subtype.mp hr
    have hc := hw.2.2.2 r.val
    change (if r.val ∈ T then q else 0) ≤ _ at hc
    rw [if_pos hrT] at hc
    have he := NatExtension.closed_sum G H (fun v => SolutionWord.copies w v.val) r
    rw [NatExtension.extend_restrict H (SolutionWord.copies w) hs] at he
    have hh : q ≤ ∑ v ∈ closed (G.induce (H : Set V)) r, SolutionWord.copies w v.val := hc.trans_eq he
    dsimp only [vector]
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hqp).mpr
    simpa only [one_mul] using (show (q : ℝ) ≤ ∑ v ∈ closed (G.induce (H : Set V)) r,
      (SolutionWord.copies w v.val : ℝ) by exact_mod_cast hh)
  · have he : PartialOptimum.objective (fun v : ↥(H : Set V) => ((c v.val).val : ℝ)) (vector H q w) =
        (IntegralTable.cost (fun v : ↥(H : Set V) => (c v.val).val) (fun v => SolutionWord.copies w v.val) : ℝ) / q := by
      simp [PartialOptimum.objective, vector, IntegralTable.cost, mul_div_assoc, Finset.sum_div]
    rw [he, NatExtension.restrict_weighted H (SolutionWord.copies w) (fun v => (c v).val) hs, hcost]
  · intro v
    dsimp only [vector]
    field_simp
end Paper.WordFractional
