import Paper.Averaging.Tasks.MaskedTaskGraph
import Paper.Preliminaries.InducedCover

/-! Public-ID masked partial LP equals the actual induced-subtype LP.
Outside coordinates can be set to zero without increasing nonnegative cost. -/
namespace Paper.MaskedLP
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def extend (H : Finset V) (z : ↥(H : Set V) → ℝ) (v : V) : ℝ :=
  if hv : v ∈ H then z ⟨v, hv⟩ else 0

theorem extend_at (H : Finset V) (z : ↥(H : Set V) → ℝ) (v : ↥(H : Set V)) :
    extend H z v.val = z v := by
  have hv : v.val ∈ H := v.property
  rw [extend, dif_pos hv]

theorem closed_sum (H : Finset V) (r : ↥(H : Set V)) (f : V → ℝ) :
    (∑ u ∈ closed (G.induce (H : Set V)) r, f u.val) = ∑ u ∈ closed G r.val ∩ H, f u := by
  rw [← InducedCover.closed_image G H r, Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)]

theorem restrict_feasible (H R : Finset V) (hR : R ⊆ H) (x : V → ℝ)
    (hx : PartialOptimum.Feasible (MaskedTaskGraph.graph G H) R x) :
    PartialOptimum.Feasible (G.induce (H : Set V)) (InducedSubsets.lift H R) (fun v => x v.val) := by
  refine ⟨fun v => hx.1 v.val, ?_⟩
  intro r hr
  have hrR := Finset.mem_subtype.mp hr
  rw [closed_sum G H r, ← MaskedTaskGraph.closed_inside G H r.val r.property]
  exact hx.2 r.val hrR

theorem extend_feasible (H R : Finset V) (hR : R ⊆ H) (z : ↥(H : Set V) → ℝ)
    (hz : PartialOptimum.Feasible (G.induce (H : Set V)) (InducedSubsets.lift H R) z) :
    PartialOptimum.Feasible (MaskedTaskGraph.graph G H) R (extend H z) := by
  refine ⟨fun v => ?_, ?_⟩
  · unfold extend
    split_ifs with hv
    · exact hz.1 ⟨v, hv⟩
    · exact le_rfl
  · intro r hr
    let u : ↥(H : Set V) := ⟨r, hR hr⟩
    have hh := hz.2 u (Finset.mem_subtype.mpr hr)
    have he : (∑ v ∈ closed (G.induce (H : Set V)) u, z v) =
        ∑ v ∈ closed (MaskedTaskGraph.graph G H) r, extend H z v := by
      rw [MaskedTaskGraph.closed_inside G H r (hR hr), ← closed_sum G H u (extend H z)]
      apply Finset.sum_congr rfl
      intro v _
      exact (extend_at H z v).symm
    exact he ▸ hh

theorem extend_cost (H : Finset V) (c : V → ℝ) (z : ↥(H : Set V) → ℝ) :
    PartialOptimum.objective c (extend H z) =
      PartialOptimum.objective (fun v : ↥(H : Set V) => c v.val) z := by
  have he : (∑ v ∈ H, c v * extend H z v) =
      PartialOptimum.objective (fun v : ↥(H : Set V) => c v.val) z := by
    rw [← Finset.sum_coe_sort H (fun v => c v * extend H z v)]
    apply Finset.sum_congr rfl
    intro v _
    rw [extend_at]
  rw [← he]
  symm
  apply Finset.sum_subset (Finset.subset_univ H)
  intro v _ hv
  rw [extend, dif_neg hv, mul_zero]

theorem restrict_cost_le (H : Finset V) (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v) :
    PartialOptimum.objective (fun v : ↥(H : Set V) => c v.val) (fun v => x v.val) ≤
      PartialOptimum.objective c x := by
  change (∑ v : ↥(H : Set V), c v.val * x v.val) ≤ ∑ v, c v * x v
  calc
    _ = ∑ v ∈ H, c v * x v := Finset.sum_coe_sort H (fun v => c v * x v)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      (fun v _ _ => mul_nonneg (hc v) (hx v))
end Paper.MaskedLP
