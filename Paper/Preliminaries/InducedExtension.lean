import Paper.Preliminaries.InducedCover

/-! Extend a genuine induced-task vector by zero, preserving its weighted
cost and all task constraints whose candidates lie in the physical graph. -/
namespace Paper.InducedExtension
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def extend (H : Finset V) (z : ↥(H : Set V) → ℝ) (v : V) : ℝ :=
  if hv : v ∈ H then z ⟨v, hv⟩ else 0

theorem at_subtype (H : Finset V) (z : ↥(H : Set V) → ℝ) (v : ↥(H : Set V)) : extend H z v.val = z v :=
  dif_pos v.property

theorem nonneg (H : Finset V) (z : ↥(H : Set V) → ℝ) (hz : ∀ v, 0 ≤ z v) : ∀ v, 0 ≤ extend H z v := by
  intro v
  unfold extend
  split_ifs <;> first | exact hz _ | exact le_rfl

theorem cost (H : Finset V) (z : ↥(H : Set V) → ℝ) (c : V → ℝ) :
    PartialOptimum.objective c (extend H z) = PartialOptimum.objective (fun v => c v.val) z := by
  classical
  have he := Finset.sum_coe_sort H (fun v => c v * extend H z v)
  unfold PartialOptimum.objective
  calc
    _ = ∑ v ∈ H, c v * extend H z v := (Finset.sum_subset (Finset.subset_univ _)
      (fun v _ hv => by simp only [extend, dif_neg hv, mul_zero])).symm
    _ = ∑ v : ↥(H : Set V), c v.val * extend H z v.val := he.symm
    _ = _ := Finset.sum_congr rfl (fun v _ => by rw [at_subtype])

theorem closed_sum (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V)
    (z : ↥(H : Set V) → ℝ) (r : ↥(H : Set V)) (hclosed : closed G r.val ⊆ H) :
    (∑ v ∈ closed G r.val, extend H z v) = ∑ v ∈ closed (G.induce (H : Set V)) r, z v := by
  have h := InducedCover.closed_sum G H r (extend H z) hclosed
  simpa only [at_subtype] using h.symm

theorem feasible (G : SimpleGraph V) [DecidableRel G.Adj] (H R : Finset V)
    (hR : R ⊆ H) (hclosed : ∀ r ∈ R, closed G r ⊆ H) (z : ↥(H : Set V) → ℝ)
    (hz : PartialOptimum.Feasible (G.induce (H : Set V)) (InducedSubsets.lift H R) z) :
    PartialOptimum.Feasible G R (extend H z) := by
  refine ⟨nonneg H z hz.1, ?_⟩
  intro r hr
  let u : ↥(H : Set V) := ⟨r, hR hr⟩
  have hu : u ∈ InducedSubsets.lift H R := Finset.mem_subtype.mpr hr
  have hs := hz.2 u hu
  change 1 ≤ ∑ v ∈ closed G u.val, extend H z v
  rw [closed_sum G H z u (hclosed r hr)]
  exact hs
end Paper.InducedExtension
