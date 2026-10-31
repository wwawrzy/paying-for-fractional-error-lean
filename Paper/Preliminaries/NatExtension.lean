import Paper.Preliminaries.InducedCover
import Paper.Preliminaries.IntegralTable

/-! Exact natural-valued zero extension between an induced physical task
and the public vertex universe. This is a proof bridge, not a decoder or
global input supplied to the broadcast program. -/
namespace Paper.NatExtension
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]

def extend (H : Finset V) (p : ↥(H : Set V) → ℕ) (v : V) : ℕ :=
  if hv : v ∈ H then p ⟨v, hv⟩ else 0

theorem at_subtype (H : Finset V) (p : ↥(H : Set V) → ℕ) (v : ↥(H : Set V)) :
    extend H p v.val = p v := dif_pos v.property

theorem outside (H : Finset V) (p : ↥(H : Set V) → ℕ) :
    ∀ v, v ∉ H → extend H p v = 0 := by
  intro v hv
  exact dif_neg hv

theorem sum (H : Finset V) (p : ↥(H : Set V) → ℕ) :
    (∑ v, extend H p v) = ∑ v : ↥(H : Set V), p v := by
  calc
    _ = ∑ v ∈ H, extend H p v := (Finset.sum_subset (Finset.subset_univ _)
      (fun v _ hv => outside H p v hv)).symm
    _ = ∑ v : ↥(H : Set V), extend H p v.val := (Finset.sum_coe_sort H _).symm
    _ = _ := Finset.sum_congr rfl (fun v _ => at_subtype H p v)

theorem weighted (H : Finset V) (p : ↥(H : Set V) → ℕ) (c : V → ℕ) :
    IntegralTable.cost c (extend H p) = IntegralTable.cost (fun v : ↥(H : Set V) => c v.val) p := by
  unfold IntegralTable.cost
  calc
    _ = ∑ v ∈ H, c v * extend H p v := (Finset.sum_subset (Finset.subset_univ _)
      (fun v _ hv => by rw [outside H p v hv, mul_zero])).symm
    _ = ∑ v : ↥(H : Set V), c v.val * extend H p v.val := (Finset.sum_coe_sort H _).symm
    _ = _ := Finset.sum_congr rfl (fun v _ => by rw [at_subtype])

theorem closed_sum (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V)
    (p : ↥(H : Set V) → ℕ) (r : ↥(H : Set V)) :
    (∑ v ∈ closed G r.val, extend H p v) = ∑ v ∈ closed (G.induce (H : Set V)) r, p v := by
  calc
    _ = ∑ v ∈ closed G r.val ∩ H, extend H p v :=
      (Finset.sum_subset Finset.inter_subset_left (fun v hv hvnot =>
        outside H p v (fun hH => hvnot (Finset.mem_inter.mpr ⟨hv, hH⟩)))).symm
    _ = ∑ v ∈ closed (G.induce (H : Set V)) r, extend H p v.val := by
      rw [← InducedCover.closed_image G H r, Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)]
    _ = _ := Finset.sum_congr rfl (fun v _ => at_subtype H p v)

theorem extend_restrict (H : Finset V) (p : V → ℕ)
    (hz : ∀ v, v ∉ H → p v = 0) : extend H (fun v => p v.val) = p := by
  funext v
  by_cases hv : v ∈ H
  · exact dif_pos hv
  · simpa only [extend, dif_neg hv] using (hz v hv).symm

theorem restrict_weighted (H : Finset V) (p : V → ℕ) (c : V → ℕ)
    (hz : ∀ v, v ∉ H → p v = 0) :
    IntegralTable.cost (fun v : ↥(H : Set V) => c v.val) (fun v => p v.val) = IntegralTable.cost c p := by
  rw [← weighted, extend_restrict H p hz]
end Paper.NatExtension
