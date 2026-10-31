import Paper.Certificates.Counting.PartialOptimum
import Paper.Preliminaries.InducedSubsets

/-! Restrict a global covering vector to exactly the useful candidates in
an actual induced physical task. All its closed incidences are retained. -/
namespace Paper.InducedCover
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem closed_image (H : Finset V) (r : ↥(H : Set V)) :
    (closed (G.induce (H : Set V)) r).image Subtype.val = closed G r.val ∩ H := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have hh := (mem_closed (G.induce (H : Set V)) u r).mp hu
    refine Finset.mem_inter.mpr ⟨?_, u.property⟩
    exact (mem_closed G u.val r.val).mpr
      (hh.elim (fun he => Or.inl (congrArg Subtype.val he)) Or.inr)
  · intro hv
    have hh := Finset.mem_inter.mp hv
    refine Finset.mem_image.mpr ⟨⟨v, hh.2⟩, ?_, rfl⟩
    exact (mem_closed (G.induce (H : Set V)) _ r).mpr
      (((mem_closed G v r.val).mp hh.1).elim (fun he => Or.inl (Subtype.ext he)) Or.inr)

theorem closed_sum (H : Finset V) (r : ↥(H : Set V)) (f : V → ℝ)
    (hclosed : closed G r.val ⊆ H) :
    (∑ v ∈ closed (G.induce (H : Set V)) r, f v.val) = ∑ v ∈ closed G r.val, f v := by
  classical
  have hi := closed_image G H r
  rw [Finset.inter_eq_left.mpr hclosed] at hi
  rw [← hi, Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)]

noncomputable def mask (H S : Finset V) (x : V → ℝ) (v : ↥(H : Set V)) : ℝ :=
  if v.val ∈ S then x v.val else 0

theorem mask_feasible (H S R : Finset V) (hR : R ⊆ H) (hS : S ⊆ H)
    (hclosed : ∀ r ∈ R, closed G r ⊆ S) (x : V → ℝ) (hx : PartialOptimum.Feasible G R x) :
    PartialOptimum.Feasible (G.induce (H : Set V)) (InducedSubsets.lift H R) (mask H S x) := by
  classical
  refine ⟨fun v => by dsimp only [mask]; split_ifs <;> first | exact hx.1 _ | exact le_rfl, ?_⟩
  intro r hr
  have hrR : r.val ∈ R := Finset.mem_subtype.mp hr
  have hclosedH : closed G r.val ⊆ H := (hclosed r.val hrR).trans hS
  have he : (∑ v ∈ closed (G.induce (H : Set V)) r, mask H S x v) =
      ∑ v ∈ closed G r.val, x v := by
    calc
      _ = ∑ v ∈ closed (G.induce (H : Set V)) r, x v.val := by
        apply Finset.sum_congr rfl
        intro v hv
        have hv' : v.val ∈ closed G r.val := by
          have hm := Finset.mem_inter.mp (closed_image G H r ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩)
          exact hm.1
        exact if_pos (hclosed r.val hrR hv')
      _ = _ := closed_sum G H r x hclosedH
  rw [he]
  exact hx.2 r.val hrR

theorem mask_cost (H S : Finset V) (hS : S ⊆ H) (c x : V → ℝ) :
    PartialOptimum.objective (fun v : ↥(H : Set V) => c v.val) (mask H S x) = ∑ v ∈ S, c v * x v := by
  classical
  unfold PartialOptimum.objective mask
  have he : (∑ v : ↥(H : Set V), c v.val * (if v.val ∈ S then x v.val else 0)) =
      ∑ v ∈ H, if v ∈ S then c v * x v else 0 := by
    simp_rw [mul_ite, mul_zero]
    exact Finset.sum_coe_sort H (fun v : V => if v ∈ S then c v * x v else 0)
  rw [he, ← Finset.sum_filter]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
end Paper.InducedCover
