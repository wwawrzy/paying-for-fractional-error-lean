import Paper.RedBlue.OrientedCharge
import Paper.RedBlue.SurfaceDensity
import Paper.Endpoints.Rounding.CoveringRoundingCost
namespace Paper.RedBlueSurfaceCharging
open SevenFoundation GeneralCoveringRounding
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 400000 in
theorem selected_cost (G : SimpleGraph V) [DecidableRel G.Adj]
    (rot : SimpleGraph.SignedRotation G) (g : ℕ) (hgen : (rot.eulerGenus : ℝ) ≤ g)
    (R B : Finset V) (hRB : Disjoint R B) (b : ℝ) (hb : 0 ≤ b)
    (x c : V → ℝ) (hx : ∀ v, 0 ≤ x v) (hc : ∀ v, 0 ≤ c v)
    (hcb : ∀ v ∈ B, c v ≤ b)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ RedBlue.rows G R B r, x v)
    (f : V → V) (hfmem : ∀ r ∈ R, f r ∈ RedBlue.rows G R B r)
    (hfmin : ∀ r ∈ R, ∀ v ∈ RedBlue.rows G R B r, c (f r) ≤ c v) :
    let L := Finset.univ.filter (fun v => 1/4 ≤ x v)
    let T := R.filter (fun r => ∀ v ∈ RedBlue.rows G R B r, x v < 1/4)
    (∑ v ∈ L ∪ T.image f, c v) ≤ 4*(∑ v, c v*x v)+b*g := by
  classical
  let L := Finset.univ.filter (fun v => 1/4 ≤ x v)
  let T := R.filter (fun r => ∀ v ∈ RedBlue.rows G R B r, x v < 1/4)
  let U := B.filter (fun v => x v < 1/4)
  obtain ⟨O,err,hload,hbudget⟩ := RedBlue.surface_incidence_orientation G rot g hgen R B hRB
  have hbudgetR : (∑ v, (err v : ℝ)) ≤ 2*(g : ℝ) := by exact_mod_cast hbudget
  have hreq := oriented_requests_cost G R B T hRB (fun r hr => (Finset.mem_filter.mp hr).1)
    O err hload (2*(g : ℝ)) b hb hbudgetR x c hx (fun v hv => ⟨hc v,hcb v hv⟩)
    (fun r hr => (Finset.mem_filter.mp hr).2)
    (fun r hr => hcover r (Finset.mem_filter.mp hr).1) f
    (fun r hr => hfmem r (Finset.mem_filter.mp hr).1)
    (fun r hr => hfmin r (Finset.mem_filter.mp hr).1)
  have hfirst : (∑ v ∈ L, c v) ≤ 4*(∑ v ∈ L, c v*x v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hh := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hv).2 (hc v)
    nlinarith
  have hd : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro v hl hu
    exact (not_lt_of_ge (Finset.mem_filter.mp hl).2) (Finset.mem_filter.mp hu).2
  have hs : (∑ v ∈ L, c v*x v)+(∑ v ∈ U, c v*x v) ≤ ∑ v, c v*x v := by
    rw [← Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => mul_nonneg (hc v) (hx v))
  have hu := CoveringRoundingCost.union_image_cost_le L T f c hc
  change (∑ v ∈ L ∪ T.image f, c v) ≤ _
  change (∑ r ∈ T, c (f r)) ≤ 4*(∑ v ∈ U, c v*x v)+b*(2*(g : ℝ))/2 at hreq
  nlinarith
end Paper.RedBlueSurfaceCharging
#print axioms Paper.RedBlueSurfaceCharging.selected_cost
