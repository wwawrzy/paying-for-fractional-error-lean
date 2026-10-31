import Paper.RedBlue.SurfaceCost
import Paper.RedBlue.Feasibility
namespace Paper.RedBlue
open BroadcastModel SevenFoundation CoveringThresholdInput
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]
set_option maxHeartbeats 400000 in
theorem surface_rounding_cost (G : SimpleGraph V) [DecidableRel G.Adj] {bits M : ℕ}
    (ids : BitCode V bits) (rot : SimpleGraph.SignedRotation G) (g : ℕ)
    (hgen : (rot.eulerGenus : ℝ) ≤ g) (R B : Finset V) (hRB : Disjoint R B)
    (c : V → Fin (M+1)) (n : V → ℕ) (q : ℕ) (hq : 0 < q)
    (hne : ∀ r ∈ R, (rows G R B r).Nonempty)
    (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ rows G R B r, (n v : ℝ)/q) :
    (∑ v ∈ CoveringThresholdCost.output G ids 4 q (roundingInput G R B c n), ((c v).val : ℝ)) ≤
      4*(∑ v, ((c v).val : ℝ)*((n v : ℝ)/q))+(M : ℝ)*g := by
  classical
  let s := roundingInput G R B c n
  let f := CoveringRoundingCost.chosen (fun v => prepare 4 q (s v))
  have hrows : ∀ r, (s r).demand = true → (s r).candidates.Nonempty := by
    intro r hr
    exact hne r (by simpa [s,roundingInput] using hr)
  have hfmem : ∀ r ∈ R, f r ∈ rows G R B r := by
    intro r hr
    exact (CoveringRoundingCost.chosen_spec (fun v => prepare 4 q (s v)) r (hne r hr)).2.1
  have hfmin : ∀ r ∈ R, ∀ v ∈ rows G R B r, ((c (f r)).val : ℝ) ≤ (c v).val := by
    intro r hr v hv
    exact (CoveringRoundingCost.chosen_spec (fun v => prepare 4 q (s v)) r (hne r hr)).2.2 v hv
  have h := RedBlueSurfaceCharging.selected_cost G rot g hgen R B hRB (M : ℝ)
    (Nat.cast_nonneg _) (fun v => (n v : ℝ)/q) (fun v => ((c v).val : ℝ))
    (fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (fun v => Nat.cast_nonneg _)
    (fun v _ => by
      change ((c v).val : ℝ) ≤ (M : ℝ)
      exact_mod_cast (show (c v).val ≤ M by omega)) hcover f hfmem hfmin
  have hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r :=
    fun r _ => rows_local G R B r
  have he := CoveringThresholdCost.output_eq G ids 4 q (by omega) hq s hlocal hrows
  have hd : CoveringThresholdCost.demands s = R := by
    ext v
    simp [CoveringThresholdCost.demands,s,roundingInput]
  rw [rounding_rows G R B c n,hd] at he
  rw [he]
  exact h
end Paper.RedBlue
#print axioms Paper.RedBlue.surface_rounding_cost
