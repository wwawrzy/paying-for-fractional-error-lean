import Paper.RedBlue.RequestCharge
import Paper.RedBlue.IncidenceDensity
import Paper.Certificates.Counting.OrientationShares
namespace Paper.RedBlueSurfaceCharging
open SevenFoundation GeneralCoveringRounding OrientationShares ApproximateOrientation
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 400000 in
theorem oriented_requests_cost (G : SimpleGraph V) [DecidableRel G.Adj]
    (R B T : Finset V) (hRB : Disjoint R B) (hTR : T ⊆ R)
    (O : MultiOrientation (incidenceGraph G (RedBlue.rows G R B)) 1)
    (err : V → ℕ) (hload : ∀ v, load _ O v ≤ 2+err v) (E b : ℝ)
    (hb : 0 ≤ b) (hbudget : (∑ v, (err v : ℝ)) ≤ E)
    (x c : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hc : ∀ v ∈ B, 0 ≤ c v ∧ c v ≤ b)
    (hsmall : ∀ r ∈ T, ∀ v ∈ RedBlue.rows G R B r, x v < 1/4)
    (hcover : ∀ r ∈ T, 1 ≤ ∑ v ∈ RedBlue.rows G R B r, x v)
    (f : V → V) (hfmem : ∀ r ∈ T, f r ∈ RedBlue.rows G R B r)
    (hfmin : ∀ r ∈ T, ∀ v ∈ RedBlue.rows G R B r, c (f r) ≤ c v) :
    (∑ r ∈ T, c (f r)) ≤ 4*(∑ v ∈ B.filter (fun v => x v < 1/4), c v*x v)+b*E/2 := by
  classical
  let I := incidenceGraph G (RedBlue.rows G R B)
  let w := share I O
  let L := B.filter (fun v => x v < 1/4)
  have hw : ∀ u v, 0 ≤ w u v := share_nonneg I O
  have hwl : ∀ v, (∑ u, w u v) ≤ 2+(err v : ℝ) := by
    intro v
    have hh := share_load I O v
    simp only [Nat.cast_one,div_one] at hh
    rw [hh]
    exact_mod_cast hload v
  have hsub (r : V) (hr : r ∈ T) : RedBlue.rows G R B r ⊆ L := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨((RedBlue.mem_rows G R B r v).mp hv).2.2,hsmall r hr v hv⟩
  have hTL : Disjoint T L := by
    apply Finset.disjoint_left.mpr
    intro v ht hl
    exact Finset.disjoint_left.mp hRB (hTR ht) (Finset.mem_filter.mp hl).1
  apply requests_charge T L hTL w c x (fun r => c (f r)) (fun v => (err v : ℝ)) b E hb
    (fun _ => Nat.cast_nonneg _) hbudget
    (fun v hv => hc v (Finset.mem_filter.mp hv).1)
    (fun v hv => ⟨hx v,(Finset.mem_filter.mp hv).2.le⟩)
  · intro v hv
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun u _ _ => hw u v)).trans (hwl v)
  · intro r hr
    have hfrB := ((RedBlue.mem_rows G R B r (f r)).mp (hfmem r hr)).2.2
    have hl : (∑ v ∈ RedBlue.rows G R B r, w v r) ≤ 2+(err r : ℝ) :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hw v r)).trans (hwl r)
    have hp : ∀ v ∈ RedBlue.rows G R B r, w r v+w v r=1 := by
      intro v hv
      have hadj : I.Adj r v := ⟨((RedBlue.mem_rows G R B r v).mp hv).2.1,Or.inl hv⟩
      exact share_pair I O (by omega) r v hadj
    have hh := request_charge (RedBlue.rows G R B r) x c (w r) (fun v => w v r)
      (c (f r)) b (err r) (hc (f r) hfrB).1 (hc (f r) hfrB).2 (Nat.cast_nonneg _)
      (fun v _ => hx v) (fun v hv => (hsmall r hr v hv).le) (hfmin r hr)
      (fun v _ => hw r v) (fun v _ => hw v r) hp hl (hcover r hr)
    have hs : (∑ v ∈ RedBlue.rows G R B r, w r v*c v*x v) ≤ ∑ v ∈ L, w r v*c v*x v :=
      Finset.sum_le_sum_of_subset_of_nonneg (hsub r hr)
        (fun v hv _ => mul_nonneg (mul_nonneg (hw r v) (hc v (Finset.mem_filter.mp hv).1).1) (hx v))
    nlinarith
end Paper.RedBlueSurfaceCharging
#print axioms Paper.RedBlueSurfaceCharging.oriented_requests_cost
