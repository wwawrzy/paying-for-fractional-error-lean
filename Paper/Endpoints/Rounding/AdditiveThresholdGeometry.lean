import Paper.Certificates.Counting.FractionalCharging
import Paper.Certificates.Counting.PartialOptimum
import Paper.Communication.ClosedBitProgram

/-! The exact sets W and U of fv:imp:additive. -/
namespace Paper.AdditiveThreshold
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def first (_G : SimpleGraph V) (t : ℝ) (x : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => t ≤ x v)
noncomputable def low (t : ℝ) (x : V → ℝ) : Finset V := Finset.univ \ first G t x
noncomputable def residual (t : ℝ) (x : V → ℝ) : Finset V := Finset.univ \ covered G (first G t x)
noncomputable def output (t : ℝ) (x : V → ℝ) : Finset V := first G t x ∪ residual G t x

theorem residual_closed_low (t : ℝ) (x : V → ℝ) (u : V)
    (hu : u ∈ residual G t x) : closed G u ⊆ low G t x := by
  classical
  intro v hv
  have hn := (Finset.mem_sdiff.mp hu).2
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro hw
  exact hn (Finset.mem_biUnion.mpr ⟨v,hw,(closed_symm G v u).mp hv⟩)

theorem low_small (t : ℝ) (x : V → ℝ) (v : V) (hv : v ∈ low G t x) : x v ≤ t := by
  classical
  have hn := (Finset.mem_sdiff.mp hv).2
  exact (lt_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))).le

theorem residual_small (t : ℝ) (x : V → ℝ) (v : V) (hv : v ∈ residual G t x) : x v ≤ t :=
  low_small G t x v (residual_closed_low G t x v hv (self_mem_closed G v))

theorem dominates_output (t : ℝ) (x : V → ℝ) : dominates G (output G t x) := by
  classical
  intro v
  by_cases hv : v ∈ covered G (first G t x)
  · exact covered_mono G Finset.subset_union_left hv
  · apply subset_covered G
    exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩)

theorem first_mass (t : ℝ) (x : V → ℝ) :
    t*(first G t x).card ≤ ∑ v ∈ first G t x, x v := by
  classical
  calc
    _ = ∑ _v ∈ first G t x, t := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2

theorem local_feasibility (t : ℝ) (x : V → ℝ) (w : V → V → ℝ)
    (hz : ∀ u v, ¬ G.Adj u v → w u v = 0)
    (hp : ∀ u v, G.Adj u v → w u v + w v u = 1)
    (hx : PartialOptimum.Feasible G Finset.univ x)
    (u : V) (hu : u ∈ residual G t x) :
    1 ≤ x u + ∑ v ∈ low G t x, (w u v + w v u)*x v := by
  classical
  have hsub := residual_closed_low G t x u hu
  have huL := hsub (self_mem_closed G u)
  have hsum : (∑ v ∈ closed G u, x v) =
      ∑ v ∈ low G t x, ((if v = u then x u else 0) + (w u v + w v u)*x v) := by
    calc
      _ = ∑ v ∈ low G t x, if v ∈ closed G u then x v else 0 := by
        rw [← Finset.sum_filter]
        congr 1
        ext v
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨hsub h,h⟩,fun h => h.2⟩
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases heq : v = u
        · subst v
          simp [self_mem_closed,hz u u (G.irrefl)]
        · by_cases hadj : G.Adj u v
          · simp [mem_closed,heq,hadj,hp u v hadj]
          · simp [mem_closed,heq,hadj,hz u v hadj,hz v u (fun h => hadj h.symm)]
  have hf := hx.2 u (Finset.mem_univ _)
  rw [hsum,Finset.sum_add_distrib] at hf
  simpa only [Finset.sum_ite_eq',huL,if_true] using hf

end Paper.AdditiveThreshold
#print axioms Paper.AdditiveThreshold.dominates_output
#print axioms Paper.AdditiveThreshold.residual_closed_low
#print axioms Paper.AdditiveThreshold.first_mass
