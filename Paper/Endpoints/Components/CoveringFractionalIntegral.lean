import Paper.Endpoints.Components.OptimumCertificate
import Paper.Certificates.Counting.CoveringOptimum
set_option maxHeartbeats 200000
namespace Paper.CoveringFractionalIntegral

theorem fractional_nonneg_le_integral
    {V : Type} [Fintype V] [DecidableEq V]
    (cover : V → Finset V) (R : Finset V) (c : V → Nat)
    (hrows : ∀ r ∈ R, (cover r).Nonempty) :
    0 ≤ Paper.CoveringOptimum.number cover R (fun u => (c u : Real)) ∧
    Paper.CoveringOptimum.number cover R (fun u => (c u : Real)) ≤
      (Paper.IntegralCoverOptimum.optimum cover R c : Real) := by
  classical
  obtain ⟨D, hD, hEq⟩ := Paper.IntegralCoverOptimum.exists_optimal cover R c hrows
  let x : V → Real := fun u => if u ∈ D then 1 else 0
  have hxnonneg : ∀ u, 0 ≤ x u := by
    intro u
    simp only [x]
    split_ifs <;> norm_num
  have hx : Paper.CoveringOptimum.Feasible cover R x := by
    refine ⟨hxnonneg, ?_⟩
    intro r hr
    obtain ⟨u, huD, hur⟩ := hD.2 r hr
    have hs := Finset.single_le_sum (fun v (_ : v ∈ cover r) => hxnonneg v) hur
    simpa only [x, if_pos huD] using hs
  have hobj : Paper.CoveringOptimum.objective (fun u => (c u : Real)) x = ((D.sum c : Nat) : Real) := by
    simp [Paper.CoveringOptimum.objective, x, mul_ite, Nat.cast_sum]
  have hbd : BddBelow (Paper.CoveringOptimum.values cover R (fun u => (c u : Real))) := by
    refine ⟨0, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (Nat.cast_nonneg (c u)) (hy.1 u))
  have hne : (Paper.CoveringOptimum.values cover R (fun u => (c u : Real))).Nonempty :=
    ⟨_, x, hx, rfl⟩
  have hzero : ∀ t ∈ Paper.CoveringOptimum.values cover R (fun u => (c u : Real)), 0 ≤ t := by
    rintro t ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (Nat.cast_nonneg (c u)) (hy.1 u))
  refine ⟨le_csInf hne hzero, ?_⟩
  have hle : Paper.CoveringOptimum.number cover R (fun u => (c u : Real)) ≤
      Paper.CoveringOptimum.objective (fun u => (c u : Real)) x :=
    csInf_le hbd ⟨x, hx, rfl⟩
  rw [hobj] at hle
  exact hle.trans (le_of_eq (congrArg (fun n : Nat => (n : Real)) hEq))

end Paper.CoveringFractionalIntegral

#print axioms Paper.CoveringFractionalIntegral.fractional_nonneg_le_integral
