import Paper.Endpoints.Rounding.NoncriticalRounding

namespace Paper.NoncriticalOptimum
open SevenFoundation NoncriticalParameters
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem feasible_iff (x : V → ℝ) :
    PartialOptimum.Feasible G Finset.univ x ↔ feasible (ordinary G) x := by
  constructor
  · intro hx
    exact ⟨hx.1, fun v hv => False.elim (hv (Finset.mem_univ v)), hx.2⟩
  · intro hx
    exact ⟨hx.1, hx.2.2⟩

theorem number_eq : PartialOptimum.number G Finset.univ (fun _ => (1 : ℝ)) = fractionalNumber G := by
  apply congrArg sInf
  ext t
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨x, (feasible_iff G x).mp hx, ?_⟩
    simpa only [ordinary_cost, PartialOptimum.objective, one_mul] using he
  · rintro ⟨x, hx, he⟩
    refine ⟨x, (feasible_iff G x).mpr hx, ?_⟩
    simpa only [ordinary_cost, PartialOptimum.objective, one_mul] using he

theorem output_bound (a θ : ℝ) (ha : 1 ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1)
    (k : ℕ) (heq : 2 * a = k + θ) (hden : Incidence.InducedDensityBound G a)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x) (hcap : ∀ v, x v ≤ 1)
    (hmass : (∑ v, x v) ≤ (1 + gain θ / (2 * a + 1 - gain θ)) * fractionalNumber G) :
    dominates G (NoncriticalGeometry.output G k (threshold a θ) x) ∧
      ((NoncriticalGeometry.output G k (threshold a θ) x).card : ℝ) ≤ (2 * a + 1) * fractionalNumber G := by
  obtain ⟨hμ, hb, _⟩ := coefficients ha hθ hθ1
  obtain ⟨_, he⟩ := NoncriticalRounding.error_cancellation a θ ha hθ hθ1
  refine ⟨NoncriticalGeometry.output_dominates G k (threshold a θ) x, ?_⟩
  calc
    _ ≤ (2 * a + 1 - gain θ) * ∑ v, x v :=
      NoncriticalRounding.strict_bound G a θ ha hθ hθ1 k heq hden x hx hcap
    _ ≤ (2 * a + 1 - gain θ) * ((1 + gain θ / (2 * a + 1 - gain θ)) * fractionalNumber G) :=
      mul_le_mul_of_nonneg_left hmass (by linarith)
    _ = _ := by rw [← mul_assoc, he]

end Paper.NoncriticalOptimum
