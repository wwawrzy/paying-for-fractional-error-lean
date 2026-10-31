import Paper.Solver.Density.NeighborhoodSlack
import Paper.Solver.Density.UnitDomination

/-! Terminal selection for capped dual growth. Selected tight rows are paid
from their actual closed neighborhood by noninteger density slack. Vertices
outside that neighborhood select themselves and are paid by their own cap.
The growth process and its termination are separate obligations. -/

namespace Paper.Density.CappedSelection

open SevenFoundation
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def residual (S : Finset V) : Finset V := Finset.univ \ covered G S

def output (S : Finset V) : Finset V := S ∪ residual G S

theorem output_dominates (S : Finset V) : dominates G (output G S) := by
  intro v
  by_cases hv : v ∈ covered G S
  · exact covered_mono G Finset.subset_union_left hv
  · exact subset_covered G _ (Finset.mem_union_right _
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩))

/-- The selected and residual vertices use disjoint dual budgets. -/
theorem terminal_bound (p : NeighborhoodSlack.Parameters)
    (hden : Incidence.InducedDensityBound G p.a) (S : Finset V)
    (y : V → ℝ) (rho : ℝ) (hy : ∀ v, 0 ≤ y v)
    (hcap : ∀ v, y v ≤ 1 / (2 * p.a + 1))
    (hrho : 2 * p.a + 1 - NeighborhoodSlack.eta p ≤ (2 * p.a + 1) * rho)
    (hselected : ∀ s ∈ S, rho ≤ UnitDomination.mass G y s)
    (hresidual : ∀ v ∈ residual G S, y v = 1 / (2 * p.a + 1)) :
    dominates G (output G S) ∧
      ((output G S).card : ℝ) ≤ (2 * p.a + 1) * ∑ v, y v := by
  have hb : 0 < 2 * p.a + 1 := by linarith [p.a_ge_one]
  have hcapscale : ∀ v, (2 * p.a + 1) * y v ≤ 1 := by
    intro v
    have hh := mul_le_mul_of_nonneg_left (hcap v) hb.le
    simpa only [one_div, mul_inv_cancel₀ hb.ne'] using hh
  have hrows : ∀ s ∈ S, 2 * p.a + 1 - NeighborhoodSlack.eta p ≤
      ∑ v ∈ closed G s, (2 * p.a + 1) * y v := by
    intro s hs
    rw [← Finset.mul_sum]
    exact hrho.trans (mul_le_mul_of_nonneg_left (hselected s hs) hb.le)
  have hs := NeighborhoodSlack.neighborhood_mass_ge G p hden S
    (fun v => (2 * p.a + 1) * y v)
    (fun v => mul_nonneg hb.le (hy v)) hcapscale hrows
  rw [← Finset.mul_sum] at hs
  have hr : ((residual G S).card : ℝ) =
      (2 * p.a + 1) * ∑ v ∈ residual G S, y v := by
    rw [Finset.mul_sum]
    have he : (∑ v ∈ residual G S, (2 * p.a + 1) * y v) =
        ∑ _v ∈ residual G S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hresidual v hv, one_div, mul_inv_cancel₀ hb.ne']
    rw [he]
    simp
  have hdis : Disjoint S (residual G S) := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvr
    exact (Finset.mem_sdiff.mp hvr).2 (subset_covered G S hvS)
  have hc : ((output G S).card : ℝ) = (S.card : ℝ) + (residual G S).card := by
    exact_mod_cast Finset.card_union_of_disjoint hdis
  have hsplit : (∑ v ∈ residual G S, y v) + (∑ v ∈ covered G S, y v) =
      ∑ v, y v := Finset.sum_sdiff (Finset.subset_univ (covered G S))
  refine ⟨output_dominates G S, ?_⟩
  rw [hc, hr, ← hsplit]
  nlinarith only [hs]

/-- Weak duality compares the actual terminal set with every fractional
cover; the neighborhood charging inequality is derived in terminal_bound. -/
theorem cost_le_cover (p : NeighborhoodSlack.Parameters)
    (hden : Incidence.InducedDensityBound G p.a) (S : Finset V)
    (y : V → ℝ) (rho : ℝ) (hy : ∀ v, 0 ≤ y v)
    (hcap : ∀ v, y v ≤ 1 / (2 * p.a + 1))
    (hpack : ∀ v, UnitDomination.mass G y v ≤ 1)
    (hrho : 2 * p.a + 1 - NeighborhoodSlack.eta p ≤ (2 * p.a + 1) * rho)
    (hselected : ∀ s ∈ S, rho ≤ UnitDomination.mass G y s)
    (hresidual : ∀ v ∈ residual G S, y v = 1 / (2 * p.a + 1))
    (x : V → ℝ) (hx : feasible (ordinary G) x) :
    ((output G S).card : ℝ) ≤ (2 * p.a + 1) * cost (ordinary G) x := by
  have ht := (terminal_bound G p hden S y rho hy hcap hrho hselected hresidual).2
  have hx' := (UnitDomination.ordinary_feasible G x).mp hx
  have hd := UnitDomination.weak_duality G x y hx'.1 hy hx'.2 hpack
  rw [ordinary_cost]
  exact ht.trans (mul_le_mul_of_nonneg_left hd (by linarith [p.a_ge_one]))

/-- The infimum endpoint does not assume that an optimum is attained. -/
theorem terminal_fractionalNumber (p : NeighborhoodSlack.Parameters)
    (hden : Incidence.InducedDensityBound G p.a) (S : Finset V)
    (y : V → ℝ) (rho : ℝ) (hy : ∀ v, 0 ≤ y v)
    (hcap : ∀ v, y v ≤ 1 / (2 * p.a + 1))
    (hpack : ∀ v, UnitDomination.mass G y v ≤ 1)
    (hrho : 2 * p.a + 1 - NeighborhoodSlack.eta p ≤ (2 * p.a + 1) * rho)
    (hselected : ∀ s ∈ S, rho ≤ UnitDomination.mass G y s)
    (hresidual : ∀ v ∈ residual G S, y v = 1 / (2 * p.a + 1)) :
    dominates G (output G S) ∧
      ((output G S).card : ℝ) ≤ (2 * p.a + 1) * fractionalNumber G := by
  have ht := terminal_bound G p hden S y rho hy hcap hrho hselected hresidual
  have hd : (∑ v, y v) ≤ fractionalNumber G := by
    apply le_csInf (feasibleCosts_nonempty G)
    rintro t ⟨x, hx, rfl⟩
    rw [ordinary_cost]
    have hx' := (UnitDomination.ordinary_feasible G x).mp hx
    exact UnitDomination.weak_duality G x y hx'.1 hy hx'.2 hpack
  exact ⟨ht.1, ht.2.trans (mul_le_mul_of_nonneg_left hd (by linarith [p.a_ge_one]))⟩

end Paper.Density.CappedSelection

#print axioms Paper.Density.CappedSelection.output_dominates
#print axioms Paper.Density.CappedSelection.terminal_bound
#print axioms Paper.Density.CappedSelection.cost_le_cover
#print axioms Paper.Density.CappedSelection.terminal_fractionalNumber
