import Paper.Endpoints.Girth.HighGirthThresholdCost
set_option maxHeartbeats 200000
namespace Paper.HighGirthSaving

theorem saving_endpoint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (hcap : ∀ v ∈ Paper.HighGirthTransformation.zone G, x v ≤ 1)
    (a : Real) (ha : 1 ≤ a) (ha_upper : a < (6 : Real) / 5)
    (hden : Paper.Incidence.InducedDensityBound G a) :
    let beta := (6 - 5 * a) / (2 * (3 - 2 * a))
    (∀ r ∈ Paper.HighGirthTransformation.demands G,
      r ∈ Paper.SevenFoundation.covered G (Paper.HighGirthRounding.output G x)) ∧
      ((Paper.HighGirthRounding.high G x).card : Real) ≤
        a * (Paper.HighGirthRounding.middle G x).card / (3 - 2 * a) ∧
      0 < beta ∧
      (Paper.HighGirthRounding.first G x).card / (2 : Real) +
        beta * (Paper.HighGirthRounding.middle G x).card + Paper.HighGirthRounding.penalty G x +
          Paper.HighGirthRounding.oversupply G x ≤
            Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x -
              (Paper.HighGirthRounding.output G x).card := by
  classical
  let h : Real := (Paper.HighGirthRounding.high G x).card
  let ell : Real := (Paper.HighGirthRounding.middle G x).card
  let z : Real := (Paper.HighGirthRounding.outside G x).card
  let w : Real := (Paper.HighGirthRounding.first G x).card
  let k : Real := (Paper.HighGirthRounding.output G x).card
  let t : Real := (Paper.HighGirthRounding.residual G x).card
  let E := Paper.HighGirthRounding.excess G x
  let C := Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x
  let P := Paper.HighGirthRounding.penalty G x
  let Om := Paper.HighGirthRounding.oversupply G x
  let beta := (6 - 5 * a) / (2 * (3 - 2 * a))
  have hde := Paper.HighGirthDensityExcess.density_excess_bounds G x a hden
  change h ≤ E ∧ E ≤ (2 * a - 2) * h + a * ell - (a + 1) * z at hde
  have hdenpos : 0 < 3 - 2 * a := by linarith
  have htwo : 0 < 2 * (3 - 2 * a) := by positivity
  have hscale : (3 - 2 * a) * E ≤ a * ell - (a + 1) * z := by
    have hm := mul_le_mul_of_nonneg_left hde.1 (show 0 ≤ 2 * a - 2 by linarith)
    nlinarith only [hm, hde.2]
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have hHbound : h ≤ a * ell / (3 - 2 * a) := by
    apply (le_div_iff₀ hdenpos).mpr
    have hm := mul_le_mul_of_nonneg_left hde.1 hdenpos.le
    have hzz := mul_nonneg (show 0 ≤ a + 1 by linarith) hz
    nlinarith only [hm, hscale, hzz]
  have hbeta : 0 < beta := div_pos (by linarith) htwo
  refine ⟨(Paper.HighGirthOutput.output_cover_and_cardinality G x).1, hHbound, hbeta, ?_⟩
  change w / 2 + beta * ell + P + Om ≤ C - k
  have hcost := Paper.HighGirthThresholdCost.threshold_cost_bound G x hx
  change (3 : Real) / 2 * w + t + Om + P - E / 2 ≤ C at hcost
  have hcard : ((Paper.HighGirthRounding.output G x).card : Real) +
      (Paper.HighGirthRounding.middle G x).card = (Paper.HighGirthRounding.first G x).card +
        (Paper.HighGirthRounding.outside G x).card + (Paper.HighGirthRounding.residual G x).card := by
    exact_mod_cast (Paper.HighGirthOutput.output_cover_and_cardinality G x).2
  change k + ell = w + z + t at hcard
  have hpre : w / 2 + ell - z - E / 2 + P + Om ≤ C - k := by
    linarith only [hcost, hcard]
  have hhalf : E / 2 ≤ (a * ell - (a + 1) * z) / (2 * (3 - 2 * a)) := by
    apply (le_div_iff₀ htwo).mpr
    nlinarith only [hscale]
  have heq : ell - z - (a * ell - (a + 1) * z) / (2 * (3 - 2 * a)) =
      beta * ell + ((5 * a - 5) / (2 * (3 - 2 * a))) * z := by
    dsimp only [beta]
    field_simp [show (3 : Real) - a * 2 ≠ 0 by linarith] <;> ring
  have hzcoef : 0 ≤ ((5 * a - 5) / (2 * (3 - 2 * a))) * z :=
    mul_nonneg (div_nonneg (by linarith) htwo.le) hz
  have hgap : beta * ell ≤ ell - z - E / 2 := by
    linarith only [hhalf, heq, hzcoef]
  linarith only [hpre, hgap]

end Paper.HighGirthSaving

#print axioms Paper.HighGirthSaving.saving_endpoint
