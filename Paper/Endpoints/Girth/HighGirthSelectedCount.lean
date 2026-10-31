import Paper.Endpoints.Girth.HighGirthFewAttachments
set_option maxHeartbeats 200000
namespace Paper.HighGirthSelectedCount

theorem selected_vertex_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (a : Real) (ha : 1 ≤ a) (ha_upper : a < (8 : Real) / 7)
    (hden : Paper.Incidence.InducedDensityBound G a) :
    ((Paper.HighGirthRounding.output G x).card : Real) ≤
      (Paper.HighGirthRounding.first G x).card +
      a * (Paper.HighGirthRounding.middle G x).card / (3 - 2 * a) +
      5 * (Paper.HighGirthAttachments.count G x : Real) +
      4 * (Paper.HighGirthRounding.middle G x).card := by
  classical
  let W := Paper.HighGirthRounding.first G x
  let H := Paper.HighGirthRounding.high G x
  let U := Paper.HighGirthRounding.last G x
  let L := Paper.HighGirthRounding.middle G x
  have hdenpos : 0 < 3 - 2 * a := by linarith
  have hde := Paper.HighGirthDensityExcess.density_excess_bounds G x a hden
  have hz : 0 ≤ (a + 1) * ((Paper.HighGirthRounding.outside G x).card : Real) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hH : (H.card : Real) ≤ a * L.card / (3 - 2 * a) := by
    apply (le_div_iff₀ hdenpos).mpr
    change (H.card : Real) ≤ Paper.HighGirthRounding.excess G x ∧
      Paper.HighGirthRounding.excess G x ≤ (2 * a - 2) * H.card + a * L.card -
        (a + 1) * (Paper.HighGirthRounding.outside G x).card at hde
    nlinarith only [hde.1,hde.2,hz]
  have hU : (U.card : Real) ≤ 5 * (Paper.HighGirthAttachments.count G x : Real) + 4 * L.card := by
    exact_mod_cast Paper.HighGirthResidualSize.residual_size_bound G x
  have hcardN : (Paper.HighGirthRounding.output G x).card ≤ W.card + H.card + U.card := by
    change ((W ∪ H) ∪ U).card ≤ W.card + H.card + U.card
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le W H) U.card)
  have hcard : ((Paper.HighGirthRounding.output G x).card : Real) ≤ W.card + H.card + U.card := by
    exact_mod_cast hcardN
  change ((Paper.HighGirthRounding.output G x).card : Real) ≤ W.card + a * L.card / (3 - 2 * a) +
    5 * (Paper.HighGirthAttachments.count G x : Real) + 4 * L.card
  linarith only [hcard,hH,hU]

end Paper.HighGirthSelectedCount

#print axioms Paper.HighGirthSelectedCount.selected_vertex_bound
