import Paper.Endpoints.Girth.HighGirthCountEndpoint
set_option maxHeartbeats 200000
namespace Paper.HighGirthCountEnvelope

theorem actual_count_envelope
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (a : Real) (ha : 1 ≤ a) (ha_upper : a < (8 : Real) / 7)
    (hden : Paper.Incidence.InducedDensityBound G a) :
    let bw := 1 + 10*a/(8-7*a)
    let bl := 4 + a/(3-2*a) + 10*(4*a-2)/(8-7*a)
    let bP := 20*(4-3*a)/(8-7*a)
    let bO := 10*(4-3*a)/(8-7*a)
    0 < bw ∧ 0 < bl ∧ 0 < bP ∧ 0 < bO ∧
      ((Paper.HighGirthRounding.output G x).card : Real) ≤
        bw * (Paper.HighGirthRounding.first G x).card +
        bl * (Paper.HighGirthRounding.middle G x).card +
        bP * Paper.HighGirthRounding.penalty G x + bO * Paper.HighGirthRounding.oversupply G x := by
  classical
    dsimp only
    let bw := 1 + 10*a/(8-7*a)
    let bl := 4 + a/(3-2*a) + 10*(4*a-2)/(8-7*a)
    let bP := 20*(4-3*a)/(8-7*a)
    let bO := 10*(4-3*a)/(8-7*a)
    have hd : 0 < 8-7*a := by linarith
    have hd3 : 0 < 3-2*a := by linarith
    have ha0 : 0 < a := by linarith
    have hc4 : 0 < 4*a-2 := by linarith
    have hc3 : 0 < 4-3*a := by linarith
    have hbw : 0 < bw := by dsimp only [bw]; positivity
    have hbl : 0 < bl := by dsimp only [bl]; positivity
    have hbP : 0 < bP := by dsimp only [bP]; positivity
    have hbO : 0 < bO := by dsimp only [bO]; positivity
    refine ⟨hbw,hbl,hbP,hbO,?_⟩
    have hc := Paper.HighGirthCountEndpoint.selected_vertex_count_bounds G x hx a ha ha_upper hden
    let w : Real := (Paper.HighGirthRounding.first G x).card
    let l : Real := (Paper.HighGirthRounding.middle G x).card
    let q : Real := Paper.HighGirthAttachments.count G x
    let P := Paper.HighGirthRounding.penalty G x
    let O := Paper.HighGirthRounding.oversupply G x
    have hfirst : (8-7*a)/2*q ≤ a*w+(4*a-2)*l+(4-3*a)*(2*P+O) := hc.1
    have hscale := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 10/(8-7*a) by positivity)
    have he : (10/(8-7*a))*((8-7*a)/2*q) = 5*q := by
      field_simp [ne_of_gt hd]
      <;> ring
    rw [he] at hscale
    change ((Paper.HighGirthRounding.output G x).card : Real) ≤ bw*w+bl*l+bP*P+bO*O
    calc
      _ ≤ w+a*l/(3-2*a)+5*q+4*l := hc.2
      _ ≤ w+a*l/(3-2*a)+(10/(8-7*a))*(a*w+(4*a-2)*l+(4-3*a)*(2*P+O))+4*l := by linarith [hscale]
      _ = bw*w+bl*l+bP*P+bO*O := by
        dsimp only [bw,bl,bP,bO]
        ring

end Paper.HighGirthCountEnvelope

#print axioms Paper.HighGirthCountEnvelope.actual_count_envelope
