import Paper.Endpoints.Girth.HighGirthCountEnvelope
import Paper.Endpoints.Girth.HighGirthSaving
set_option maxHeartbeats 200000
namespace Paper.HighGirthRoundingSlack

theorem actual_rounding_slack
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x)
    (hcap : ∀ v ∈ Paper.HighGirthTransformation.zone G, x v ≤ 1)
    (a : Real) (ha : 1 ≤ a) (ha_upper : a < (8 : Real) / 7)
    (hden : Paper.Incidence.InducedDensityBound G a) :
    let beta := (6-5*a)/(2*(3-2*a))
    let bw := 1 + 10*a/(8-7*a)
    let bl := 4 + a/(3-2*a) + 10*(4*a-2)/(8-7*a)
    let bP := 20*(4-3*a)/(8-7*a)
    let bO := 10*(4-3*a)/(8-7*a)
    let delta := min (min (1/(2*bw)) (beta/bl)) (min (1/bP) (1/bO))
    (∀ r ∈ Paper.HighGirthTransformation.demands G,
      r ∈ Paper.SevenFoundation.covered G (Paper.HighGirthRounding.output G x)) ∧
      0 < delta ∧ (1+delta) * ((Paper.HighGirthRounding.output G x).card : Real) ≤
        Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x := by
  classical
    dsimp only
    let beta := (6-5*a)/(2*(3-2*a))
    let bw := 1 + 10*a/(8-7*a)
    let bl := 4 + a/(3-2*a) + 10*(4*a-2)/(8-7*a)
    let bP := 20*(4-3*a)/(8-7*a)
    let bO := 10*(4-3*a)/(8-7*a)
    let delta := min (min (1/(2*bw)) (beta/bl)) (min (1/bP) (1/bO))
    let w : Real := (Paper.HighGirthRounding.first G x).card
    let l : Real := (Paper.HighGirthRounding.middle G x).card
    let P := Paper.HighGirthRounding.penalty G x
    let O := Paper.HighGirthRounding.oversupply G x
    let k : Real := (Paper.HighGirthRounding.output G x).card
    let C := Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x
    have henv := Paper.HighGirthCountEnvelope.actual_count_envelope G x hx a ha ha_upper hden
    change 0 < bw ∧ 0 < bl ∧ 0 < bP ∧ 0 < bO ∧ k ≤ bw*w+bl*l+bP*P+bO*O at henv
    obtain ⟨hbw,hbl,hbP,hbO,hcount⟩ := henv
    have hs := Paper.HighGirthSaving.saving_endpoint G x hx hcap a ha (by linarith) hden
    have hbeta : 0 < beta := hs.2.2.1
    have hsave : w/2+beta*l+P+O ≤ C-k := hs.2.2.2
    have hd : 0 < delta := by
      apply lt_min
      · exact lt_min (div_pos (by norm_num) (mul_pos (by norm_num) hbw)) (div_pos hbeta hbl)
      · exact lt_min (div_pos (by norm_num) hbP) (div_pos (by norm_num) hbO)
    have hdw : delta ≤ 1/(2*bw) :=
      (min_le_left (min (1/(2*bw)) (beta/bl)) (min (1/bP) (1/bO))).trans (min_le_left _ _)
    have hdl : delta ≤ beta/bl :=
      (min_le_left (min (1/(2*bw)) (beta/bl)) (min (1/bP) (1/bO))).trans (min_le_right _ _)
    have hdP : delta ≤ 1/bP :=
      (min_le_right (min (1/(2*bw)) (beta/bl)) (min (1/bP) (1/bO))).trans (min_le_left _ _)
    have hdO : delta ≤ 1/bO :=
      (min_le_right (min (1/(2*bw)) (beta/bl)) (min (1/bP) (1/bO))).trans (min_le_right _ _)
    have hcw : delta*bw ≤ 1/2 := by
      have hh := (le_div_iff₀ (mul_pos (by norm_num) hbw)).mp hdw
      nlinarith only [hh]
    have hcl : delta*bl ≤ beta := (le_div_iff₀ hbl).mp hdl
    have hcP : delta*bP ≤ 1 := (le_div_iff₀ hbP).mp hdP
    have hcO : delta*bO ≤ 1 := (le_div_iff₀ hbO).mp hdO
    have hn := Paper.HighGirthSlack.slack_nonnegative G x hx
    have hw0 : 0 ≤ w := Nat.cast_nonneg _
    have hl0 : 0 ≤ l := Nat.cast_nonneg _
    have hw := mul_le_mul_of_nonneg_right hcw hw0
    have hl := mul_le_mul_of_nonneg_right hcl hl0
    have hP := mul_le_mul_of_nonneg_right hcP hn.1
    have hO := mul_le_mul_of_nonneg_right hcO hn.2.1
    have hscaled := mul_le_mul_of_nonneg_left hcount hd.le
    refine ⟨hs.1,hd,?_⟩
    change (1+delta)*k ≤ C
    nlinarith only [hscaled,hw,hl,hP,hO,hsave]

end Paper.HighGirthRoundingSlack

#print axioms Paper.HighGirthRoundingSlack.actual_rounding_slack
