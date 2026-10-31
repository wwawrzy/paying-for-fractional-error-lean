import Paper.TotalDomination.HighGirthFreePathEnds

/-! Arithmetic consequences of the actual open-neighborhood path constraints.
These lemmas do not assert the graph-to-coordinate classification of bad paths. -/
namespace Paper.TotalDomination.HighGirthBadArithmetic

theorem terminal_payment (Q Ω z loss : ℝ) (hQ : 0 ≤ Q) (hΩ : 0 ≤ Ω)
    (hchain : 1-loss ≤ z) (hloss : loss ≤ Q+Ω) (hz : z ≤ 2/3 ∨ z ≤ Q) :
    (1:ℝ)/3 ≤ Q+Ω := by
  rcases hz with hz | hz <;> linarith

theorem gap_six (x0 x2 x4 x6 ω3 : ℝ)
    (h1 : 1 ≤ x0+x2) (h3 : x2+x4 ≤ 1+ω3) (h5 : 1 ≤ x4+x6) :
    1-x0-ω3 ≤ x6 := by linarith

theorem prefix_three_gap_six (xm2 x0 x2 x4 x6 ωm1 ω3 : ℝ)
    (hcap : xm2 ≤ 1) (hm3 : 1 ≤ xm2) (hm1 : xm2+x0 ≤ 1+ωm1)
    (h1 : 1 ≤ x0+x2) (h3 : x2+x4 ≤ 1+ω3) (h5 : 1 ≤ x4+x6) :
    1-ωm1-ω3 ≤ x6 := by linarith

theorem prefix_three_gap_seven (e xm1 x1 x3 x5 x7 ω0 ω4 : ℝ)
    (hm2 : 1 ≤ e+xm1) (h0 : xm1+x1 ≤ 1+ω0)
    (h2 : 1 ≤ x1+x3) (h4 : x3+x5 ≤ 1+ω4) (h6 : 1 ≤ x5+x7) :
    1-e-ω0-ω4 ≤ x7 := by linarith

theorem one_inner_seven (x1 x3 x5 x7 ω4 Q Ω : ℝ)
    (h2 : 1 ≤ x1+x3) (h6 : 1 ≤ x5+x7) (h4 : x3+x5 ≤ 1+ω4)
    (hQ : x1+x7 ≤ Q) (hΩ : ω4 ≤ Ω) : 1 ≤ Q+Ω := by linarith

theorem inner_distance_two (endWeight branchWeight Q Ω : ℝ)
    (hrow : 1 ≤ endWeight+branchWeight) (hcap : branchWeight ≤ 2/3)
    (hQ : endWeight ≤ Q) (hΩ : 0 ≤ Ω) : (1:ℝ)/3 ≤ Q+Ω := by linarith

theorem one_end_three (left right Q Ω : ℝ)
    (hrow : 1 ≤ left+right) (hQ : left+right ≤ Q) (hΩ : 0 ≤ Ω) :
    1 ≤ Q+Ω := by linarith

end Paper.TotalDomination.HighGirthBadArithmetic
