import Paper.TotalDomination.HighGirthSavingArithmetic
namespace Paper.TotalDomination.HighGirthCountArithmetic
/-- Elimination of the actual retained graph and component counts. -/
theorem eliminate (a q w y f p o u s cp c b : ℝ)
    (ha : 1 ≤ a) (ha' : a < 9/8)
    (hd : u-cp+q+s ≤ a*(u+s+w)) (hs : s ≤ q)
    (hu : u+8*c ≤ 7*q+6*y+2*b)
    (hcp : cp ≤ c+2*y+f) (hc : 2*c ≤ q+b)
    (hb : b ≤ w+3*p+3*o) :
    (9-8*a)/2*q ≤ (5-2*a)/2*w+(6*a-4)*y+f+(15-12*a)/2*(p+o) := by
  have hA : 0 ≤ a-1 := by linarith
  have hB : 0 ≤ 9-8*a := by linarith
  have hC : 0 ≤ 5-4*a := by linarith
  have h1 := mul_le_mul_of_nonneg_left hs hA
  have h2 := mul_le_mul_of_nonneg_left hu hA
  have h3 := mul_le_mul_of_nonneg_left hc hB
  have h4 := mul_le_mul_of_nonneg_left hb hC
  nlinarith
end Paper.TotalDomination.HighGirthCountArithmetic
#print axioms Paper.TotalDomination.HighGirthCountArithmetic.eliminate
