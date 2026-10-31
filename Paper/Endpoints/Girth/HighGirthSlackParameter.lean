import Paper.Endpoints.Girth.HighGirthRoundingSlack
import Mathlib.Data.Rat.Cast.Order

/-! Exact rational coefficients and the rational minimum from fv:hg:three. -/
namespace Paper.HighGirthSlackParameter

def beta (a : Rat) : Rat := (6-5*a)/(2*(3-2*a))
def bw (a : Rat) : Rat := 1+10*a/(8-7*a)
def bl (a : Rat) : Rat := 4+a/(3-2*a)+10*(4*a-2)/(8-7*a)
def bP (a : Rat) : Rat := 20*(4-3*a)/(8-7*a)
def bO (a : Rat) : Rat := 10*(4-3*a)/(8-7*a)
def delta (a : Rat) : Rat := min (min (1/(2*bw a)) (beta a/bl a)) (min (1/bP a) (1/bO a))

theorem delta_cast (a : Rat) :
    (delta a : Real) =
      let beta := (6-5*(a : Real))/(2*(3-2*(a : Real)))
      let bw := 1+10*(a : Real)/(8-7*(a : Real))
      let bl := 4+(a : Real)/(3-2*(a : Real))+10*(4*(a : Real)-2)/(8-7*(a : Real))
      let bP := 20*(4-3*(a : Real))/(8-7*(a : Real))
      let bO := 10*(4-3*(a : Real))/(8-7*(a : Real))
      min (min (1/(2*bw)) (beta/bl)) (min (1/bP) (1/bO)) := by
  norm_num [delta,beta,bw,bl,bP,bO,Rat.cast_min]

theorem at_seventeen_fifteenths : delta (17/15) = 5/8482 := by
  norm_num [delta,beta,bw,bl,bP,bO]

end Paper.HighGirthSlackParameter
#print axioms Paper.HighGirthSlackParameter.beta
#print axioms Paper.HighGirthSlackParameter.bw
#print axioms Paper.HighGirthSlackParameter.bl
#print axioms Paper.HighGirthSlackParameter.bP
#print axioms Paper.HighGirthSlackParameter.bO
#print axioms Paper.HighGirthSlackParameter.delta
#print axioms Paper.HighGirthSlackParameter.delta_cast
#print axioms Paper.HighGirthSlackParameter.at_seventeen_fifteenths
