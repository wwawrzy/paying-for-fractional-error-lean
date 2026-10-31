import Paper.Endpoints.Rounding.WeightedBudget

/-! The exact branch-based transformation of fv:hg:budget.
Branch means degree at least three: endpoints of degree zero or one are NOT
included, unlike the earlier degree-not-equal-to-two defect construction. -/
namespace Paper.HighGirthTransformation

variable {V : Type} [Fintype V] [DecidableEq V]

def branches (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => 3 ≤ G.degree v)

def zone (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  SevenFoundation.covered G (SevenFoundation.covered G (branches G))

def far (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ \ zone G

def demands (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  zone G \ SevenFoundation.covered G (far G)

/-- Natural-valued original candidate cost; its range1..3 is a proof obligation. -/
def candidateCost (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Nat :=
  3 - (G.neighborFinset v ∩ far G).card

end Paper.HighGirthTransformation

#print axioms Paper.HighGirthTransformation.branches
#print axioms Paper.HighGirthTransformation.zone
#print axioms Paper.HighGirthTransformation.far
#print axioms Paper.HighGirthTransformation.demands
#print axioms Paper.HighGirthTransformation.candidateCost
