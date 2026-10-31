import Paper.Endpoints.Girth.HighGirthCheapDemands

/-! Actual weighted fractional covering problem on G[Z], with original R0 and
integer candidate costs3-|N(v)interF|, for fv:hg:budget(iii). Its infimum is a
semantic benchmark, never a runtime input or an assumed optimum witness. -/
namespace Paper.HighGirthAuxiliary

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def auxiliary : SevenFoundation.CoverInstance V where
  demands := HighGirthTransformation.demands G
  candidates := HighGirthTransformation.zone G
  eligible := fun r => SevenFoundation.closed G r ∩ HighGirthTransformation.zone G
  eligible_subset := by intros; exact Finset.inter_subset_right
  cost := fun v => if v ∈ HighGirthTransformation.zone G then
    (HighGirthTransformation.candidateCost G v : Real) else 0
  cost_nonneg := by
    intro v
    split_ifs <;> positivity

noncomputable def restrict (y : V → Real) (v : V) : Real :=
  if v ∈ HighGirthTransformation.zone G then y v else 0

def feasibleCosts : Set Real :=
  {a | ∃ x, SevenFoundation.feasible (auxiliary G) x ∧
    SevenFoundation.cost (auxiliary G) x = a}

noncomputable def number : Real := sInf (feasibleCosts G)

end Paper.HighGirthAuxiliary

#print axioms Paper.HighGirthAuxiliary.auxiliary
#print axioms Paper.HighGirthAuxiliary.restrict
#print axioms Paper.HighGirthAuxiliary.feasibleCosts
#print axioms Paper.HighGirthAuxiliary.number
