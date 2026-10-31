import Paper.Endpoints.Girth.HighGirthBudget

/-! Exact sets of fv:hg:saving and the subsequent residual/path analysis.
The first threshold is strict1/2 on cost3 candidates; the second cutoff is4.
These differ from earlier critical-degree rounding definitions. -/
namespace Paper.HighGirthRounding
open HighGirthTransformation

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def first : Finset V := by
  classical
  exact (zone G).filter (fun v => candidateCost G v = 3 ∧ (1 : Real) / 2 < x v)

noncomputable def residual : Finset V := demands G \ SevenFoundation.covered G (first G x)
noncomputable def hits (v : V) : Nat := (SevenFoundation.closed G v ∩ residual G x).card
noncomputable def high : Finset V := by
  classical
  exact (zone G \ first G x).filter (fun v => 4 ≤ hits G x v)
noncomputable def last : Finset V := residual G x \ SevenFoundation.covered G (high G x)
noncomputable def output : Finset V := first G x ∪ high G x ∪ last G x
noncomputable def other : Finset V := zone G \ (first G x ∪ high G x)
noncomputable def middle : Finset V := residual G x \ (high G x ∪ last G x)
noncomputable def overlap : Finset V := high G x ∩ residual G x
noncomputable def outside : Finset V := high G x \ residual G x
noncomputable def penalty : Real :=
  ∑ v ∈ other G x, ((candidateCost G v : Real) - (hits G x v : Real)) * x v
noncomputable def oversupply : Real :=
  ∑ r ∈ residual G x, ((∑ v ∈ SevenFoundation.closed G r, x v) - 1)
noncomputable def positive : Finset V := by
  classical
  exact (other G x).filter (fun v => hits G x v < candidateCost G v)
noncomputable def excess : Real := ∑ v ∈ high G x, ((hits G x v : Real) - 3)

end Paper.HighGirthRounding
