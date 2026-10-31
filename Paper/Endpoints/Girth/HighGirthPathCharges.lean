import Paper.Endpoints.Girth.HighGirthFree

/-! Exact Q_K, Omega_K and component-incidence sets from fv:hg:half.
No slack inequality, feasibility or multiplicity bound is built into these definitions. -/
namespace Paper.HighGirthPathCharges

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def positiveCharge
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Real :=
  ∑ v ∈ HighGirthRounding.positive G x ∩ SevenFoundation.covered G (HighGirthFreePaths.members G x K), x v

noncomputable def rowExcess
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Real :=
  ∑ r ∈ HighGirthFreePaths.members G x K, ((∑ v ∈ SevenFoundation.closed G r, x v) - 1)

noncomputable def incidentComponents
    (family : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (v : V) : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact family.filter (fun K => v ∈ SevenFoundation.covered G (HighGirthFreePaths.members G x K))

end Paper.HighGirthPathCharges

#print axioms Paper.HighGirthPathCharges.positiveCharge
#print axioms Paper.HighGirthPathCharges.rowExcess
#print axioms Paper.HighGirthPathCharges.incidentComponents
