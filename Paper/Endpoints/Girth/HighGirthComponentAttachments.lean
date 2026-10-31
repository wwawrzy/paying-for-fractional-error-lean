import Paper.Endpoints.Girth.HighGirthSingletonCharge

/-! Original U-to-T attachment edges restricted to a genuine component K.
The following definitions contain no cardinality or charge assumptions. -/
namespace Paper.HighGirthComponentAttachments
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def pairs
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Finset (V × V) := by
  classical
  exact (HighGirthAttachments.pairs G x).filter
    (fun p => p.1 ∈ HighGirthFreePaths.members G x K)

noncomputable def edges
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Finset (Sym2 V) := by
  classical
  exact (pairs G x K).image (fun p => s(p.1, p.2))

noncomputable def count
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Nat :=
  (edges G x K).card

end Paper.HighGirthComponentAttachments

#print axioms Paper.HighGirthComponentAttachments.pairs
#print axioms Paper.HighGirthComponentAttachments.edges
#print axioms Paper.HighGirthComponentAttachments.count
