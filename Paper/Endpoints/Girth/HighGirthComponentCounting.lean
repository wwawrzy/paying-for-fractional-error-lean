import Paper.Endpoints.Girth.HighGirthSelectedCount

/-! Actual component families and incidence used by fv:hg:count. -/
namespace Paper.HighGirthComponentCounting
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def pathComponents : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact Finset.univ.filter (HighGirthFreePaths.isPathComponent G x)

noncomputable def freeComponents : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact (pathComponents G x).filter (HighGirthFreePaths.free G x)

noncomputable def nonfreeComponents : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact pathComponents G x \ freeComponents G x

noncomputable def touching
    (family : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (v : V) : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent := by
  classical
  exact family.filter (fun K => ∃ u ∈ HighGirthFreePaths.members G x K, G.Adj v u)

end Paper.HighGirthComponentCounting

#print axioms Paper.HighGirthComponentCounting.pathComponents
#print axioms Paper.HighGirthComponentCounting.freeComponents
#print axioms Paper.HighGirthComponentCounting.nonfreeComponents
#print axioms Paper.HighGirthComponentCounting.touching
