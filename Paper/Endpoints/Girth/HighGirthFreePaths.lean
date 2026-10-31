import Paper.Endpoints.Girth.HighGirthFreeCoordinates

/-! Actual connected components and free paths from fv:hg:free.
Membership uses the true component of G[U]. Freeness is exactly absence of
original-graph edges to L. The path predicate includes all vertices and edges. -/
namespace Paper.HighGirthFreePaths

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def members
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ hv : v ∈ HighGirthRounding.last G x,
    (G.induce (↑(HighGirthRounding.last G x) : Set V)).connectedComponentMk ⟨v, hv⟩ = K)

def isPathComponent
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Prop :=
  ∃ (a b : K) (p : K.toSimpleGraph.Walk a b), p.IsPath ∧
    (∀ z : K, z ∈ p.support) ∧ K.toSimpleGraph = p.toSubgraph.spanningCoe

noncomputable def free
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Prop :=
  ∀ u ∈ members G x K, ∀ l ∈ HighGirthRounding.middle G x, ¬ G.Adj u l

noncomputable def isFreePath
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) : Prop :=
  isPathComponent G x K ∧ free G x K

end Paper.HighGirthFreePaths

#print axioms Paper.HighGirthFreePaths.members
#print axioms Paper.HighGirthFreePaths.isPathComponent
#print axioms Paper.HighGirthFreePaths.free
#print axioms Paper.HighGirthFreePaths.isFreePath
