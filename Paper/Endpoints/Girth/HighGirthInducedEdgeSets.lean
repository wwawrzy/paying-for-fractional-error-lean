import Paper.Endpoints.Girth.HighGirthRetainedCycleEdges

/-! Induced edges represented in the original vertex type. Their cardinality
is proved equal to the actual induced graph edgeSet cardinality. -/
namespace Paper.HighGirthInducedEdgeSets
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def edges (S : Finset V) : Finset (Sym2 V) := G.edgeFinset ∩ S.sym2

theorem edges_card (S : Finset V) :
    (edges G S).card = Nat.card (G.induce (↑S : Set V)).edgeSet := by
  classical
  have hm := G.map_edgeFinset_induce (s := (↑S : Set V))
  have hh := congrArg Finset.card hm
  simp only [Finset.card_map, ←SimpleGraph.card_edgeSet, ←Nat.card_eq_fintype_card] at hh
  simpa [edges] using hh.symm

end Paper.HighGirthInducedEdgeSets
#print axioms Paper.HighGirthInducedEdgeSets.edges
#print axioms Paper.HighGirthInducedEdgeSets.edges_card
