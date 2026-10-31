import GraphTheory.SimpleGraph.Minor.Defs
/-! External weak density bounds from Jørgensen, Contractions to K8,
J. Graph Theory 18 (1994), 431–448, DOI 10.1002/jgt.3190180502,
and Song–Thomas, The extremal function for K9 minors,
JCTB 96 (2006), 240–252, DOI 10.1016/j.jctb.2005.07.008.
Only the weak all-order corollaries are assumed, including all exceptions.
These declarations are axioms, not Lean proofs of the literature results. -/
namespace Paper.External.CliqueDensity
axiom k8_edge_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsKMinorFree 8) :
    G.edgeFinset.card ≤ 6 * Fintype.card V
axiom k9_edge_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsKMinorFree 9) :
    G.edgeFinset.card ≤ 7 * Fintype.card V
end Paper.External.CliqueDensity
