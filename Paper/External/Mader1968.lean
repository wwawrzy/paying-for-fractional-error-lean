import GraphTheory.SimpleGraph.Minor.Defs

/-! External density bound from Mader, Homomorphiesätze für Graphen,
Math. Ann. 178 (1968), 154–168, DOI 10.1007/BF01350657:
Part II, assertion (8), p.164, specialized to r = 5.
This declaration is an axiom, not a Lean proof of Mader's theorem. -/
namespace Paper.External.Mader1968

/-- Every finite simple K₇-minor-free graph on at least five vertices has
at most 5n−15 edges. Ordinary branch-set minors; no connectedness assumption. -/
axiom k7_edge_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsKMinorFree 7) (hV : 5 ≤ Fintype.card V) :
    G.edgeFinset.card + 15 ≤ 5 * Fintype.card V

end Paper.External.Mader1968
