import Paper.Endpoints.Girth.HighGirthShortAccess

/-! Finite original U-internal reach sets for fv:hg:residual(iv).
No cardinality bound is assumed. uBallTwo includes the center, its U-neighbors,
and their U-neighbors excluding the center (the immediate return step).
Use its radius-two interpretation only when the center belongs to U.
lAccessTwo lists U vertices reached from an exterior L vertex in one or two
edges, with intermediate vertices in U. -/
namespace Paper.HighGirthAccessSets

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def neighborsU (v : V) : Finset V :=
  G.neighborFinset v ∩ HighGirthRounding.last G x

noncomputable def uBallTwo (v : V) : Finset V :=
  insert v (neighborsU G x v ∪ (neighborsU G x v).biUnion
    (fun p => neighborsU G x p \ {v}))

noncomputable def lAccessTwo (v : V) : Finset V :=
  neighborsU G x v ∪ (neighborsU G x v).biUnion (neighborsU G x)

end Paper.HighGirthAccessSets

#print axioms Paper.HighGirthAccessSets.neighborsU
#print axioms Paper.HighGirthAccessSets.uBallTwo
#print axioms Paper.HighGirthAccessSets.lAccessTwo
