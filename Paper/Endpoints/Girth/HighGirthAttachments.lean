import Paper.Endpoints.Girth.HighGirthResidualDegree

/-! Actual T and attachments from fv:hg:residual and subsequent path lemmas.
Attachments are oriented U-to-T pairs; equality with the source undirected
edge count requires proving U,T disjoint, not assuming it. -/
namespace Paper.HighGirthAttachments

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def connectors : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∉ HighGirthRounding.first G x ∧
    (∃ w ∈ HighGirthRounding.first G x, G.Adj v w) ∧
    (∃ u ∈ HighGirthRounding.last G x, G.Adj v u))

noncomputable def pairs : Finset (V × V) := by
  classical
  exact ((HighGirthRounding.last G x).product (connectors G x)).filter
    (fun p => G.Adj p.1 p.2)

noncomputable def vertices : Finset V := by
  classical
  exact (HighGirthRounding.last G x).filter
    (fun u => ∃ t ∈ connectors G x, G.Adj u t)

noncomputable def count : Nat := (pairs G x).card

end Paper.HighGirthAttachments

#print axioms Paper.HighGirthAttachments.connectors
#print axioms Paper.HighGirthAttachments.pairs
#print axioms Paper.HighGirthAttachments.vertices
#print axioms Paper.HighGirthAttachments.count
