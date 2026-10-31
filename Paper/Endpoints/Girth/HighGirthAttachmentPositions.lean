import Paper.Endpoints.Girth.HighGirthAttachmentGap

/-! Actual attachment positions on a genuine component path. -/
namespace Paper.HighGirthAttachmentPositions

noncomputable def positions
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    {a b : K} (p : K.toSimpleGraph.Walk a b) : Finset Nat := by
  classical
  exact (Finset.range (p.length + 1)).filter
    (fun i => (p.getVert i).val.val ∈ HighGirthAttachments.vertices G x)

end Paper.HighGirthAttachmentPositions

#print axioms Paper.HighGirthAttachmentPositions.positions
