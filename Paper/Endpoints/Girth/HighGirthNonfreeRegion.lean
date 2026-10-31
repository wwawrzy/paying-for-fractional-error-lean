import Paper.Endpoints.Girth.HighGirthComponentBalls

/-! The actual vertices outside free path components and their attachment
vertices. These definitions contain no size bound. -/
namespace Paper.HighGirthNonfreeRegion
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

noncomputable def freeVertices : Finset V := by
  classical
  exact (HighGirthComponentCounting.freeComponents G x).biUnion (HighGirthFreePaths.members G x)

noncomputable def vertices : Finset V := HighGirthRounding.last G x \ freeVertices G x

noncomputable def attachments : Finset V := HighGirthAttachments.vertices G x ∩ vertices G x

end Paper.HighGirthNonfreeRegion
#print axioms Paper.HighGirthNonfreeRegion.freeVertices
#print axioms Paper.HighGirthNonfreeRegion.vertices
#print axioms Paper.HighGirthNonfreeRegion.attachments
