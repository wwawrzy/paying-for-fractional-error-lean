import GraphTheory.Surfaces.SignedRotationComponentEdges
import GraphTheory.Surfaces.SignedRotationVertices

/-! Nonisolated vertices, and hence surface vertex classes, split over components. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (r : SignedRotation G)

def closedSupportEquiv (s : Set V)
    (hs : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s) :
    (G.induce s).support ≃ {v : G.support // v.val ∈ s} where
  toFun x := ⟨⟨x.val.val, by
    obtain ⟨w, hw⟩ := x.property
    exact ⟨w.val, hw⟩⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, by
    obtain ⟨w, hw⟩ := x.val.property
    exact ⟨⟨w, hs x.property hw⟩, hw⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

def componentSupportEquiv :
    (Σ c : G.ConnectedComponent, (G.induce c.supp).support) ≃ G.support :=
  (Equiv.sigmaCongrRight (fun c : G.ConnectedComponent => closedSupportEquiv c.supp
    (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu huv))).trans
      (Equiv.sigmaFiberEquiv (fun v : G.support => G.connectedComponentMk v.val))

noncomputable def componentVertexEquiv :
    (Σ c : G.ConnectedComponent, (r.restrictComponent c).Vertex) ≃ r.Vertex := by
  classical
  exact (Equiv.sigmaCongrRight (fun c : G.ConnectedComponent =>
    (r.restrictComponent c).vertexEquiv)).trans
      ((componentSupportEquiv (G := G)).trans r.vertexEquiv.symm)

theorem vertex_card_sum [Fintype G.ConnectedComponent] :
    Nat.card r.Vertex = ∑ c : G.ConnectedComponent, Nat.card (r.restrictComponent c).Vertex := by
  classical
  letI (c : G.ConnectedComponent) : Finite (r.restrictComponent c).Vertex :=
    inferInstanceAs (Finite (Quotient (pairSetoid sideFlip (r.restrictComponent c).cornerFlip)))
  rw [← Nat.card_congr r.componentVertexEquiv, Nat.card_sigma]

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.componentSupportEquiv
#print axioms SimpleGraph.SignedRotation.componentVertexEquiv
#print axioms SimpleGraph.SignedRotation.vertex_card_sum
