import Paper.Preliminaries.DeletionComponents

/-! A connected set avoiding X and touching an X-component lies wholly in
that component. This supplies monotonicity of heavy components. -/
namespace Paper.ComponentContainment
attribute [local instance] Classical.propDecidable
open DeletionComponents
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem subset (X : Finset V) (C : (deleted G X).ConnectedComponent) (S : Finset V)
    (hconn : (G.induce (S : Set V)).Connected) (hdis : Disjoint S X)
    (hmeet : (S ∩ physical G X C).Nonempty) : S ⊆ physical G X C := by
  obtain ⟨u, hu⟩ := hmeet
  have hu' := Finset.mem_inter.mp hu
  obtain ⟨huX, huC⟩ := (mem_physical G X C u).mp hu'.2
  let f : G.induce (S : Set V) →g deleted G X := {
    toFun := fun v => ⟨v.val, fun hv => Finset.disjoint_left.mp hdis v.property hv⟩
    map_rel' := fun h => h }
  intro v hv
  have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdis hv h
  have hr := (hconn ⟨u, hu'.1⟩ ⟨v, hv⟩).map f
  have he := SimpleGraph.ConnectedComponent.sound hr
  have huEq := (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨u, huX⟩).mp huC
  apply (mem_physical G X C v).mpr
  refine ⟨hvX, ?_⟩
  apply (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨v, hvX⟩).mpr
  exact he.symm.trans huEq
end Paper.ComponentContainment
