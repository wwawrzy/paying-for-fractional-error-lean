import Paper.Endpoints.Girth.CurrentFaceBound
import GraphTheory.SimpleGraph.CycleExistence

/-!
# The marked-edge face bound over actual connected components

The marked vertices in a component are precisely the restriction of the
original `A`. Its marked edges are the original incident edges in that
component, so their cardinalities add up exactly to the original `p`.

Acyclic components use the forest edge formula. Every cyclic component
uses a supplied `ConnectedPlaneMap` and the accepted connected face bound.
This is a component assembly theorem, not a constructor of plane maps from
the forbidden-minor definition of `IsPlanar`.
-/

namespace Paper.CurrentFaceComponents

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open scoped BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The same marked set restricted to an actual connected component. -/
noncomputable def componentMarkedVertices
    (C : G.ConnectedComponent) (A : Finset V) : Finset C :=
  Finset.univ.filter fun v => v.val ∈ A

@[simp] theorem mem_componentMarkedVertices
    (C : G.ConnectedComponent) (A : Finset V) (v : C) :
    v ∈ componentMarkedVertices C A ↔ v.val ∈ A := by
  simp [componentMarkedVertices]

/-- Girth outside the original marked set restricts to every component. -/
theorem component_girth
    (A : Finset V) (g : ℕ)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length)
    (C : G.ConnectedComponent)
    (v : {x : C // x ∉ componentMarkedVertices C A})
    (c : (C.toSimpleGraph.induce
      {x : C | x ∉ componentMarkedVertices C A}).Walk v v)
    (hc : c.IsCycle) : g ≤ c.length := by
  let f : (C.toSimpleGraph.induce
      {x : C | x ∉ componentMarkedVertices C A}) →g
      G.induce {x : V | x ∉ A} :=
    { toFun := fun x => ⟨x.val.val, by
        simpa only [mem_componentMarkedVertices] using x.property⟩
      map_rel' := fun h => h }
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {x : V // x ∉ A} => z.val) h
  have hcycle : (c.map f).IsCycle :=
    (Walk.map_isCycle_iff_of_injective (f := f) hinj).mpr hc
  simpa only [Walk.length_map] using hgirth (f v) (c.map f) hcycle

/-- Component marked edges, viewed as the original unordered vertex pairs. -/
noncomputable def componentMarkedEdgeImage
    (C : G.ConnectedComponent) (A : Finset V) : Finset (Sym2 V) :=
  (CurrentFaceBound.incidentMarkedEdges (G := C.toSimpleGraph)
    (componentMarkedVertices C A)).image
      (fun e => Sym2.map Subtype.val e.val)

theorem componentMarkedEdgeImage_card
    (C : G.ConnectedComponent) (A : Finset V) :
    (componentMarkedEdgeImage C A).card =
      (CurrentFaceBound.incidentMarkedEdges (G := C.toSimpleGraph)
        (componentMarkedVertices C A)).card := by
  apply Finset.card_image_of_injective
  exact (Sym2.map.injective Subtype.val_injective).comp Subtype.val_injective

/-- Each component's image consists of actual original marked edges. -/
theorem componentMarkedEdgeImage_subset
    (C : G.ConnectedComponent) (A : Finset V) :
    componentMarkedEdgeImage C A ⊆
      (CurrentFaceBound.incidentMarkedEdges (G := G) A).image Subtype.val := by
  intro e he
  obtain ⟨eC, hmark, rfl⟩ := Finset.mem_image.mp he
  let eG : G.edgeFinset :=
    ⟨Sym2.map Subtype.val eC.val,
      G.mem_edgeFinset.mpr
        (C.toSimpleGraph_hom.map_mem_edgeSet
          (C.toSimpleGraph.mem_edgeFinset.mp eC.property))⟩
  have hm : eG ∈ CurrentFaceBound.incidentMarkedEdges (G := G) A := by
    obtain ⟨x, hx, hxe⟩ :=
      (GirthFaceOccurrenceBudget.mem_markedEdges_iff
        (componentMarkedVertices C A) eC).mp hmark
    apply (GirthFaceOccurrenceBudget.mem_markedEdges_iff A eG).mpr
    exact ⟨x.val, (mem_componentMarkedVertices C A x).mp hx,
      Sym2.mem_map.mpr ⟨x, hxe, rfl⟩⟩
  exact Finset.mem_image.mpr ⟨eG, hm, rfl⟩

/-- The original marked edges are partitioned by their actual component. -/
theorem componentMarkedEdgeImage_cover (A : Finset V) :
    (CurrentFaceBound.incidentMarkedEdges (G := G) A).image Subtype.val =
      Finset.univ.biUnion (fun C : G.ConnectedComponent =>
        componentMarkedEdgeImage C A) := by
  ext e
  constructor
  · intro he
    obtain ⟨eG, hmark, rfl⟩ := Finset.mem_image.mp he
    rcases eG with ⟨e, hedge⟩
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := G.mem_edgeSet.mp (G.mem_edgeFinset.mp hedge)
      let C := G.connectedComponentMk u
      let uC : C := ⟨u, (ConnectedComponent.mem_supp_iff C u).mpr rfl⟩
      let vC : C := ⟨v, (ConnectedComponent.mem_supp_iff C v).mpr
        (ConnectedComponent.sound huv.reachable).symm⟩
      let eC : C.toSimpleGraph.edgeFinset :=
        ⟨s(uC, vC), C.toSimpleGraph.mem_edgeFinset.mpr
          (C.toSimpleGraph.mem_edgeSet.mpr huv)⟩
      have hm : eC ∈ CurrentFaceBound.incidentMarkedEdges
          (G := C.toSimpleGraph) (componentMarkedVertices C A) := by
        obtain ⟨x, hx, hxe⟩ :=
          (GirthFaceOccurrenceBudget.mem_markedEdges_iff
            A (⟨s(u, v), hedge⟩ : G.edgeFinset)).mp hmark
        apply (GirthFaceOccurrenceBudget.mem_markedEdges_iff
          (componentMarkedVertices C A) eC).mpr
        rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · exact ⟨uC, (mem_componentMarkedVertices C A uC).mpr hx,
            Sym2.mem_iff.mpr (Or.inl rfl)⟩
        · exact ⟨vC, (mem_componentMarkedVertices C A vC).mpr hx,
            Sym2.mem_iff.mpr (Or.inr rfl)⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨C, Finset.mem_univ C, ?_⟩
      exact Finset.mem_image.mpr ⟨eC, hm, rfl⟩
  · intro he
    obtain ⟨C, _, hC⟩ := Finset.mem_biUnion.mp he
    exact componentMarkedEdgeImage_subset C A hC

theorem componentMarkedEdgeImage_disjoint (A : Finset V) :
    (↑(Finset.univ : Finset G.ConnectedComponent) :
      Set G.ConnectedComponent).PairwiseDisjoint
        (fun C => componentMarkedEdgeImage C A) := by
  intro C _ C' _ hne
  change Disjoint (componentMarkedEdgeImage C A) (componentMarkedEdgeImage C' A)
  rw [Finset.disjoint_left]
  intro e he he'
  apply hne
  obtain ⟨eC, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨eC', _, heq⟩ := Finset.mem_image.mp he'
  rcases eC with ⟨eC, heC⟩
  rcases eC' with ⟨eC', heC'⟩
  induction eC using Sym2.inductionOn with
  | hf u v =>
    induction eC' using Sym2.inductionOn with
    | hf u' v' =>
      have heq' : s(u.val, v.val) = s(u'.val, v'.val) := heq.symm
      rw [Sym2.eq_iff] at heq'
      have hu := (ConnectedComponent.mem_supp_iff C u.val).mp u.property
      have hu' := (ConnectedComponent.mem_supp_iff C' u'.val).mp u'.property
      have hv' := (ConnectedComponent.mem_supp_iff C' v'.val).mp v'.property
      rcases heq' with ⟨h, _⟩ | ⟨h, _⟩
      · exact hu.symm.trans ((congrArg G.connectedComponentMk h).trans hu')
      · exact hu.symm.trans ((congrArg G.connectedComponentMk h).trans hv')

/-- Exact incident-edge accounting, with no degree-sum or ambient-size loss. -/
theorem sum_incidentMarkedEdges_components (A : Finset V) :
    (∑ C : G.ConnectedComponent,
      (CurrentFaceBound.incidentMarkedEdges (G := C.toSimpleGraph)
        (componentMarkedVertices C A)).card) =
      (CurrentFaceBound.incidentMarkedEdges (G := G) A).card := by
  calc
    (∑ C : G.ConnectedComponent,
      (CurrentFaceBound.incidentMarkedEdges (G := C.toSimpleGraph)
        (componentMarkedVertices C A)).card) =
        ∑ C : G.ConnectedComponent, (componentMarkedEdgeImage C A).card :=
      Finset.sum_congr rfl fun C _ => (componentMarkedEdgeImage_card C A).symm
    _ = (Finset.univ.biUnion
        (fun C : G.ConnectedComponent => componentMarkedEdgeImage C A)).card :=
      (Finset.card_biUnion (componentMarkedEdgeImage_disjoint A)).symm
    _ = ((CurrentFaceBound.incidentMarkedEdges (G := G) A).image
        Subtype.val).card := by rw [← componentMarkedEdgeImage_cover A]
    _ = (CurrentFaceBound.incidentMarkedEdges (G := G) A).card :=
      Finset.card_image_of_injective _ Subtype.val_injective

/-- Forests require no plane-map certificate, including the empty graph. -/
theorem acyclic_edge_bound (hacyclic : G.IsAcyclic) (A : Finset V) (g : ℕ) :
    (g - 2) * G.edgeFinset.card ≤
      g * Fintype.card V +
        (g - 3) * (CurrentFaceBound.incidentMarkedEdges (G := G) A).card := by
  have hforest := hacyclic.edgeFinset_card_add_card_connectedComponent
  have hedge : G.edgeFinset.card ≤ Fintype.card V := by omega
  calc
    (g - 2) * G.edgeFinset.card ≤ g * G.edgeFinset.card :=
      Nat.mul_le_mul_right _ (Nat.sub_le g 2)
    _ ≤ g * Fintype.card V := Nat.mul_le_mul_left g hedge
    _ ≤ g * Fintype.card V +
        (g - 3) * (CurrentFaceBound.incidentMarkedEdges (G := G) A).card :=
      Nat.le_add_right _ _

/-- Componentwise weak estimate, with a real map required only in the cyclic
branch. The stronger `-2` term from the accepted theorem is discarded here. -/
theorem component_edge_bound
    (A : Finset V) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length)
    (C : G.ConnectedComponent)
    (hmap : ¬ C.toSimpleGraph.IsAcyclic →
      Nonempty (ConnectedPlaneMap C.toSimpleGraph)) :
    (g - 2) * C.toSimpleGraph.edgeFinset.card ≤
      g * Fintype.card C + (g - 3) *
        (CurrentFaceBound.incidentMarkedEdges (G := C.toSimpleGraph)
          (componentMarkedVertices C A)).card := by
  by_cases hacyclic : C.toSimpleGraph.IsAcyclic
  · exact acyclic_edge_bound hacyclic (componentMarkedVertices C A) g
  · obtain ⟨M⟩ := hmap hacyclic
    have h := CurrentFaceBound.connectedPlaneMap_edge_bound M hacyclic
      (componentMarkedVertices C A) g hg (component_girth A g hgirth C)
    have hweak : ((g - 2 : ℕ) : ℤ) *
        (C.toSimpleGraph.edgeFinset.card : ℤ) ≤
        (g : ℤ) * (Fintype.card C : ℤ) + ((g - 3 : ℕ) : ℤ) *
          ((CurrentFaceBound.incidentMarkedEdges (G := C.toSimpleGraph)
            (componentMarkedVertices C A)).card : ℤ) := by
      have hg0 : (0 : ℤ) ≤ (g : ℤ) := by positivity
      nlinarith only [h, hg0]
    exact_mod_cast hweak

/-- The weak face bound for an arbitrary finite graph, with precisely the
original marked set and its incident edges. Empty vertex types need no
special map, since the sum over actual components is then empty.

The certificate hypothesis is deliberately explicit. Discharging it from
minor-free `IsPlanar` is a separate bridge, not assumed to have happened. -/
theorem edge_bound_of_component_maps
    (A : Finset V) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length)
    (hmaps : ∀ C : G.ConnectedComponent, ¬ C.toSimpleGraph.IsAcyclic →
      Nonempty (ConnectedPlaneMap C.toSimpleGraph)) :
    (g - 2) * G.edgeFinset.card ≤
      g * Fintype.card V +
        (g - 3) * (CurrentFaceBound.incidentMarkedEdges (G := G) A).card := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun C _ => component_edge_bound A g hg hgirth C (hmaps C))
  have henum : (SetLike.instFintype : Fintype G.ConnectedComponent) =
      (inferInstance : Fintype G.ConnectedComponent) := Subsingleton.elim _ _
  have hE : (∑ C : G.ConnectedComponent, C.toSimpleGraph.edgeFinset.card) =
      G.edgeFinset.card := by
    have h := SimpleGraph.sum_edgeFinset_components_eq (G := G)
    rwa [henum] at h
  have hV : (∑ C : G.ConnectedComponent, Fintype.card C) = Fintype.card V := by
    have h := SimpleGraph.sum_card_components_eq (G := G)
    rwa [henum] at h
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hE, hV,
    sum_incidentMarkedEdges_components] using hsum

end Paper.CurrentFaceComponents

#print axioms Paper.CurrentFaceComponents.component_girth
#print axioms Paper.CurrentFaceComponents.componentMarkedEdgeImage_cover
#print axioms Paper.CurrentFaceComponents.componentMarkedEdgeImage_disjoint
#print axioms Paper.CurrentFaceComponents.sum_incidentMarkedEdges_components
#print axioms Paper.CurrentFaceComponents.acyclic_edge_bound
#print axioms Paper.CurrentFaceComponents.component_edge_bound
#print axioms Paper.CurrentFaceComponents.edge_bound_of_component_maps
