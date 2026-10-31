import GraphTheory.Plane.PlaneEdgeGluing
import GraphTheory.Plane.PlaneGeneralTransport

/-! # Actual edge gluing on an arbitrary two-set vertex cover -/

noncomputable section

namespace PlaneTopology.PlaneEdgeGluingTransport

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneEdgeGluingGraph

variable {V : Type*} [DecidableEq V]

/-- Private vertices of one side, excluding the two common endpoints. -/
def Private (S : Set V) (u v : V) := {x : V // x ∈ S ∧ x ≠ u ∧ x ≠ v}

/-- The two distinguished endpoint coordinates. -/
def endpoint (u v : V) (i : Fin 2) : V := if i = 0 then u else v

theorem endpoint_injective {u v : V} (hne : u ≠ v) : Function.Injective (endpoint u v) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [endpoint, eq_comm]

/-- Put the two endpoint coordinates and the private coordinates into one side. -/
def sideVertex (S : Set V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) : Fin 2 ⊕ Private S u v → S
  | Sum.inl i => ⟨endpoint u v i, by fin_cases i <;> simp [endpoint, hu, hv]⟩
  | Sum.inr x => ⟨x.1, x.2.1⟩

theorem sideVertex_injective (S : Set V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) :
    Function.Injective (sideVertex S u v hu hv) := by
  intro x y h
  have heq := congrArg Subtype.val h
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (endpoint_injective hne heq)
    | inr y =>
      fin_cases i
      · exact (y.2.2.1 heq.symm).elim
      · exact (y.2.2.2 heq.symm).elim
  | inr x =>
    cases y with
    | inl j =>
      fin_cases j
      · exact (x.2.2.1 heq).elim
      · exact (x.2.2.2 heq).elim
    | inr y => exact congrArg Sum.inr (Subtype.ext heq)

theorem sideVertex_surjective (S : Set V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) :
    Function.Surjective (sideVertex S u v hu hv) := by
  intro x
  by_cases hx : x.1 = u
  · exact ⟨Sum.inl 0, Subtype.ext hx.symm⟩
  by_cases hy : x.1 = v
  · exact ⟨Sum.inl 1, Subtype.ext hy.symm⟩
  exact ⟨Sum.inr ⟨x.1, x.2, hx, hy⟩, Subtype.ext rfl⟩

/-- Actual coordinate equivalence for one side of a two-vertex separator. -/
def sideEquiv (S : Set V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) :
    Fin 2 ⊕ Private S u v ≃ S :=
  Equiv.ofBijective (sideVertex S u v hu hv)
    ⟨sideVertex_injective S u v hu hv hne, sideVertex_surjective S u v hu hv⟩

/-- Global coordinates put private vertices of both sides into the ambient set. -/
def unionVertex (S T : Set V) (u v : V) : Fin 2 ⊕ (Private S u v ⊕ Private T u v) → V :=
  Sum.elim (endpoint u v) (Sum.elim Subtype.val Subtype.val)

theorem unionVertex_injective (S T : Set V) (u v : V) (hne : u ≠ v)
    (hinter : S ∩ T = {u, v}) : Function.Injective (unionVertex S T u v) := by
  have hcross (x : Private S u v) (y : Private T u v) : x.1 ≠ y.1 := by
    intro h
    have hm : x.1 ∈ S ∩ T := ⟨x.2.1, h.symm ▸ y.2.1⟩
    rw [hinter] at hm
    rcases Set.mem_insert_iff.mp hm with hu | hv
    · exact x.2.2.1 hu
    · exact x.2.2.2 (Set.mem_singleton_iff.mp hv)
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (endpoint_injective hne h)
    | inr y =>
      cases y with
      | inl y =>
        fin_cases i
        · exact (y.2.2.1 h.symm).elim
        · exact (y.2.2.2 h.symm).elim
      | inr y =>
        fin_cases i
        · exact (y.2.2.1 h.symm).elim
        · exact (y.2.2.2 h.symm).elim
  | inr x =>
    cases x with
    | inl x =>
      cases y with
      | inl j =>
        fin_cases j
        · exact (x.2.2.1 h).elim
        · exact (x.2.2.2 h).elim
      | inr y =>
        cases y with
        | inl y => exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h)
        | inr y => exact (hcross x y h).elim
    | inr x =>
      cases y with
      | inl j =>
        fin_cases j
        · exact (x.2.2.1 h).elim
        · exact (x.2.2.2 h).elim
      | inr y =>
        cases y with
        | inl y => exact (hcross y x h.symm).elim
        | inr y => exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext h)

theorem unionVertex_surjective (S T : Set V) (u v : V) (hcover : S ∪ T = Set.univ) :
    Function.Surjective (unionVertex S T u v) := by
  intro x
  by_cases hx : x = u
  · exact ⟨Sum.inl 0, hx.symm⟩
  by_cases hy : x = v
  · exact ⟨Sum.inl 1, hy.symm⟩
  have hm : x ∈ S ∪ T := hcover.symm ▸ Set.mem_univ x
  rcases hm with hS | hT
  · exact ⟨Sum.inr (Sum.inl ⟨x, hS, hx, hy⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨x, hT, hx, hy⟩), rfl⟩

/-- The global edge-sum coordinate map is a genuine equivalence. -/
def unionEquiv (S T : Set V) (u v : V) (hne : u ≠ v)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u, v}) :
    Fin 2 ⊕ (Private S u v ⊕ Private T u v) ≃ V :=
  Equiv.ofBijective (unionVertex S T u v)
    ⟨unionVertex_injective S T u v hne hinter, unionVertex_surjective S T u v hcover⟩

theorem unionVertex_left (S T : Set V) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (x : Fin 2 ⊕ Private S u v) :
    unionVertex S T u v (leftVertex x) = (sideVertex S u v hu hv x).1 := by cases x <;> rfl

theorem unionVertex_right (S T : Set V) (u v : V) (hu : u ∈ T) (hv : v ∈ T)
    (x : Fin 2 ⊕ Private T u v) :
    unionVertex S T u v (rightVertex x) = (sideVertex T u v hu hv x).1 := by cases x <;> rfl

/-- Pulling a graph back along a vertex equivalence gives an actual graph isomorphism. -/
def comapIso {α β : Type*} (G : SimpleGraph β) (e : α ≃ β) : G.comap e ≃g G where
  toEquiv := e
  map_rel_iff' := Iff.rfl

/-- Map and comap cancel along the chosen coordinate equivalence. -/
theorem map_comap_equiv_comp {α β γ : Type*} (G : SimpleGraph β) (e : α ≃ β)
    (f : β → γ) : (G.comap e).map (f ∘ e) = G.map f := by
  ext x y
  simp only [SimpleGraph.map_adj', SimpleGraph.comap_adj, Function.comp_apply]
  constructor
  · rintro ⟨hne, a, b, hab, ha, hb⟩
    exact ⟨hne, e a, e b, hab, ha, hb⟩
  · rintro ⟨hne, a, b, hab, ha, hb⟩
    exact ⟨hne, e.symm a, e.symm b, by simpa using hab, by simpa using ha, by simpa using hb⟩

/-- Graph image distributes over the exact union. -/
theorem map_sup_graph {α β : Type*} (G H : SimpleGraph α) (f : α → β) :
    (G ⊔ H).map f = G.map f ⊔ H.map f := by
  ext x y
  simp only [SimpleGraph.map_adj', SimpleGraph.sup_adj]
  aesop

/-- The normalized edge sum maps to exactly the union of the original side graphs. -/
theorem image_gluedGraph_eq (S T : Set V) (u v : V)
    (huS : u ∈ S) (hvS : v ∈ S) (huT : u ∈ T) (hvT : v ∈ T)
    (hne : u ≠ v) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u, v})
    (L : SimpleGraph S) (R : SimpleGraph T) :
    (gluedGraph (L.comap (sideEquiv S u v huS hvS hne))
      (R.comap (sideEquiv T u v huT hvT hne))).map (unionEquiv S T u v hne hcover hinter) =
      L.map Subtype.val ⊔ R.map Subtype.val := by
  rw [gluedGraph, map_sup_graph, SimpleGraph.map_map, SimpleGraph.map_map]
  have hl : (unionEquiv S T u v hne hcover hinter) ∘
      (leftEmbedding (A := Private S u v) (B := Private T u v)) =
      Subtype.val ∘ (sideEquiv S u v huS hvS hne) :=
    funext (unionVertex_left S T u v huS hvS)
  have hr : (unionEquiv S T u v hne hcover hinter) ∘
      (rightEmbedding (A := Private S u v) (B := Private T u v)) =
      Subtype.val ∘ (sideEquiv T u v huT hvT hne) :=
    funext (unionVertex_right S T u v huT hvT)
  rw [hl, hr, map_comap_equiv_comp, map_comap_equiv_comp]

/-- Actual graph isomorphism from normalized K₂ gluing to the arbitrary cover union. -/
def unionGraphIso (S T : Set V) (u v : V)
    (huS : u ∈ S) (hvS : v ∈ S) (huT : u ∈ T) (hvT : v ∈ T)
    (hne : u ≠ v) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u, v})
    (L : SimpleGraph S) (R : SimpleGraph T) :
    gluedGraph (L.comap (sideEquiv S u v huS hvS hne))
      (R.comap (sideEquiv T u v huT hvT hne)) ≃g L.map Subtype.val ⊔ R.map Subtype.val := by
  let e := SimpleGraph.Iso.map (unionEquiv S T u v hne hcover hinter)
    (gluedGraph (L.comap (sideEquiv S u v huS hvS hne)) (R.comap (sideEquiv T u v huT hvT hne)))
  change _ ≃g (gluedGraph (L.comap (sideEquiv S u v huS hvS hne))
      (R.comap (sideEquiv T u v huT hvT hne))).map (unionEquiv S T u v hne hcover hinter) at e
  rw [image_gluedGraph_eq S T u v huS hvS huT hvT hne hcover hinter L R] at e
  exact e

variable [Fintype V]

/-- **Actual edge gluing for arbitrary vertex sets.** The two side maps share
exactly `{u,v}`, contain that common edge, and cover the ambient vertex set.
The result embeds their precise image union on the original type `V`. -/
def gluedPlaneMap (S T : Set V) (u v : V)
    (huS : u ∈ S) (hvS : v ∈ S) (huT : u ∈ T) (hvT : v ∈ T)
    (hne : u ≠ v) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u, v})
    (L : SimpleGraph S) (R : SimpleGraph T)
    (l : by classical exact ConnectedPlaneMap L) (r : by classical exact ConnectedPlaneMap R)
    (hL : L.Adj ⟨u, huS⟩ ⟨v, hvS⟩) (hR : R.Adj ⟨u, huT⟩ ⟨v, hvT⟩) :
    (by classical exact ConnectedPlaneMap (L.map Subtype.val ⊔ R.map Subtype.val)) := by
  classical
  letI : Fintype (Private S u v) := by unfold Private; infer_instance
  letI : Fintype (Private T u v) := by unfold Private; infer_instance
  let eL := sideEquiv S u v huS hvS hne
  let eR := sideEquiv T u v huT hvT hne
  let l' := PlaneTopology.PlaneGeneralTransport.planeMap (comapIso L eL).symm l
  let r' := PlaneTopology.PlaneGeneralTransport.planeMap (comapIso R eR).symm r
  have hL' : (L.comap eL).Adj (Sum.inl 0) (Sum.inl 1) := hL
  have hR' : (R.comap eR).Adj (Sum.inl 0) (Sum.inl 1) := hR
  let M := PlaneTopology.PlaneEdgeGluing.gluedPlaneMap (L.comap eL) (R.comap eR) l' r' hL' hR'
  exact PlaneTopology.PlaneGeneralTransport.planeMap
    (unionGraphIso S T u v huS hvS huT hvT hne hcover hinter L R) M

#print axioms unionEquiv
#print axioms map_comap_equiv_comp
#print axioms gluedPlaneMap

end PlaneTopology.PlaneEdgeGluingTransport
