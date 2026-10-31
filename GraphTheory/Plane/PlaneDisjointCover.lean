import GraphTheory.Plane.PlaneDisjointBridge
import GraphTheory.Plane.PlaneTriangulationMaximal

/-! # Actual plane supergraphs from disjoint vertex-cover sides -/

namespace PlaneTopology.PlaneDisjointCover

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneTriangulationMaximal

variable {V : Type*}

/-- Forget the side label in the disjoint sum of the covering subsets. -/
def unionVertex (S T : Set V) : S ⊕ T → V := Sum.elim Subtype.val Subtype.val

theorem unionVertex_injective (S T : Set V) (hdis : S ∩ T = ∅) :
    Function.Injective (unionVertex S T) := by
  have hcross (x : S) (y : T) : x.1 ≠ y.1 := by
    intro h
    have hm : x.1 ∈ S ∩ T := ⟨x.2, h.symm ▸ y.2⟩
    simp only [hdis, Set.mem_empty_iff_false] at hm
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext h)
    | inr y => exact (hcross x y h).elim
  | inr x =>
    cases y with
    | inl y => exact (hcross y x h.symm).elim
    | inr y => exact congrArg Sum.inr (Subtype.ext h)

/-- Every ambient vertex belongs to at least one of the two covering sides. -/
theorem mem_cover (S T : Set V) (hcover : S ∪ T = Set.univ) (x : V) : x ∈ S ∨ x ∈ T := by
  change x ∈ S ∪ T
  exact hcover.symm ▸ Set.mem_univ x

theorem unionVertex_surjective (S T : Set V) (hcover : S ∪ T = Set.univ) :
    Function.Surjective (unionVertex S T) := by
  intro x
  rcases mem_cover S T hcover x with hx | hx
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

/-- Actual vertex equivalence from the disjoint side sum to the ambient graph. -/
noncomputable def unionEquiv (S T : Set V) (hcover : S ∪ T = Set.univ) (hdis : S ∩ T = ∅) :
    S ⊕ T ≃ V :=
  Equiv.ofBijective (unionVertex S T)
    ⟨unionVertex_injective S T hdis, unionVertex_surjective S T hcover⟩

/-- The bridge-joined side supergraphs retain every original edge. -/
theorem le_mapped_bridge (G : SimpleGraph V) (S T : Set V)
    (hcover : S ∪ T = Set.univ) (hdis : S ∩ T = ∅)
    (hnoedges : ∀ x ∈ S, ∀ y ∈ T, ¬G.Adj x y)
    (L : SimpleGraph S) (R : SimpleGraph T)
    (hL : G.induce S ≤ L) (hR : G.induce T ≤ R) (a : S) (b : T) :
    G ≤ ((L ⊕g R) ⊔ edge (Sum.inl a) (Sum.inr b)).map (unionEquiv S T hcover hdis).toEmbedding := by
  intro x y hxy
  rcases mem_cover S T hcover x with hx | hx
  · rcases mem_cover S T hcover y with hy | hy
    · apply (SimpleGraph.map_adj _ _ _ _).mpr
      exact ⟨Sum.inl ⟨x, hx⟩, Sum.inl ⟨y, hy⟩, Or.inl (hL hxy), rfl, rfl⟩
    · exact (hnoedges x hx y hy hxy).elim
  · rcases mem_cover S T hcover y with hy | hy
    · exact (hnoedges y hy x hx hxy.symm).elim
    · apply (SimpleGraph.map_adj _ _ _ _).mpr
      exact ⟨Sum.inr ⟨x, hx⟩, Sum.inr ⟨y, hy⟩, Or.inl (hR hxy), rfl, rfl⟩

variable [Fintype V] [DecidableEq V]

/-- **Actual plane supergraph across a disconnected two-side cover.**
Join the actual side maps by one genuine bridge and transport the constructed
sphere map to V. Original edges are retained; the bridge is the only operation
used beyond the supplied side supergraphs. -/
theorem exists_plane_supergraph (G : SimpleGraph V) (S T : Set V)
    (hcover : S ∪ T = Set.univ) (hdis : S ∩ T = ∅)
    (hnoedges : ∀ x ∈ S, ∀ y ∈ T, ¬G.Adj x y)
    (L : SimpleGraph S) (R : SimpleGraph T)
    (M : by classical exact ConnectedPlaneMap L) (N : by classical exact ConnectedPlaneMap R)
    (hL : G.induce S ≤ L) (hR : G.induce T ≤ R) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlaneMap K := by
  classical
  obtain ⟨d⟩ := M.dartNonempty
  obtain ⟨e⟩ := N.dartNonempty
  let q := unionEquiv S T hcover hdis
  let J := (L ⊕g R) ⊔ edge (Sum.inl d.fst) (Sum.inr e.fst)
  let P := PlaneTopology.PlaneDisjointBridge.bridgePlaneMap L R M N d.fst e.fst
  let K := J.map q.toEmbedding
  let Q := PlaneTopology.PlaneGeneralTransport.planeMap (SimpleGraph.Iso.map q J) P
  exact ⟨K, le_mapped_bridge G S T hcover hdis hnoedges L R hL hR d.fst e.fst,
    hasPlaneMap_of_map Q⟩

#print axioms exists_plane_supergraph

end PlaneTopology.PlaneDisjointCover
