import GraphTheory.Plane.PlaneLeafInsertion
import GraphTheory.Plane.PlaneGeneralTransport
import GraphTheory.Plane.PlaneTriangulationMaximal

/-! # Extending an actual plane supergraph across one isolated vertex -/

namespace PlaneTopology.PlaneSingletonExtension

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneLeafInsertion PlaneTopology.PlaneTriangulationMaximal

variable {V : Type*}

/-- Identify the fresh leaf with the singled-out ambient vertex. -/
def singletonVertex (S : Set V) (b : V) : Option S → V
  | none => b
  | some x => x.1

theorem singletonVertex_injective (S : Set V) (b : V) (hb : b ∉ S) :
    Function.Injective (singletonVertex S b) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      change b = y.1 at h
      exact (hb (h.symm ▸ y.2)).elim
  | some x =>
    cases y with
    | none =>
      change x.1 = b at h
      exact (hb (h ▸ x.2)).elim
    | some y => exact congrArg some (Subtype.ext h)

/-- Every vertex other than the singleton belongs to the other side. -/
theorem mem_side_of_ne (S : Set V) (b : V) (hcover : S ∪ {b} = Set.univ)
    {x : V} (hx : x ≠ b) : x ∈ S := by
  have hm : x ∈ S ∪ {b} := hcover.symm ▸ Set.mem_univ x
  exact hm.resolve_right (by simpa using hx)

theorem singletonVertex_surjective (S : Set V) (b : V) (hcover : S ∪ {b} = Set.univ) :
    Function.Surjective (singletonVertex S b) := by
  classical
  intro x
  by_cases hx : x = b
  · exact ⟨none, hx.symm⟩
  · exact ⟨some ⟨x, mem_side_of_ne S b hcover hx⟩, rfl⟩

/-- Actual vertex equivalence from the leaf-extended side to the original type. -/
noncomputable def singletonEquiv (S : Set V) (b : V) (hb : b ∉ S)
    (hcover : S ∪ {b} = Set.univ) : Option S ≃ V :=
  Equiv.ofBijective (singletonVertex S b)
    ⟨singletonVertex_injective S b hb, singletonVertex_surjective S b hcover⟩

/-- In a singleton separation, the distinguished vertex is genuinely isolated. -/
theorem not_adj_singleton (G : SimpleGraph V) (S : Set V) (b : V)
    (hcover : S ∪ {b} = Set.univ) (hnoedges : ∀ x ∈ S, ¬G.Adj b x) (x : V) :
    ¬G.Adj b x := by
  classical
  by_cases hx : x = b
  · subst x
    intro h
    exact h.ne rfl
  · exact hnoedges x (mem_side_of_ne S b hcover hx)

/-- Mapping any true leaf extension contains the original singleton-separated graph. -/
theorem le_mapped_leaf (G : SimpleGraph V) (S : Set V) (b : V) (hb : b ∉ S)
    (hcover : S ∪ {b} = Set.univ) (hnoedges : ∀ x ∈ S, ¬G.Adj b x)
    (H : SimpleGraph S) (hdom : G.induce S ≤ H) (a : S) :
    G ≤ (leafGraph H a).map (singletonEquiv S b hb hcover).toEmbedding := by
  intro x y hxy
  have hx : x ≠ b := by
    intro h
    exact not_adj_singleton G S b hcover hnoedges y (h ▸ hxy)
  have hy : y ≠ b := by
    intro h
    exact not_adj_singleton G S b hcover hnoedges x (h ▸ hxy.symm)
  let x' : S := ⟨x, mem_side_of_ne S b hcover hx⟩
  let y' : S := ⟨y, mem_side_of_ne S b hcover hy⟩
  apply (SimpleGraph.map_adj _ _ _ _).mpr
  exact ⟨some x', some y', hdom hxy, rfl, rfl⟩

variable [Fintype V] [DecidableEq V]

/-- **Actual plane supergraph across an isolated singleton side.** Choose an
existing vertex from the supplied edgeful plane map, add the singleton as a
genuine leaf, then transport the constructed sphere map to the original V. -/
theorem exists_plane_supergraph (G : SimpleGraph V) (S : Set V) (b : V) (hb : b ∉ S)
    (hcover : S ∪ {b} = Set.univ) (hnoedges : ∀ x ∈ S, ¬G.Adj b x)
    (H : SimpleGraph S) (M : by classical exact ConnectedPlaneMap H)
    (hdom : G.induce S ≤ H) :
    ∃ T : SimpleGraph V, G ≤ T ∧ HasPlaneMap T := by
  classical
  obtain ⟨d⟩ := M.dartNonempty
  let e := singletonEquiv S b hb hcover
  let T := (leafGraph H d.fst).map e.toEmbedding
  let N := PlaneTopology.PlaneGeneralTransport.planeMap (SimpleGraph.Iso.map e (leafGraph H d.fst))
    (leafPlaneMap H d.fst M)
  exact ⟨T, le_mapped_leaf G S b hb hcover hnoedges H hdom d.fst, hasPlaneMap_of_map N⟩

#print axioms exists_plane_supergraph

end PlaneTopology.PlaneSingletonExtension
