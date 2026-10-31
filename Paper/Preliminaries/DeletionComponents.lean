import Paper.Preliminaries.WeakProjection

/-! Physical vertex sets of actual connected components after deletion.
They are connected, disjoint from the deleted set and closed under edges
whose second endpoint was not deleted. -/
namespace Paper.DeletionComponents
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev deleted (X : Finset V) : SimpleGraph {v // v ∉ X} := G.induce {v | v ∉ X}

noncomputable def physical (X : Finset V) (C : (deleted G X).ConnectedComponent) : Finset V :=
  C.supp.toFinset.image Subtype.val

theorem mem_physical (X : Finset V) (C : (deleted G X).ConnectedComponent) (v : V) :
    v ∈ physical G X C ↔ ∃ hv : v ∉ X, (⟨v, hv⟩ : {v // v ∉ X}) ∈ C.supp := by
  classical
  constructor
  · intro hv
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    have hu' := Set.mem_toFinset.mp hu
    refine ⟨he ▸ u.property, ?_⟩
    have he' : u = (⟨v, he ▸ u.property⟩ : {v // v ∉ X}) := Subtype.ext he
    exact he' ▸ hu'
  · rintro ⟨hv, hC⟩
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Set.mem_toFinset.mpr hC, rfl⟩

theorem nonempty (X : Finset V) (C : (deleted G X).ConnectedComponent) : (physical G X C).Nonempty :=
  ⟨C.out.val, (mem_physical G X C _).mpr ⟨C.out.property, C.out_eq⟩⟩

theorem avoids (X : Finset V) (C : (deleted G X).ConnectedComponent) : Disjoint (physical G X C) X := by
  apply Finset.disjoint_left.mpr
  intro v hv hx
  exact (mem_physical G X C v).mp hv |>.choose hx

theorem connected (X : Finset V) (C : (deleted G X).ConnectedComponent) :
    (G.induce (physical G X C : Set V)).Connected := by
  classical
  have hc := WeakProjection.connected_image (deleted G X) G Subtype.val
    (fun _ _ h => Or.inr h) C.supp C.connected_toSimpleGraph
  have he : Subtype.val '' C.supp = (physical G X C : Set V) := by
    ext v
    simp only [physical, Set.mem_image, Finset.mem_coe, Finset.mem_image, Set.mem_toFinset]
  rwa [he] at hc

theorem closed (X : Finset V) (C : (deleted G X).ConnectedComponent) {u v : V}
    (hu : u ∈ physical G X C) (hv : v ∉ X) (ha : G.Adj u v) : v ∈ physical G X C := by
  obtain ⟨huX, huC⟩ := (mem_physical G X C u).mp hu
  exact (mem_physical G X C v).mpr ⟨hv, C.mem_supp_of_adj_mem_supp huC ha⟩

theorem disjoint (X : Finset V) (C D : (deleted G X).ConnectedComponent) (hne : C ≠ D) :
    Disjoint (physical G X C) (physical G X D) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  obtain ⟨hvX, hC⟩ := (mem_physical G X C v).mp hvC
  obtain ⟨_, hD⟩ := (mem_physical G X D v).mp hvD
  exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hC hD)

theorem covers (X : Finset V) {v : V} (hv : v ∉ X) :
    v ∈ physical G X ((deleted G X).connectedComponentMk ⟨v, hv⟩) :=
  (mem_physical G X _ v).mpr ⟨hv, rfl⟩
end Paper.DeletionComponents
