import Paper.Endpoints.Girth.CurrentFaceComponents
import GraphTheory.Plane.ConnectedPlaneSubgraph
import Paper.Preliminaries.Incidence

/-!
# The marked-edge face bound from forbidden-minor planarity

The component certificates are constructed for the exact original component
graphs. Thus the marked set, the edges counted by `p`, and the girth condition
outside the marked set are unchanged by the embedding construction.
-/

namespace Paper.CurrentPlanarFaceBound

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneSupergraphBasics
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Each cyclic component of an abstract planar graph has an actual faithful
plane map. Forest components need no certificate in the face-bound assembly. -/
theorem component_maps_of_isPlanar (hplanar : G.IsPlanar)
    (C : G.ConnectedComponent) (hna : ¬ C.toSimpleGraph.IsAcyclic) :
    Nonempty (ConnectedPlaneMap C.toSimpleGraph) := by
  have hcard : 2 ≤ Fintype.card C := by
    by_contra h
    have hsmall : Fintype.card C ≤ 2 := by omega
    apply hna
    exact IsAcyclic.of_card_le_two (by
      rw [ENat.card_eq_coe_fintype_card]
      exact_mod_cast hsmall)
  apply (hasPlaneMap_iff_nonempty C.toSimpleGraph).mp
  exact PlaneTopology.ConnectedPlaneSubgraph.hasPlaneMap_of_isPlanar_connected
    C.toSimpleGraph (hplanar.induce C.supp) C.connected_toSimpleGraph hcard

/-- The paper's short-face estimate, in cross-multiplied natural form.
The original independent-set hypothesis is unnecessary for this estimate. -/
theorem edge_bound
    (hplanar : G.IsPlanar) (A : Finset V) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length) :
    (g - 2) * G.edgeFinset.card ≤
      g * Fintype.card V +
        (g - 3) * (CurrentFaceBound.incidentMarkedEdges (G := G) A).card :=
  CurrentFaceComponents.edge_bound_of_component_maps A g hg hgirth
    (component_maps_of_isPlanar hplanar)

/-- The same estimate with the exact coefficients printed in the paper. -/
theorem real_edge_bound
    (hplanar : G.IsPlanar) (A : Finset V) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length) :
    (G.edgeFinset.card : ℝ) ≤
      (g : ℝ) / ((g : ℝ) - 2) * Fintype.card V +
        ((g : ℝ) - 3) / ((g : ℝ) - 2) *
          (CurrentFaceBound.incidentMarkedEdges (G := G) A).card := by
  have h : (((g - 2 : ℕ) : ℝ) * (G.edgeFinset.card : ℝ)) ≤
      (g : ℝ) * (Fintype.card V : ℝ) +
        ((g - 3 : ℕ) : ℝ) *
          ((CurrentFaceBound.incidentMarkedEdges (G := G) A).card : ℝ) := by
    exact_mod_cast edge_bound hplanar A g hg hgirth
  rw [Nat.cast_sub (by omega : 2 ≤ g), Nat.cast_sub hg] at h
  norm_num only [Nat.cast_ofNat] at h
  have hpos : (0 : ℝ) < (g : ℝ) - 2 := by
    have hgR : (3 : ℝ) ≤ g := by exact_mod_cast hg
    linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [h]

/-- With no marked vertices the face estimate becomes the usual girth
density estimate, including forests and empty graphs. -/
theorem girth_edge_bound
    (hplanar : G.IsPlanar) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    (G.edgeFinset.card : ℝ) ≤
      (g : ℝ) / ((g : ℝ) - 2) * Fintype.card V := by
  have hgirth' : ∀ (v : {x : V // x ∉ (∅ : Finset V)})
      (c : (G.induce {x : V | x ∉ (∅ : Finset V)}).Walk v v),
      c.IsCycle → g ≤ c.length := by
    intro v c hc
    let f : (G.induce {x : V | x ∉ (∅ : Finset V)}) →g G :=
      { toFun := Subtype.val
        map_rel' := fun h => h }
    have hcycle : (c.map f).IsCycle :=
      (Walk.map_isCycle_iff_of_injective (f := f) Subtype.val_injective).mpr hc
    simpa only [Walk.length_map] using hgirth (f v) (c.map f) hcycle
  simpa [CurrentFaceBound.incidentMarkedEdges,
    GirthFaceOccurrenceBudget.markedEdges] using
      real_edge_bound hplanar ∅ g hg hgirth'

/-- Girth is inherited by every induced subgraph, so the density hypothesis
used by the noninteger rounding theorem holds with `a = g/(g-2)`. -/
theorem induced_density
    (hplanar : G.IsPlanar) (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    Incidence.InducedDensityBound G ((g : ℝ) / ((g : ℝ) - 2)) := by
  classical
  intro S
  have hgirthS : ∀ (v : (S : Set V))
      (c : (G.induce (S : Set V)).Walk v v),
      c.IsCycle → g ≤ c.length := by
    intro v c hc
    let f : G.induce (S : Set V) →g G :=
      { toFun := Subtype.val
        map_rel' := fun h => h }
    have hcycle : (c.map f).IsCycle :=
      (Walk.map_isCycle_iff_of_injective (f := f) Subtype.val_injective).mpr hc
    simpa only [Walk.length_map] using hgirth (f v) (c.map f) hcycle
  have h := girth_edge_bound (hplanar.induce (S : Set V)) g hg hgirthS
  simpa only [SimpleGraph.inducedEdgeCount, Fintype.card_eq_nat_card,
    Finset.coe_sort_coe, Nat.card_eq_finsetCard] using h

end Paper.CurrentPlanarFaceBound

#print axioms Paper.CurrentPlanarFaceBound.component_maps_of_isPlanar
#print axioms Paper.CurrentPlanarFaceBound.edge_bound
#print axioms Paper.CurrentPlanarFaceBound.real_edge_bound
#print axioms Paper.CurrentPlanarFaceBound.girth_edge_bound
#print axioms Paper.CurrentPlanarFaceBound.induced_density
