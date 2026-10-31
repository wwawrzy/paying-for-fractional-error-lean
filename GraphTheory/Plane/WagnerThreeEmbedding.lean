import GraphTheory.Plane.WagnerContractionEmbedding
import GraphTheory.Plane.PlaneTriangulation

/-!
# Constructive Wagner embedding for three-connected graphs

Strong induction on the actual vertex cardinality. K4 has an explicit
tetrahedral map; every other three-connected graph has a strictly smaller
three-connected edge contraction. The proved reverse-contraction surgery
returns the original graph's actual faithful sphere map.
-/

namespace PlaneTopology.WagnerThreeEmbedding

open SimpleGraph SimpleGraph.EdgeContraction PlaneTopology.Faces.FaithfulPlaneMap
  PlaneTopology.WagnerContractionGraph PlaneTopology.WagnerContractionEmbedding

universe u

/-- Three-connected graphs with neither forbidden minor have actual faithful
connected plane maps. No geometric provider or density axiom is assumed. -/
theorem exists_planeMap_of_isPlanar_three {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsPlanar)
    (h3 : G.IsKConnected 3) : Nonempty (ConnectedPlaneMap G) := by
  classical
  suffices h : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Fintype.card W = n →
        H.IsPlanar → H.IsKConnected 3 → Nonempty (ConnectedPlaneMap H) by
    exact h _ V G rfl hG h3
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H _ hcard hplanar hconn
    by_cases hK4 : Nonempty (H ≃g (⊤ : SimpleGraph (Fin 4)))
    · obtain ⟨e⟩ := hK4
      exact ⟨PlaneTopology.PlaneGeneralTransport.planeMap e.symm PlaneTopology.PlaneSmallBases.tetrahedronPlaneMap⟩
    · obtain ⟨x, y, hxy, hplanarC, hconnC, hsmaller⟩ :=
        exists_smaller_planar_three_contraction H hplanar hconn hK4
      obtain ⟨M⟩ := ih (Fintype.card (ContrVertex x y))
        (by simpa only [hcard] using hsmaller)
        (ContrVertex x y) (contrGraph H x y) rfl hplanarC hconnC
      exact exists_planeMap_of_contracted_map H x y hplanar hconn hxy hconnC M

/-- A chosen actual sphere map supplied solely by three-connectivity and
the original forbidden-minor definition of planarity. -/
noncomputable def planeMapOfIsPlanarThree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsPlanar)
    (h3 : G.IsKConnected 3) : ConnectedPlaneMap G :=
  (exists_planeMap_of_isPlanar_three G hG h3).some

/-- Every three-connected forbidden-minor planar graph admits a triangular
plane supergraph on the same vertex type. -/
theorem hasTriangulatedSupergraph_of_isPlanar_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsPlanar)
    (h3 : G.IsKConnected 3) : TriangularFaces.HasTriangulatedSupergraph G := by
  have hcard := isKConnected_three_card_ge_four G h3
  exact PlaneTopology.PlaneTriangulation.hasTriangulatedSupergraph_of_connectedPlaneMap
    (planeMapOfIsPlanarThree G hG h3) (by omega)

#print axioms exists_planeMap_of_isPlanar_three
#print axioms hasTriangulatedSupergraph_of_isPlanar_three

end PlaneTopology.WagnerThreeEmbedding
