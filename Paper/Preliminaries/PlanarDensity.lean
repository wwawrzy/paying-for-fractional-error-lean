import GraphTheory.Plane.WagnerGeneralEmbedding
import GraphTheory.Plane.TriangularFaces
import Paper.Preliminaries.MinorDensity

/-! Discharge the all-minors density hypothesis from actual forbidden-minor
planarity, using the existing constructive Wagner embedding development. -/
namespace Paper.PlanarDensity
open SimpleGraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_bound (hG : G.IsPlanar) : G.edgeFinset.card ≤ 3 * Fintype.card V := by
  classical
  by_cases hn : 3 ≤ Fintype.card V
  · obtain ⟨T, hGT, M, htri⟩ :=
      PlaneTopology.WagnerGeneralEmbedding.hasTriangulatedSupergraph_of_isPlanar G hG hn
    have hsat := TriangularFaces.saturated_of_triangular_rotation
      M.rawRotation M.euler htri
    have hmono := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
    omega
  · have h := G.card_edgeFinset_le_card_choose_two
    have hn' : Fintype.card V = 0 ∨ Fintype.card V = 1 ∨ Fintype.card V = 2 := by omega
    have hc : (Fintype.card V).choose 2 ≤ 3 * Fintype.card V := by
      rcases hn' with hzero | hone | htwo
      · rw [hzero]; decide
      · rw [hone]; decide
      · rw [htwo]; decide
    exact h.trans hc

theorem minor_density (hG : G.IsPlanar) : MinorDensity.Bound G 3 := by
  classical
  intro A _ _ J _ hm
  have hp : J.IsPlanar := ⟨IsHMinorFree.minor hG.1 hm, IsHMinorFree.minor hG.2 hm⟩
  exact_mod_cast edge_bound J hp
end Paper.PlanarDensity
