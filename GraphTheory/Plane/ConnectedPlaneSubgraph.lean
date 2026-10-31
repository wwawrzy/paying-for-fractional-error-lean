import GraphTheory.Plane.PlaneEdgeDeletion
import GraphTheory.Plane.WagnerGeneralEmbedding

/-!
# Plane maps of connected spanning subgraphs

Deleting an edge outside a fixed connected spanning subgraph preserves
connectedness. Iterating the actual edge-deletion constructor therefore
restricts a plane supergraph to that subgraph. Together with the constructive
Wagner supergraph theorem, this supplies an exact map of a connected
forbidden-minor planar graph with at least two vertices.
-/

namespace PlaneTopology.ConnectedPlaneSubgraph

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlaneTriangulationMaximal
open PlaneTopology.PlaneSupergraphBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected spanning subgraph inherits an actual faithful sphere map.
The proof removes only edges absent from the target graph. -/
theorem hasPlaneMap_of_connected_subgraph
    {G H : SimpleGraph V} (hGH : G ≤ H) (hG : G.Connected)
    (hH : HasPlaneMap H) : HasPlaneMap G := by
  classical
  suffices h : ∀ n : ℕ, ∀ H : SimpleGraph V,
      Nat.card H.edgeSet = n → G ≤ H → HasPlaneMap H → HasPlaneMap G by
    exact h _ H rfl hGH hH
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hcard hGH hH
    by_cases hHG : H ≤ G
    · have heq : H = G := le_antisymm hHG hGH
      simpa only [heq] using hH
    have hex : ∃ u v, H.Adj u v ∧ ¬ G.Adj u v := by
      by_contra! h
      exact hHG h
    obtain ⟨u, v, huv, hnot⟩ := hex
    let K := H.deleteEdges {s(u, v)}
    have hGK : G ≤ K := by
      intro x y hxy
      refine deleteEdges_adj.mpr ⟨hGH hxy, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnot hxy
      · exact hnot hxy.symm
    have hK : K.Connected := Connected.mono hGK hG
    have hKH : K < H := by
      refine lt_of_le_of_ne (H.deleteEdges_le _) ?_
      intro heq
      have hbad : K.Adj u v := heq.symm ▸ huv
      simpa [K] using hbad
    have hlt : Nat.card K.edgeSet < n := by
      have h := Finset.card_lt_card (edgeFinset_strict_mono hKH)
      simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card, hcard] using h
    obtain ⟨M⟩ := (hasPlaneMap_iff_nonempty H).mp hH
    exact ih _ hlt K rfl hGK
      (hasPlaneMap_of_map
        (PlaneTopology.PlaneEdgeDeletion.deleteEdgePlaneMap H u v M huv hK))

/-- The constructive forbidden-minor theorem yields a map of the exact
connected graph, rather than merely a supergraph with extra edges. -/
theorem hasPlaneMap_of_isPlanar_connected
    (G : SimpleGraph V) (hplanar : G.IsPlanar) (hconn : G.Connected)
    (hcard : 2 ≤ Fintype.card V) : HasPlaneMap G := by
  obtain ⟨H, hGH, hH⟩ :=
    PlaneTopology.WagnerGeneralEmbedding.hasPlaneSupergraph_of_isPlanar
      G hplanar hcard
  exact hasPlaneMap_of_connected_subgraph hGH hconn hH

end PlaneTopology.ConnectedPlaneSubgraph

#print axioms PlaneTopology.WagnerGeneralEmbedding.hasPlaneSupergraph_of_isPlanar
#print axioms PlaneTopology.PlaneEdgeDeletion.deleteEdgePlaneMap
#print axioms PlaneTopology.ConnectedPlaneSubgraph.hasPlaneMap_of_connected_subgraph
#print axioms PlaneTopology.ConnectedPlaneSubgraph.hasPlaneMap_of_isPlanar_connected
