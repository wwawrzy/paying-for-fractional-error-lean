import Paper.Endpoints.Girth.HighGirthInducedDegree
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
set_option maxHeartbeats 200000
namespace Paper.HighGirthPathInternal

theorem internal_path_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ z, G.degree z ≤ 2)
    (u v : V) (p : G.Walk u v) (hp : p.IsPath) :
    ∀ z ∈ p.support, z ≠ u → z ≠ v → ∀ y, G.Adj z y → y ∈ p.support := by
  classical
  intro z hz hzu hzv y hzy
  obtain ⟨i, hiz, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hi0 : i ≠ 0 := by
    intro heq
    subst i
    exact hzu (by simpa using hiz.symm)
  have hilt : i < p.length := by
    by_contra hn
    have heq : i = p.length := by omega
    subst i
    exact hzv (by simpa using hiz.symm)
  have hnz : (p.toSubgraph.neighborSet z).ncard = 2 := by
    simpa only [hiz] using hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
  have hzdeg : (G.neighborSet z).ncard ≤ 2 := by
    rw [Set.ncard_eq_toFinset_card']
    simpa using hd z
  have heq : p.toSubgraph.neighborSet z = G.neighborSet z :=
    Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset z) (by omega)
  have hy : y ∈ p.toSubgraph.neighborSet z := heq.symm ▸ hzy
  exact (p.mem_verts_toSubgraph).mp (p.toSubgraph.neighborSet_subset_verts z hy)

end Paper.HighGirthPathInternal

#print axioms Paper.HighGirthPathInternal.internal_path_neighbors
