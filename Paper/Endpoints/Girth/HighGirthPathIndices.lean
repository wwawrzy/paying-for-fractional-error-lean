import Paper.Endpoints.Girth.HighGirthPathMetric
set_option maxHeartbeats 200000
namespace Paper.HighGirthPathIndices

theorem ordered_index_distance
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hpath : Paper.HighGirthFreePaths.isPathComponent G x K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ p.length) :
    K.toSimpleGraph.dist (p.getVert i) (p.getVert j) = j - i := by
  have hplen := Paper.HighGirthPathMetric.path_length_eq_distance G x K hpath a b p hp
  have hsub : ((p.drop i).take (j - i)).IsSubwalk p :=
    (SimpleGraph.Walk.isSubwalk_take (p.drop i) (j - i)).trans (SimpleGraph.Walk.isSubwalk_drop p i)
  have hh := SimpleGraph.length_eq_dist_of_subwalk hplen hsub
  have hlen : ((p.drop i).take (j - i)).length = j - i := by
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length]
    exact Nat.min_eq_left (by omega)
  have hend : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [SimpleGraph.Walk.drop_getVert]
    have he : i + (j - i) = j := by omega
    rw [he]
  rw [hlen] at hh
  simpa only [hend] using hh.symm

end Paper.HighGirthPathIndices

#print axioms Paper.HighGirthPathIndices.ordered_index_distance
