import Paper.Endpoints.Girth.HighGirthResidualPaths
set_option maxHeartbeats 200000
namespace Paper.HighGirthInducedPaths

theorem lift_internal_path
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (w : G.Walk u v) (hw : w.IsPath) (hs : ∀ a ∈ w.support, a ∈ S) :
    ∃ q : (G.induce (↑S : Set V)).Walk ⟨u, hu⟩ ⟨v, hv⟩,
      q.IsPath ∧ q.length = w.length ∧
      q.map (SimpleGraph.Embedding.induce (↑S : Set V)).toHom = w := by
  classical
    let q := w.induce (↑S : Set V) hs
    have hmap : q.map (SimpleGraph.Embedding.induce (↑S : Set V)).toHom = w := by
      exact w.map_induce hs
    have hq : q.IsPath := by
      apply SimpleGraph.Walk.IsPath.of_map
      rw [hmap]
      exact hw
    have hlen : q.length = w.length := by
      have hh := congrArg SimpleGraph.Walk.length hmap
  
  
  
      have hlen_map : (q.map (SimpleGraph.Embedding.induce (↑S : Set V)).toHom).length = q.length :=
        SimpleGraph.Walk.length_map (SimpleGraph.Embedding.induce (↑S : Set V)).toHom q
  
  
  
  
  
      rw [hlen_map] at hh
      exact hh
    exact ⟨q, hq, hlen, hmap⟩

end Paper.HighGirthInducedPaths

#print axioms Paper.HighGirthInducedPaths.lift_internal_path
