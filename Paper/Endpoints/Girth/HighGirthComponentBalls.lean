import Paper.Endpoints.Girth.HighGirthRetainedPartition

namespace Paper.HighGirthComponentBalls
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)

theorem adjacent_member
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (u v : V) (hu : u ∈ HighGirthFreePaths.members G x K)
    (hv : v ∈ HighGirthRounding.last G x) (hadj : G.Adj u v) :
    v ∈ HighGirthFreePaths.members G x K := by
  classical
  obtain ⟨huU,hK⟩ := (Finset.mem_filter.mp hu).2
  have ha : (G.induce (↑(HighGirthRounding.last G x) : Set V)).Adj ⟨u,huU⟩ ⟨v,hv⟩ := hadj
  have he := SimpleGraph.ConnectedComponent.sound ha.reachable
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨hv,he.symm.trans hK⟩⟩

theorem ball_stays_in_component
    (K : (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (a : V) (ha : a ∈ HighGirthFreePaths.members G x K) :
    HighGirthAccessSets.uBallTwo G x a ⊆ HighGirthFreePaths.members G x K := by
  classical
  have hstep : ∀ u ∈ HighGirthFreePaths.members G x K,
      HighGirthAccessSets.neighborsU G x u ⊆ HighGirthFreePaths.members G x K := by
    intro u hu v hv
    obtain ⟨hvu,hvU⟩ := Finset.mem_inter.mp hv
    exact adjacent_member G x K u v hu hvU ((G.mem_neighborFinset u v).mp hvu)
  intro u hu
  rcases Finset.mem_insert.mp hu with he | hu
  · simpa only [he] using ha
  rcases Finset.mem_union.mp hu with hu | hu
  · exact hstep a ha hu
  · obtain ⟨v,hv,hu⟩ := Finset.mem_biUnion.mp hu
    exact hstep v (hstep a ha hv) (Finset.mem_sdiff.mp hu).1

end Paper.HighGirthComponentBalls
#print axioms Paper.HighGirthComponentBalls.adjacent_member
#print axioms Paper.HighGirthComponentBalls.ball_stays_in_component
