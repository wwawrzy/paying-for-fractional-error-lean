import Paper.Endpoints.Girth.HighGirthPathInternal
set_option maxHeartbeats 200000
namespace Paper.HighGirthSpanningPath

theorem connected_spanning_path
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hd : ∀ z, G.degree z ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ z : V, z ∈ p.support := by
  classical
  letI : Nonempty V := hconn.nonempty
  obtain ⟨u,v,p,hp,hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hclosed : ∀ z ∈ p.support, ∀ y, G.Adj z y → y ∈ p.support := by
    intro z hz y hzy
    by_cases hzu : z = u
    · subst z
      by_contra hy
      have hnew : (SimpleGraph.Walk.cons hzy.symm p).IsPath := hp.cons hy
      have hm := hmax y v (SimpleGraph.Walk.cons hzy.symm p) hnew
      simp only [SimpleGraph.Walk.length_cons] at hm
      omega
    · by_cases hzv : z = v
      · subst z
        by_contra hy
        have hnew := hp.concat hy hzy
        have hm := hmax u y (p.concat hzy) hnew
        simp only [SimpleGraph.Walk.length_concat] at hm
        omega
      · exact Paper.HighGirthPathInternal.internal_path_neighbors G hd u v p hp z hz hzu hzv y hzy
  have hreach : ∀ {a b : V} (w : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b w
    induction w with
    | nil => exact fun h => h
    | cons h w ih =>
      intro ha
      exact ih (hclosed _ ha _ h)
  refine ⟨u,v,p,hp,?_⟩
  intro z
  obtain ⟨w,hw⟩ := hconn.exists_isPath u z
  exact hreach w p.start_mem_support

end Paper.HighGirthSpanningPath

#print axioms Paper.HighGirthSpanningPath.connected_spanning_path
