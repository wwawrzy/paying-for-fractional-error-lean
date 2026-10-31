import Paper.Optimality.Treewidth.CliquePartitionDegrees
namespace Paper.CliqueTwoDeletion
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem induced_degree (N : Finset V) (a c z : V)
    (hd : 5 ≤ G.inducedDegree z N) :
    3 ≤ G.inducedDegree z ((N.erase a).erase c) := by
  classical
  let T := (N.erase a).erase c
  have hs : N.filter (G.Adj z) ⊆ T.filter (G.Adj z) ∪ {a,c} := by
    intro w hw
    obtain ⟨hwN,hzw⟩ := Finset.mem_filter.mp hw
    by_cases hwa : w = a
    · subst w; exact Finset.mem_union_right _ (by simp)
    by_cases hwc : w = c
    · subst w; exact Finset.mem_union_right _ (by simp)
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨by simp [T,hwa,hwc,hwN],hzw⟩)
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hc : ({a,c} : Finset V).card ≤ 2 := by simpa using (Finset.card_insert_le a ({c} : Finset V))
  change G.inducedDegree z N ≤ G.inducedDegree z T + ({a,c} : Finset V).card at hh
  change 3 ≤ G.inducedDegree z T
  omega
end Paper.CliqueTwoDeletion
