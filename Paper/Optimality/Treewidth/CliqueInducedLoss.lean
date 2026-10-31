import Paper.Optimality.Treewidth.CliquePartitionDegrees
namespace Paper.CliqueInducedLoss
open SimpleGraph
variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem bound (N B : Finset V) (z : V) :
    G.inducedDegree z N ≤ G.inducedDegree z B + (N \ B).card := by
  classical
  have hs : N.filter (G.Adj z) ⊆ B.filter (G.Adj z) ∪ (N \ B) := by
    intro w hw
    obtain ⟨hwN,hzw⟩ := Finset.mem_filter.mp hw
    by_cases hwB : w ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwB,hzw⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwN,hwB⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
end Paper.CliqueInducedLoss
