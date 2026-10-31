import Paper.Optimality.Treewidth.CliqueTwoVertexBoundary
namespace Paper.CliqueTwoVertexEdge
open SimpleGraph CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem adjacent (x y : V) (hb : (boundary G ({x,y} : Set V)).card ≤ 7)
    (hd : 8 ≤ G.degree x) : G.Adj x y := by
  classical
  by_contra hn
  have hs : G.neighborFinset x ⊆ boundary G ({x,y} : Set V) := by
    intro z hz
    have hxz := (G.mem_neighborFinset x z).mp hz
    apply (mem_boundary G _ z).mpr
    refine ⟨?_,x,by simp,hxz.symm⟩
    intro hh
    rcases hh with he | he
    · exact G.irrefl (he ▸ hxz)
    · exact hn ((show z = y from he) ▸ hxz)
  have hh := Finset.card_le_card hs
  rw [G.card_neighborFinset_eq_degree] at hh
  omega
end Paper.CliqueTwoVertexEdge
