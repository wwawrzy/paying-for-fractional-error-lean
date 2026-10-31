import Paper.Optimality.Treewidth.SixCliqueSharp
namespace Paper.CliqueEightSixFreeDegree
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem four_le (hG : G.IsKMinorFree 6) (hV : Fintype.card V = 8)
    (he : G.edgeFinset.card = 22) (v : V) : 4 ≤ G.degree v := by
  classical
  let T : Set V := {v}ᶜ
  let H := G.induce T
  have hcard : Fintype.card T = 7 := by simp [T,Fintype.card_compl_set,hV]
  have hf : H.IsKMinorFree 6 := IsHMinorFree.minor hG (IsMinor.of_induce G T)
  have hb := SixCliqueSharp.edge_bound H hf (by omega)
  rw [hcard] at hb
  have hs : H.edgeFinset.card = G.edgeFinset.card-G.degree v := by
    exact (G.card_edgeFinset_induce_compl_singleton v).trans (G.card_edgeFinset_deleteIncidenceSet v)
  omega
end Paper.CliqueEightSixFreeDegree
