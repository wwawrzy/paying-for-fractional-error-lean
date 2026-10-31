import Paper.Optimality.Treewidth.CliqueAffineCore
import Paper.Optimality.Treewidth.CliqueFourElimination

/-! The additive extremal bound for K5-free graphs. The affine threshold
retains the constant six, which is needed when filling small neighborhoods. -/
namespace Paper.FiveCliqueSharp

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_bound (hG : G.IsKMinorFree 5) (hV : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  by_contra hbound
  have hdense : 3 * Fintype.card V - 5 ≤ G.edgeFinset.card := by omega
  obtain ⟨W, _, _, H, _, hW, _, hp, hc, hm⟩ :=
    CliqueAffineCore.extract G 3 5 3 (by decide) (by decide) (by decide) hV hdense
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let v : W := Classical.arbitrary W
  have hH : H.IsKMinorFree 5 := IsHMinorFree.minor hG hm
  have hN : 0 < Fintype.card (H.neighborSet v) := by
    rw [H.card_neighborSet_eq_degree]
    exact hp v
  letI : Nonempty (H.neighborSet v) := Fintype.card_pos_iff.mp hN
  obtain ⟨w, hw⟩ := CliqueFourElimination.low_degree (H.induce (H.neighborSet v))
    (CliqueDenseCore.neighborhood_excludes_four H hH v)
  have hh := commonNeighbors_implies_induced_degree H v 3 w (hc v w w.property)
  omega

end Paper.FiveCliqueSharp

#print axioms Paper.FiveCliqueSharp.edge_bound
