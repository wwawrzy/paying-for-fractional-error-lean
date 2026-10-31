import Paper.Optimality.Treewidth.SevenCliqueGlobalReduction
namespace Paper.SevenCliqueNineOrder
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
/-- Handshaking in an affine K7 extremal core of minimum degree at least nine. -/
theorem order_twenty_eight (v : V) (hv : G.degree v = 9)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (he : G.edgeFinset.card+14 = 5*Fintype.card V) : 28 ≤ Fintype.card V := by
  letI : Nonempty V := ⟨v⟩
  have hm : 9 ≤ G.minDegree := G.le_minDegree_of_forall_le_degree 9 (fun z => by simpa [hv] using hmin z)
  have hs := G.minDegree_mul_card_le_two_mul_card_edges
  have hh := Nat.mul_le_mul_right (Fintype.card V) hm
  omega
end Paper.SevenCliqueNineOrder
