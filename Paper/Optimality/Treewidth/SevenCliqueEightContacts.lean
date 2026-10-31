import Paper.Optimality.Treewidth.SevenCliqueEightExact
import Paper.Optimality.Treewidth.CliqueEightSixFreeDegree
import Paper.Optimality.Treewidth.SevenCliqueEightRegular
namespace Paper.SevenCliqueEightContacts
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem bounds (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8)
    (x : V) (hx : x ∈ vertices (outside G (insert v (G.neighborSet v)) C)) :
    4 ≤ G.inducedDegree x (vertices (outside G (insert v (G.neighborSet v)) C)) ∧
    G.inducedDegree x (vertices (outside G (insert v (G.neighborSet v)) C))ᶜ ≤ 4 := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  let H := G.induce (T : Set V)
  have hf := SevenCliqueEightComponent.small_component_free G hG v hv8 hmin C (by omega)
  have he := SevenCliqueEightExact.component_edges G hG v hv8 hmin hcn C hsize
  have hcard : Fintype.card (T : Set V) = 8 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hsize
  have hd := CliqueEightSixFreeDegree.four_le H hf hcard he ⟨x,hx⟩
  rw [InducedCounting.degree_induce_eq_inducedDegree G T ⟨x,hx⟩] at hd
  change 4 ≤ G.inducedDegree x T at hd
  have h8 := SevenCliqueEightRegular.component_regular G hG v hv8 hmin hcn C hsize x hx
  have hp := CliquePartitionDegrees.partition G T x
  change 4 ≤ G.inducedDegree x T ∧ G.inducedDegree x Tᶜ ≤ 4
  exact ⟨hd,by omega⟩
end Paper.SevenCliqueEightContacts
