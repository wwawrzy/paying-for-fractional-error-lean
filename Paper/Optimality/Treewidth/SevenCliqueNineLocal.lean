import Paper.Optimality.Treewidth.CliqueSixExtremalGeneral
import Paper.Optimality.Treewidth.SevenCliqueNineExact
namespace Paper.SevenCliqueNineLocal
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem component_vertex (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ a w, G.Adj a w → 5 ≤ Fintype.card (G.commonNeighbors a w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 9) :
    let H := G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)
    ∃ u, 3 ≤ H.degree u ∧ H.degree u ≤ 5 ∧
      (H.degree u = 3 → H.IsClique (H.neighborSet u)) ∧
      (H.edgeFinset.card = 26 → H.degree u = 4 → H.IsClique (H.neighborSet u)) ∧
      (∀ w : H.neighborSet u, ((H.induce (H.neighborSet u))ᶜ).degree w ≤ H.degree u-3) := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  let H := G.induce (T : Set V)
  have hcard : Fintype.card (T : Set V) = 9 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hsize
  have hf := CliqueExteriorComplementConnected.free_nine G hG
    (fun z => by have hh := hmin z; omega) hcn v hsep C (by omega)
  obtain ⟨hel,heu,_⟩ := SevenCliqueNineExact.component_edges G hG v hv8 hmin hcn hsep C hsize
  change 25 ≤ H.edgeFinset.card at hel
  change H.edgeFinset.card ≤ 26 at heu
  let b := 36-H.edgeFinset.card
  have hb : 10 ≤ b ∧ b ≤ 11 := by dsimp [b]; omega
  have he : H.edgeFinset.card+b = 4*Fintype.card (T : Set V) := by rw [hcard]; dsimp [b]; omega
  letI : Nonempty (T : Set V) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u,hu⟩ := H.exists_minimal_degree_vertex
  have hlow := CliqueSixExtremalGeneral.degree_deficit H hf (by omega) b he u
  have hs := H.minDegree_mul_card_le_two_mul_card_edges
  rw [hcard] at hs
  have hu3 : 3 ≤ H.degree u := by omega
  have hu5 : H.degree u ≤ 5 := by omega
  refine ⟨u,hu3,hu5,?_,?_,?_⟩
  · intro h3
    change H.degree u = 3 at h3
    have hb11 : b = 11 := by omega
    rw [hb11] at he
    exact CliqueSixExtremalGeneral.near_three_clique H hf (by omega) he u h3
  · intro h26 h4
    change H.edgeFinset.card = 26 at h26
    change H.degree u = 4 at h4
    have hb10 : b = 10 := by dsimp [b]; omega
    rw [hb10] at he
    exact CliqueSixExtremalGeneral.four_clique H hf (by omega) he u h4
  · intro w
    change ((H.induce (H.neighborSet u))ᶜ).degree w ≤ H.degree u-3
    have hh := CliqueSixExtremalGeneral.neighborhood_deficit H hf (by omega) b he u w
    omega
end Paper.SevenCliqueNineLocal
