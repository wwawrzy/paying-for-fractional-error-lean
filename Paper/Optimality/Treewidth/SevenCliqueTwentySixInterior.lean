import Paper.Optimality.Treewidth.SevenCliqueTwentySixNeighborhood
import Paper.Optimality.Treewidth.SevenCliqueEightContacts
import Paper.Optimality.Treewidth.CliqueSixExtremalLocal
namespace Paper.SevenCliqueTwentySixInterior
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem five_le (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8)
    (x : V) (hx : x ∈ vertices (outside G (insert v (G.neighborSet v)) C)) :
    5 ≤ G.inducedDegree x (vertices (outside G (insert v (G.neighborSet v)) C)) := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  let H := G.induce (T : Set V)
  have hm : ∀ z, G.degree v ≤ G.degree z := by intro z; rw [hv8]; exact hmin z
  have hlo := (SevenCliqueEightContacts.bounds G hG v hv8 hm (hcn v) C hsize x hx).1
  change 4 ≤ G.inducedDegree x T at hlo
  change 5 ≤ G.inducedDegree x T
  by_contra hn
  have hint : G.inducedDegree x T = 4 := by omega
  have hx8 := SevenCliqueEightRegular.component_regular G hG v hv8 hm (hcn v) C hsize x hx
  have hf := SevenCliqueEightComponent.small_component_free G hG v hv8 hm C (by omega)
  have he := SevenCliqueEightExact.component_edges G hG v hv8 hm (hcn v) C hsize
  have hcard : Fintype.card (T : Set V) = 8 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hsize
  have hd : H.degree ⟨x,hx⟩ = 4 := by rw [InducedCounting.degree_induce_eq_inducedDegree G T ⟨x,hx⟩]; exact hint
  have hclH := CliqueSixExtremalLocal.four_clique H hf hcard he ⟨x,hx⟩ hd
  let S := T.filter (G.Adj x)
  have hS : S.card = 4 := hint
  have hsub : S ⊆ G.neighborFinset x := by
    intro y hy
    exact (G.mem_neighborFinset x y).mpr (Finset.mem_filter.mp hy).2
  have hcl : G.IsClique (S : Set V) := by
    intro a ha b hb hab
    obtain ⟨haT,hxa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbT,hxb⟩ := Finset.mem_filter.mp hb
    exact hclH (show (⟨a,haT⟩ : (T : Set V)) ∈ H.neighborSet ⟨x,hx⟩ from hxa)
      (show (⟨b,hbT⟩ : (T : Set V)) ∈ H.neighborSet ⟨x,hx⟩ from hxb)
      (fun hh => hab (congrArg Subtype.val hh))
  exact SevenCliqueTwentySixNeighborhood.no_four_clique G hG x hx8
    (fun z => by rw [hx8]; exact hmin z) (hcn x) (by rw [hx8,horder]; decide)
    hsep horder S hS hsub hcl
end Paper.SevenCliqueTwentySixInterior
