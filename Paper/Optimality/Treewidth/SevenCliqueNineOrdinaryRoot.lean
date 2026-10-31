import Paper.Optimality.Treewidth.CliqueNineTwoLow
import Paper.Optimality.Treewidth.SevenCliqueNineDegree
namespace Paper.SevenCliqueNineOrdinaryRoot
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem exists_low_root (hG : G.IsKMinorFree 7) (v : V) (hv8 : G.degree v = 8)
    (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ a w, G.Adj a w → 5 ≤ Fintype.card (G.commonNeighbors a w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 9) :
    let H := G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)
    ∃ u, H.degree u ≤ 5 ∧ G.degree u.val = 8 := by
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
  have hlow : 2 ≤ (Finset.univ.filter (fun x => H.degree x ≤ 5)).card := by
    by_cases h26 : H.edgeFinset.card = 26
    · exact CliqueNineTwoLow.two_low H hf hcard h26
    · exact CliqueNineTwoLow.two_low_near H hf hcard (by omega)
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hlow
  have ha5 := (Finset.mem_filter.mp ha).2
  have hb5 := (Finset.mem_filter.mp hb).2
  have hhigh := SevenCliqueNineDegree.component_high_count G hG v hv8 hmin hcn hsep C hsize
  let P := T.filter (fun x => 9 ≤ G.degree x)
  change P.card ≤ 1 at hhigh
  have hmina : 8 ≤ G.degree a.val := by have hh := hmin a.val; omega
  have hminb : 8 ≤ G.degree b.val := by have hh := hmin b.val; omega
  by_cases ha8 : G.degree a.val = 8
  · exact ⟨a,ha5,ha8⟩
  · have haP : a.val ∈ P := Finset.mem_filter.mpr ⟨a.property,by omega⟩
    have hb8 : G.degree b.val = 8 := by
      by_contra hn
      have hbP : b.val ∈ P := Finset.mem_filter.mpr ⟨b.property,by omega⟩
      have heq := Finset.card_le_one.mp hhigh a.val haP b.val hbP
      exact hab (Subtype.ext heq)
    exact ⟨b,hb5,hb8⟩
end Paper.SevenCliqueNineOrdinaryRoot
