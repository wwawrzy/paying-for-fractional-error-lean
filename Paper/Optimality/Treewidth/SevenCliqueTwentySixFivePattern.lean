import Paper.Optimality.Treewidth.CliqueFiveMissingMatching
import Paper.Optimality.Treewidth.SevenCliqueTwentySixInterior
namespace Paper.SevenCliqueTwentySixFivePattern
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem matching (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8)
    (u : (vertices (outside G (insert v (G.neighborSet v)) C) : Set V))
    (hu : (G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)).degree u = 5) :
    let H := G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)
    ((H.induce (H.neighborSet u))ᶜ).edgeFinset.card = 2 := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  let H := G.induce (T : Set V)
  let J := H.induce (H.neighborSet u)
  have hm : ∀ z, G.degree v ≤ G.degree z := by intro z; rw [hv8]; exact hmin z
  have hf := SevenCliqueEightComponent.small_component_free G hG v hv8 hm C (by omega)
  have he := SevenCliqueEightExact.component_edges G hG v hv8 hm (hcn v) C hsize
  have hcard : Fintype.card (T : Set V) = 8 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hsize
  have hcomp := CliqueSixExtremalLocal.five_complement H hf hcard he u hu
  have hJcard : Fintype.card (H.neighborSet u) = 5 := by rw [H.card_neighborSet_eq_degree,hu]
  change Jᶜ.edgeFinset.card = 2
  apply CliqueFiveMissingMatching.two_edges J hJcard hcomp
  intro Q hQ hclQ
  let f : H.neighborSet u → V := fun w => w.val.val
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  let P := Q.image f
  have hP : P.card = 4 := by rw [Finset.card_image_of_injective _ hinj,hQ]
  have hsub : P ⊆ G.neighborFinset u.val := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact (G.mem_neighborFinset u.val (f w)).mpr w.property
  have hclP : G.IsClique (P : Set V) := by
    intro a ha b hb hab
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    exact hclQ hx hy (fun hh => hab (congrArg f hh))
  have hu8 := SevenCliqueEightRegular.component_regular G hG v hv8 hm (hcn v) C hsize u.val u.property
  exact SevenCliqueTwentySixNeighborhood.no_four_clique G hG u.val hu8
    (fun z => by rw [hu8]; exact hmin z) (hcn u.val) (by rw [hu8,horder]; decide)
    hsep horder P hP hsub hclP
theorem exists_pattern (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8)
 :
    let H := G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)
    ∃ u, H.degree u = 5 ∧ ((H.induce (H.neighborSet u))ᶜ).edgeFinset.card = 2 := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  let H := G.induce (T : Set V)
  have hcard : Fintype.card (T : Set V) = 8 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hsize
  letI : Nonempty (T : Set V) := Fintype.card_pos_iff.mp (by omega)
  have hlow : 5 ≤ H.minDegree := H.le_minDegree_of_forall_le_degree 5 (by
    intro x
    rw [InducedCounting.degree_induce_eq_inducedDegree G T x]
    exact SevenCliqueTwentySixInterior.five_le G hG horder hmin hcn hsep v hv8 C hsize x.val x.property)
  obtain ⟨u,hu⟩ := H.exists_minimal_degree_vertex
  have he := SevenCliqueEightExact.component_edges G hG v hv8
    (fun z => by rw [hv8]; exact hmin z) (hcn v) C hsize
  have hs := H.minDegree_mul_card_le_two_mul_card_edges
  change H.edgeFinset.card = 22 at he
  rw [hcard,he] at hs
  have hu5 : H.degree u = 5 := by omega
  exact ⟨u,hu5,matching G hG horder hmin hcn hsep v hv8 C hsize u hu5⟩

end Paper.SevenCliqueTwentySixFivePattern

