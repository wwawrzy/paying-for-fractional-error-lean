import Paper.Optimality.Treewidth.CliqueMinorMinimal
import Paper.Optimality.Treewidth.CliqueSeparationCount
import Paper.Optimality.Treewidth.CliqueFourSeparation

/-! A global structural consequence of affine minimality. A minimal
counterexample at the K6 threshold has no clique separator. The exact
separator accounting and the actual induced minors are both explicit. -/
namespace Paper.CliqueMinimalSeparation

open SimpleGraph PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem left_floor {S : Finset V} (s : Separation G S) [Fintype s.left]
    (hd : ∀ v, 4 ≤ G.degree v) : 4 ≤ Fintype.card s.left := by
  classical
  obtain ⟨v, hvL, hvR⟩ := s.left_private
  have hvS : v ∉ S := by
    intro h
    have hh : v ∈ s.left ∩ s.right := by rw [s.overlap]; exact h
    exact hvR hh.2
  let w : s.left := ⟨v, hvL⟩
  have he := CliqueFourSeparation.degree_preserved G s w hvS
  have hh := (CliqueFourSeparation.fill G s.left S).degree_lt_card_verts w
  have hvd := hd v
  dsimp only [w] at he hh
  omega

theorem clique_edges (S : Finset V) [Fintype (S : Set V)]
    (hS : G.IsClique (S : Set V)) :
    (G.induce (S : Set V)).edgeFinset.card = S.card.choose 2 := by
  classical
  have heq : G.induce (S : Set V) = ⊤ := by
    ext a b
    constructor
    · intro hab
      intro hh
      subst b
      exact G.loopless.irrefl a.val hab
    · intro hab
      exact hS a.property b.property (fun hh => hab (Subtype.ext hh))
  have e : G.induce (S : Set V) ≃g (⊤ : SimpleGraph (S : Set V)) := by
    rw [heq]
  have hcard : Fintype.card (S : Set V) = S.card := by
    simp only [Fintype.card_eq_nat_card, Finset.coe_sort_coe, Nat.card_eq_finsetCard]
  calc
    _ = (⊤ : SimpleGraph (S : Set V)).edgeFinset.card := e.card_edgeFinset_eq
    _ = _ := by rw [card_edgeFinset_top_eq_card_choose_two, hcard]

theorem choose_bound (s : ℕ) : 4 * s ≤ s.choose 2 + 10 := by
  have hlarge : ∀ m : ℕ, 4 * (m + 4) ≤ (m + 4).choose 2 + 10 := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      have hc : (m + 4 + 1).choose 2 = m + 4 + (m + 4).choose 2 := by
        simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (m + 4) 1
      have he : m + 1 + 4 = m + 4 + 1 := by omega
      rw [he, hc]
      omega
  by_cases hs : s < 4
  · interval_cases s <;> decide
  · have he : s - 4 + 4 = s := by omega
    simpa only [he] using hlarge (s - 4)

theorem no_clique_separator
    (he : G.edgeFinset.card + 9 = 4 * Fintype.card V)
    (hd : ∀ v, 4 ≤ G.degree v)
    (hminimal : CliqueMinorMinimal.BelowThreshold G 4 9 4)
    (S : Finset V) (hS : G.IsClique (S : Set V)) :
    IsEmpty (Separation G S) := by
  classical
  refine ⟨fun s => ?_⟩
  letI : Fintype s.left := Fintype.ofFinite _
  letI : Fintype s.right := Fintype.ofFinite _
  letI : Fintype (S : Set V) := Fintype.ofFinite _
  have hL := hminimal s.left (G.induce s.left) (IsMinor.of_induce G _)
    (left_floor G s hd) (by
      simpa only [Nat.card_eq_fintype_card] using Separation.card_left_lt G s)
  have hRfloor : 4 ≤ Fintype.card s.right := by
    have hh := left_floor G (CliqueFourSeparation.flip G s) hd
    simpa only [Fintype.card_eq_nat_card] using hh
  have hR := hminimal s.right (G.induce s.right) (IsMinor.of_induce G _)
    hRfloor (by
      simpa only [Nat.card_eq_fintype_card] using Separation.card_right_lt G s)
  have hsum := CliqueSeparationCount.edge_sum G s
  have hvertices := CliqueSeparationCount.vertex_sum G s
  rw [clique_edges G S hS] at hsum
  have hb := choose_bound S.card
  omega

end Paper.CliqueMinimalSeparation

#print axioms Paper.CliqueMinimalSeparation.left_floor
#print axioms Paper.CliqueMinimalSeparation.clique_edges
#print axioms Paper.CliqueMinimalSeparation.choose_bound
#print axioms Paper.CliqueMinimalSeparation.no_clique_separator
