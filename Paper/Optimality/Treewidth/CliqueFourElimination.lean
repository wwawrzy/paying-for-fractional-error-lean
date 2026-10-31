import Paper.Optimality.Treewidth.CliqueFourConnectivity
import Paper.Optimality.Treewidth.CliqueFourSeparation
import Paper.Optimality.Treewidth.TreewidthDensity

/-! Actual elimination in K4-minor-free graphs. A clique may be reserved;
the eliminated vertex lies outside it. Minimum separators have size at most
two, their filled sides are proved minors, and private degrees are preserved. -/
namespace Paper.CliqueFourElimination

open SimpleGraph PlaneTopology.WagnerSeparation CliqueFourSeparation

theorem avoiding_clique {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : G.IsKMinorFree 4)
    (K : Finset V) (hK : G.IsClique (K : Set V)) (hout : ∃ v, v ∉ K) :
    ∃ v, v ∉ K ∧ G.degree v ≤ 2 := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Fintype.card W = n →
      H.IsKMinorFree 4 → ∀ K : Finset W, H.IsClique (K : Set W) →
      (∃ v, v ∉ K) → ∃ v, v ∉ K ∧ H.degree v ≤ 2 by
    exact hh _ V G rfl hfree K hK hout
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H _ hcard hfree K hK hout
    by_cases hsmall : Fintype.card W ≤ 3
    · obtain ⟨v, hv⟩ := hout
      exact ⟨v, hv, by have hd := H.degree_lt_card_verts v; omega⟩
    obtain ⟨S, hS, hconn, ⟨s⟩⟩ := exists_minimum_small_separation H
      (by omega) (CliqueFourConnectivity.not_three_connected H hfree)
    obtain ⟨q, havoid⟩ := choose_side H s K hK
    let A := q.left
    let F := fill H A S
    have hminor : F.IsMinor H := fill_minor H S hS hconn q
    have hFfree : F.IsKMinorFree 4 := IsHMinorFree.minor hfree hminor
    have hsmaller : Fintype.card A < n := by
      have hh := Separation.card_left_lt H q
      simpa only [Nat.card_eq_fintype_card, hcard] using hh
    have houtF : ∃ v : A, v ∉ boundary A S := by
      obtain ⟨v, hvA, hvR⟩ := q.left_private
      refine ⟨⟨v, hvA⟩, ?_⟩
      intro hvb
      have hvS : v ∈ S := (Finset.mem_filter.mp hvb).2
      have hvboth : v ∈ q.left ∩ q.right := by rw [q.overlap]; exact hvS
      exact hvR hvboth.2
    obtain ⟨v, hvb, hvdeg⟩ := ih _ hsmaller A F rfl hFfree (boundary A S)
      (boundary_clique H A S) houtF
    have hvS : v.val ∉ S := by
      intro hvS
      exact hvb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS⟩)
    have hvR : v.val ∉ q.right := by
      intro hvR
      apply hvS
      have hvboth : v.val ∈ q.left ∩ q.right := ⟨v.property, hvR⟩
      rwa [q.overlap] at hvboth
    refine ⟨v.val, havoid v.val ⟨v.property, hvR⟩, ?_⟩
    exact (degree_preserved H q v hvS) ▸ hvdeg

theorem low_degree {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : G.IsKMinorFree 4) :
    ∃ v, G.degree v ≤ 2 := by
  classical
  obtain ⟨v, _, hv⟩ := avoiding_clique G hfree ∅ (by simp)
    ⟨Classical.arbitrary V, Finset.notMem_empty _⟩
  exact ⟨v, hv⟩

theorem degeneracy {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : G.IsKMinorFree 4) :
    G.IsKDegenerate 2 := by
  classical
  intro S hS
  letI : Nonempty ↥(S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hminor : (G.induce (S : Set V)).IsMinor G := IsMinor.of_induce G _
  obtain ⟨v, hv⟩ := low_degree (G.induce (S : Set V)) (IsHMinorFree.minor hfree hminor)
  exact ⟨v.val, v.property, (TreewidthDensity.induced_degree G S v) ▸ hv⟩

end Paper.CliqueFourElimination

#print axioms Paper.CliqueFourElimination.avoiding_clique
#print axioms Paper.CliqueFourElimination.low_degree
#print axioms Paper.CliqueFourElimination.degeneracy
