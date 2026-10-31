import GraphTheory.SimpleGraph.Minor.Defs
import GraphTheory.SimpleGraph.Degeneracy

/-! Small near-complete separators. On at most five vertices, at most one
missing neighbor per vertex leaves at most two missing unordered edges.
The proof counts actual degrees and uses the handshaking identity. -/
namespace Paper.CliqueMissingEdges

open SimpleGraph

private theorem numeric (n e : ℕ) (hn : n ≤ 5) (h : n * (n - 2) ≤ 2 * e) :
    n.choose 2 ≤ e + 2 := by
  interval_cases n <;> norm_num [Nat.choose] at * <;> omega

theorem two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V ≤ 5)
    (hdegree : ∀ v, Fintype.card V - 2 ≤ G.degree v) :
    (Fintype.card V).choose 2 ≤ G.edgeFinset.card + 2 := by
  classical
  have hh : (∑ _v : V, (Fintype.card V - 2)) ≤ ∑ v : V, G.degree v :=
    Finset.sum_le_sum (fun v _ => hdegree v)
  rw [G.sum_degrees_eq_twice_card_edges] at hh
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh
  exact numeric _ _ hV hh

theorem degree_lower {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u : V)
    (hunique : ∀ a ∈ S, a ≠ u → ¬G.Adj u a →
      ∀ b ∈ S, b ≠ u → ¬G.Adj u b → a = b) :
    S.card - 2 ≤ G.inducedDegree u S := by
  classical
  let M := (S.erase u).filter (fun a => ¬G.Adj u a)
  have hM : M.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, hna⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hnb⟩ := Finset.mem_filter.mp hb
    obtain ⟨hau, haS⟩ := Finset.mem_erase.mp ha
    obtain ⟨hbu, hbS⟩ := Finset.mem_erase.mp hb
    exact hunique a haS hau hna b hbS hbu hnb
  have hsub : S.filter (fun a => ¬G.Adj u a) ⊆ insert u M := by
    intro a ha
    obtain ⟨haS, hna⟩ := Finset.mem_filter.mp ha
    by_cases hau : a = u
    · exact Finset.mem_insert.mpr (Or.inl hau)
    · exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hau, haS⟩, hna⟩))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hpartition := Finset.card_filter_add_card_filter_not (s := S) (G.Adj u)
  change S.card - 2 ≤ (S.filter (G.Adj u)).card
  omega

end Paper.CliqueMissingEdges

#print axioms Paper.CliqueMissingEdges.two
#print axioms Paper.CliqueMissingEdges.degree_lower
