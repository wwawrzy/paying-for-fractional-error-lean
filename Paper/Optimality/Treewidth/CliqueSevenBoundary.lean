import Paper.Optimality.Treewidth.TreewidthDensity
import Paper.Optimality.Treewidth.CliqueMissingEdges

/-! Boundaries in a seven-vertex four-regular neighborhood. A subset with
at most one missing neighbor at each vertex has at most five vertices.
This uses actual induced degrees and closure of a full-degree subset. -/
namespace Paper.CliqueSevenBoundary

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem closed (S : Finset V) (x : V) (hdeg : G.degree x ≤ G.inducedDegree x S) :
    G.neighborSet x ⊆ (S : Set V) := by
  classical
  have hsub : S.filter (G.Adj x) ⊆ G.neighborFinset x := by
    intro w hw
    exact (G.mem_neighborFinset x w).mpr (Finset.mem_filter.mp hw).2
  have hcard : (G.neighborFinset x).card ≤ (S.filter (G.Adj x)).card := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro y hy
  have hh : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hy
  rw [← heq] at hh
  exact (Finset.mem_filter.mp hh).1

theorem card_le_five (hcard : Fintype.card V = 7) (hregular : ∀ v, G.degree v = 4)
    (S : Finset V) (hdegree : ∀ x ∈ S, S.card - 2 ≤ G.inducedDegree x S) : S.card ≤ 5 := by
  classical
  have hupper : S.card ≤ 7 := by simpa only [hcard] using Finset.card_le_univ S
  by_contra hn
  have hlarge : 6 ≤ S.card := by omega
  have hall : ∀ x ∈ S, G.neighborSet x ⊆ (S : Set V) := by
    intro x hx
    apply closed G S x
    have hh := hdegree x hx
    rw [hregular]
    omega
  by_cases hfull : S = Finset.univ
  · have hsize : S.card = 7 := by rw [hfull, Finset.card_univ, hcard]
    letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let x : V := Classical.arbitrary V
    have hh := hdegree x (by rw [hfull]; exact Finset.mem_univ _)
    have heq : G.inducedDegree x S = G.degree x := by
      rw [hfull]
      change (Finset.univ.filter (G.Adj x)).card = (G.neighborFinset x).card
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, G.mem_neighborFinset]
    rw [heq, hregular, hsize] at hh
    omega
  · have hsize : S.card = 6 := by
      have hstrict : S.card < Fintype.card V := Finset.card_lt_card
        (Finset.ssubset_univ_iff.mpr hfull)
      omega
    have hz : ∃ z, z ∉ S := by
      by_contra hh
      push_neg at hh
      exact hfull (Finset.eq_univ_iff_forall.mpr hh)
    obtain ⟨z, hz⟩ := hz
    have hsub : G.neighborFinset z ⊆ Finset.univ \ S := by
      intro w hw
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hwS
      exact hz (hall w hwS ((G.mem_neighborFinset z w).mp hw).symm)
    have hh := Finset.card_le_card hsub
    have hSsub : S ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
    rw [G.card_neighborFinset_eq_degree, hregular, Finset.card_sdiff_of_subset hSsub,
      Finset.card_univ, hcard, hsize] at hh
    omega

theorem closed_relative (N S : Finset V) (hSN : S ⊆ N) (x : V)
    (hdeg : G.inducedDegree x N ≤ G.inducedDegree x S) :
    ∀ y ∈ N, G.Adj x y → y ∈ S := by
  classical
  have hsub : S.filter (G.Adj x) ⊆ N.filter (G.Adj x) := by
    intro y hy
    obtain ⟨hyS, hxy⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hSN hyS, hxy⟩
  have hcard : (N.filter (G.Adj x)).card ≤ (S.filter (G.Adj x)).card := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro y hyN hxy
  have hh : y ∈ N.filter (G.Adj x) := Finset.mem_filter.mpr ⟨hyN, hxy⟩
  rw [← heq] at hh
  exact (Finset.mem_filter.mp hh).1

/-- The relative form keeps the original vertex type and an actual finite
neighborhood, avoiding any change of graph or vertex identifiers. -/
theorem within (N S : Finset V) (hN : N.card = 7) (hSN : S ⊆ N)
    (hregular : ∀ x ∈ N, G.inducedDegree x N = 4)
    (hdegree : ∀ x ∈ S, S.card - 2 ≤ G.inducedDegree x S) : S.card ≤ 5 := by
  classical
  have hupper : S.card ≤ 7 := by simpa only [hN] using Finset.card_le_card hSN
  by_contra hn
  have hlarge : 6 ≤ S.card := by omega
  have hall : ∀ x ∈ S, ∀ y ∈ N, G.Adj x y → y ∈ S := by
    intro x hx
    apply closed_relative G N S hSN x
    have hh := hdegree x hx
    rw [hregular x (hSN hx)]
    omega
  by_cases hfull : S = N
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < N.card by omega)
    have hxS : x ∈ S := by rw [hfull]; exact hx
    have hh := hdegree x hxS
    rw [hfull, hN, hregular x hx] at hh
    omega
  · have hproper : S ⊂ N := Finset.ssubset_iff_subset_ne.mpr ⟨hSN, hfull⟩
    have hstrict := Finset.card_lt_card hproper
    have hsize : S.card = 6 := by omega
    have hdiff : (N \ S).card = 1 := by
      rw [Finset.card_sdiff_of_subset hSN, hN, hsize]
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (N \ S).card by omega)
    obtain ⟨hzN, hzS⟩ := Finset.mem_sdiff.mp hz
    have hsub : N.filter (G.Adj z) ⊆ N \ S := by
      intro w hw
      obtain ⟨hwN, hzw⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_sdiff.mpr ⟨hwN, fun hwS => hzS (hall w hwS z hzN hzw.symm)⟩
    have hh := Finset.card_le_card hsub
    change G.inducedDegree z N ≤ (N \ S).card at hh
    rw [hregular z hzN, hdiff] at hh
    omega

end Paper.CliqueSevenBoundary

#print axioms Paper.CliqueSevenBoundary.closed
#print axioms Paper.CliqueSevenBoundary.card_le_five
#print axioms Paper.CliqueSevenBoundary.closed_relative
#print axioms Paper.CliqueSevenBoundary.within
