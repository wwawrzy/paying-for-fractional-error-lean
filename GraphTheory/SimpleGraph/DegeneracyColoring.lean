/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib
import GraphTheory.SimpleGraph.Degeneracy

/-!
# k-Degenerate Graphs are (k+1)-Colorable (Diestel Proposition 5.2.4)

A graph `G` is **k-degenerate** if every non-empty induced subgraph has a vertex of degree
at most `k`. We prove that every k-degenerate graph is `(k+1)`-colorable.

**Proof idea (induction on |V|):**
Take a vertex `v` of degree at most `k` (exists by k-degeneracy). The graph `G - v` is still
k-degenerate. By induction, `G - v` is `(k+1)`-colorable. Since `v` has at most `k` neighbours,
there is a free color among the `k+1` colors for `v`.

## Main results

* `SimpleGraph.IsKDegenerate.colorable` — if `G` is k-degenerate, then `G.Colorable (k + 1)`.

The induced-subgraph step uses the public owner lemma
`SimpleGraph.IsKDegenerate.induce_ne` from `Degeneracy.lean`.

## References

* Diestel, *Graph Theory*, 5th ed., Proposition 5.2.4
* [B3] in project paper catalog
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Helper: a Finset of Fin (k+1) with at most k elements has a complement in univ. -/
private lemma exists_free_color (k : Nat) (s : Finset (Fin (k + 1))) (hs : s.card ≤ k) :
    (Finset.univ \ s).Nonempty := by
  rw [Finset.sdiff_nonempty]
  intro h
  have := Finset.card_le_card h
  simp [Fintype.card_fin] at this
  omega

/-- **[B3] Diestel Prop 5.2.4**: A k-degenerate graph is (k+1)-colorable.

The proof proceeds by strong induction on `|V|`. In each non-empty graph, k-degeneracy
guarantees a vertex `v` with at most `k` neighbours. Removing `v` yields a smaller
k-degenerate graph, which is `(k+1)`-colorable by the induction hypothesis. Since `v`
has at most `k` neighbours, at least one of the `k+1` colors is available for `v`. -/
theorem IsKDegenerate.colorable (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKDegenerate k) :
    G.Colorable (k + 1) := by
  -- Induction on the number of vertices
  induction h : Fintype.card V using Nat.strongRecOn generalizing V with
  | _ n ih =>
  by_cases hne : Nonempty V
  · -- Nonempty case: find a low-degree vertex v
    obtain ⟨v, _, hdeg⟩ := hG Finset.univ ⟨(Classical.arbitrary V), Finset.mem_univ _⟩
    -- Consider the induced subgraph on V \ {v}
    let G' := G.induce {w : V | w ≠ v}
    have hG' : G'.IsKDegenerate k := hG.induce_ne v
    -- The subtype has strictly fewer vertices
    have hcard : Fintype.card {w : V // w ≠ v} < n := by
      rw [← h]
      exact Fintype.card_subtype_lt (by simp : ¬(v ≠ v))
    -- By IH, G' is (k+1)-colorable
    obtain ⟨C⟩ := ih _ hcard G' hG' rfl
    -- Colors used by v's neighbors (in the subtype)
    let neighborColors : Finset (Fin (k + 1)) :=
      (Finset.univ.filter (fun w : {w : V // w ≠ v} => G.Adj v w.val)).image C
    -- v has at most k neighbors, so neighborColors has at most k elements
    have hcard_nc : neighborColors.card ≤ k := by
      calc neighborColors.card
          ≤ (Finset.univ.filter (fun w : {w : V // w ≠ v} => G.Adj v w.val)).card :=
            Finset.card_image_le
        _ ≤ (Finset.univ.filter (G.Adj v)).card := by
            apply Finset.card_le_card_of_injOn Subtype.val
            · intro w hw
              have hw' := Finset.mem_filter.mp hw
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'.2⟩
            · exact fun _ _ _ _ h => Subtype.val_injective h
        _ = G.inducedDegree v Finset.univ := rfl
        _ ≤ k := hdeg
    -- Pick a free color for v
    have hfree := exists_free_color k neighborColors hcard_nc
    let freeColor := (Finset.univ \ neighborColors).min' hfree
    have hfree_not_used : freeColor ∉ neighborColors :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ hfree)).2
    -- Build the full coloring
    refine ⟨SimpleGraph.Coloring.mk
      (fun w => if hw : w = v then freeColor else C ⟨w, hw⟩) ?_⟩
    intro a b hadj heq
    -- heq : (if ha : a = v then freeColor else C ⟨a, ha⟩) =
    --        (if hb : b = v then freeColor else C ⟨b, hb⟩)
    by_cases ha : a = v <;> by_cases hb : b = v
    · subst ha; subst hb; exact absurd hadj G.irrefl
    · subst ha
      have : C ⟨b, hb⟩ ∈ neighborColors := by
        apply Finset.mem_image.mpr
        exact ⟨⟨b, hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
      have : freeColor ≠ C ⟨b, hb⟩ := fun h => hfree_not_used (h ▸ this)
      exact this (by simp only [dif_neg hb, ne_eq] at heq; exact heq)
    · subst hb
      have : C ⟨a, ha⟩ ∈ neighborColors := by
        apply Finset.mem_image.mpr
        exact ⟨⟨a, ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.symm hadj⟩, rfl⟩
      have : freeColor ≠ C ⟨a, ha⟩ := fun h => hfree_not_used (h ▸ this)
      exact this.symm (by simp only [dif_neg ha, ne_eq] at heq; exact heq)
    · have hadj' : G'.Adj ⟨a, ha⟩ ⟨b, hb⟩ :=
        SimpleGraph.induce_adj.mpr hadj
      have hne : C ⟨a, ha⟩ ≠ C ⟨b, hb⟩ := C.valid hadj'
      exact hne (by simp only [dif_neg ha, dif_neg hb, ne_eq] at heq; exact heq)
  · -- Empty case
    rw [not_nonempty_iff] at hne
    exact Colorable.of_isEmpty (k + 1)

/-- Corollary: The chromatic number of a k-degenerate graph is at most k+1. -/
theorem IsKDegenerate.chromaticNumber_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKDegenerate k) :
    G.chromaticNumber ≤ k + 1 :=
  (hG.colorable G).chromaticNumber_le

end SimpleGraph
