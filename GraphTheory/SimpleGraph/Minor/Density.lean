/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Minor.Defs
import GraphTheory.SimpleGraph.Degeneracy
import GraphTheory.SimpleGraph.Minor.AverageDegree
import Mathlib.Tactic

/-!
# Edge-density bounds for `Kₜ`-minor-free graphs (Mader's theorem, Diestel §7.2)

Linear edge bounds (Mader, 1967) for graphs that exclude a fixed complete minor.
For every `h ≥ 1` there exists a constant `c(h)` such that every `K_h`-minor-free
graph `G` satisfies `|E(G)| ≤ c(h) · |V(G)|`. We use the explicit constant
`c(h) = 2^(h-2)` coming from Diestel Proposition 7.2.3.


Source: `MdsLean/MdsLean/Mader.lean`. The file `MdsLean/MdsLean/MinorFreeDensity.lean`
contains related material that may be merged here in a future KID.

Mathlib currently has no upstream notion of Mader's constant nor of edge-density
bounds for minor-free graph classes; this file fills that gap and is intended
for upstream promotion.

## Main definitions

* `SimpleGraph.maderConst` — the Mader constant `c(h) = 2^(h-2)`.

## Main results

* `SimpleGraph.IsKMinorFree.edgeFinset_card_le` — Mader's theorem
  (Diestel Thm 7.2.1): `|E(G)| ≤ maderConst h · |V(G)|` for `K_h`-minor-free `G`.
* `SimpleGraph.induce_isMinor` — an induced subgraph is a minor.
* `SimpleGraph.IsKMinorFree.hasEdgeDensityBound` — edge-density corollary
  expressed via `HasEdgeDensityBound`.
* `SimpleGraph.IsKMinorFree.two_mul_edgeFinset_card_le` — degree-sum corollary.
* `SimpleGraph.IsKMinorFree.isKDegenerate` — degeneracy corollary
  (every `K_h`-minor-free graph is `(2 · maderConst h)`-degenerate).
* `SimpleGraph.IsKMinorFree.degeneracy_le` — degeneracy bound.

## Implementation notes

The proof of Mader's theorem proceeds by contrapositive of Diestel
Proposition 7.2.3: a graph with sufficiently high average degree contains
a `K_h` minor. Edge cases (`h < 2` or empty vertex set) are handled separately;
notably, for `h = 0` and `h = 1` the assumption `IsKMinorFree h` is vacuous
on nonempty graphs and yields a contradiction directly.

## References

* Diestel, *Graph Theory*, 5th ed., Theorem 7.2.1.
* Mader, W. (1967). *Homomorphieeigenschaften und mittlere Kantendichte von Graphen.*
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Mader's constant -/

/-- **Mader's constant**: for `K_h`-minor-free graphs, `|E| ≤ maderConst h · |V|`.

We define `maderConst h = 2^(h-2)` (with natural subtraction, so
`maderConst 0 = maderConst 1 = 1`). This follows from Diestel Proposition 7.2.3:
if `d(G) ≥ 2^(h-2)` then `G` has a `K_h` minor. The contrapositive gives
`|E| < 2^(h-2) · |V|` for `K_h`-minor-free graphs. -/
def maderConst (h : ℕ) : ℕ := 2 ^ (h - 2)

/-! ## Mader's theorem -/

/-- **Mader's theorem** (Diestel Thm 7.2.1): every `K_h`-minor-free graph satisfies
`|E(G)| ≤ maderConst h · |V(G)|`.

**Proof.** From Diestel Prop 7.2.3 (contrapositive): if `G` is `K_h`-minor-free
and `h ≥ 2`, then `2|E| < 2^(h-2) · |V|`, so `|E| < 2^(h-2) · |V| = maderConst h · |V|`.
Edge cases (`h < 2` or `|V| = 0`) are handled separately. -/
theorem IsKMinorFree.edgeFinset_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {h : ℕ} (hfree : G.IsKMinorFree h) :
    G.edgeFinset.card ≤ maderConst h * Fintype.card V := by
  unfold maderConst
  by_cases hV : Fintype.card V = 0
  · -- |V| = 0 implies |E| = 0
    have hEmpty : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have hcard : G.edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero]
      ext e
      constructor <;> intro h <;> simp_all
    simp [hcard, hV]
  · -- |V| > 0
    have hVpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
    by_cases hh : 2 ≤ h
    · -- Main case: h ≥ 2, |V| > 0
      have hlt := hfree.two_mul_edges_lt G h hh hVpos
      -- 2 * |E| < 2^(h-2) * |V|, so |E| ≤ 2 * |E| < 2^(h-2) * |V|
      have hle : G.edgeFinset.card ≤ 2 * G.edgeFinset.card := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · -- h < 2: h = 0 or h = 1. In both cases IsKMinorFree h is False when |V| > 0.
      push_neg at hh
      interval_cases h <;> simp_all only [zero_tsub, pow_zero, one_mul,
        Nat.one_le_ofNat, Nat.sub_eq_zero_of_le] <;> exfalso <;> apply hfree
      · -- h = 0: K_0 on Fin 0 is trivially a minor (empty branch set function)
        exact ⟨{ branchSet := Fin.elim0, nonempty := fun v => v.elim0,
                  disjoint := fun v => v.elim0, connected := fun v => v.elim0,
                  adjacent := fun v => v.elim0 }⟩
      · -- h = 1: K_1 minor exists when |V| > 0 (singleton branch set)
        have ⟨v⟩ := Fintype.card_pos_iff.mp hVpos
        refine ⟨{ branchSet := fun _ => {v},
                   nonempty := fun _ => ⟨v, rfl⟩,
                   disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij,
                   connected := fun _ => ?_,
                   adjacent := fun i j hij => absurd (Subsingleton.elim i j) hij.ne }⟩
        haveI : Nonempty ({v} : Set V) := ⟨⟨v, rfl⟩⟩
        haveI : Subsingleton ({v} : Set V) := Unique.instSubsingleton
        exact Connected.of_subsingleton

/-! ## Helper: induced subgraph is a minor -/

omit [Fintype V] [DecidableEq V] in
/-- An induced subgraph `G.induce s` is a minor of `G`. The branch sets are singletons:
each vertex `v : s` maps to `{v.val}`. -/
theorem induce_isMinor (G : SimpleGraph V) (s : Set V) : IsMinor (G.induce s) G := by
  constructor
  refine {
    branchSet := fun v => {v.val}
    nonempty := fun v => Set.singleton_nonempty v.val
    disjoint := fun v1 v2 hne => by
      simp only [Set.disjoint_singleton]
      intro h
      exact hne (Subtype.val_injective h)
    connected := fun v => ?_
    adjacent := fun v1 v2 hadj =>
      Exists.intro v1.val (And.intro rfl (Exists.intro v2.val (And.intro rfl hadj)))
  }
  haveI : Nonempty ({v.val} : Set V) := (Set.singleton_nonempty v.val).to_subtype
  haveI : Subsingleton ({v.val} : Set V) := Unique.instSubsingleton
  exact Connected.of_subsingleton

/-! ## Corollary: edge density bound -/

/-- `K_h`-minor-free graphs satisfy the edge density bound with constant `maderConst h`.
This connects Mader's theorem with our degeneracy machinery.

**Proof:** for any nonempty `s`, the induced subgraph `G[s]` is also `K_h`-minor-free
(since minor-freeness passes to subgraphs via `induce_isMinor` and `IsHMinorFree.minor`).
By Mader's theorem applied to `G[s]`, we get `|E(G[s])| ≤ c(h) · |V(G[s])| = c(h) · |s|`. -/
theorem IsKMinorFree.hasEdgeDensityBound (G : SimpleGraph V) [DecidableRel G.Adj]
    {h : ℕ} (hfree : G.IsKMinorFree h) :
    G.HasEdgeDensityBound (maderConst h) := by
  intro s hs
  unfold inducedEdgeCount
  have hfree_sub : (G.induce (s : Set V)).IsKMinorFree h :=
    IsHMinorFree.minor hfree (induce_isMinor G s)
  have hle := hfree_sub.edgeFinset_card_le (G.induce (s : Set V))
  have hcard : Fintype.card (s : Set V) = s.card := by simp
  rw [hcard] at hle
  exact hle

/-! ## Corollary: average degree bound -/

/-- **Corollary of Mader's theorem**: `K_h`-minor-free implies average degree `≤ 2·c(h)`.

From `|E| ≤ c(h)·|V|` and `2|E| = Σ deg(v)`, the average degree is at most `2·c(h)`. -/
theorem IsKMinorFree.two_mul_edgeFinset_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {h : ℕ} (hfree : G.IsKMinorFree h) :
    2 * G.edgeFinset.card ≤ 2 * maderConst h * Fintype.card V := by
  have h1 := hfree.edgeFinset_card_le G
  calc 2 * G.edgeFinset.card
      ≤ 2 * (maderConst h * Fintype.card V) := Nat.mul_le_mul_left 2 h1
    _ = 2 * maderConst h * Fintype.card V := by ring

/-! ## Corollary: degeneracy bound -/

/-- **Corollary of Mader's theorem**: every `K_h`-minor-free graph is
`(2 · maderConst h)`-degenerate.

Follows from the edge density bound and `isKDegenerate_of_edgeDensityBound`. -/
theorem IsKMinorFree.isKDegenerate (G : SimpleGraph V) [DecidableRel G.Adj]
    {h : ℕ} (hfree : G.IsKMinorFree h) :
    G.IsKDegenerate (2 * maderConst h) :=
  isKDegenerate_of_edgeDensityBound G (hfree.hasEdgeDensityBound G)

/-- **Corollary**: the degeneracy of a `K_h`-minor-free graph is at most `2 · maderConst h`. -/
theorem IsKMinorFree.degeneracy_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {h : ℕ} (hfree : G.IsKMinorFree h) :
    G.degeneracy ≤ 2 * maderConst h :=
  degeneracy_le_of_isKDegenerate G (hfree.isKDegenerate G)

end SimpleGraph
