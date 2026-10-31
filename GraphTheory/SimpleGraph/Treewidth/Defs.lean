/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Tree decompositions and treewidth

This file introduces tree decompositions of a simple graph and the derived graph
parameter `SimpleGraph.treeWidth`, following Diestel, *Graph Theory* (5th ed.), §12.3.

## Main definitions

* `SimpleGraph.TreeDecomposition G T`: a tree decomposition of `G` indexed by the tree `T`.
  It consists of a family of *bags* `bag : ι → Set V` subject to the three conditions of
  Diestel §12.3: every vertex lies in some bag, every edge has both ends in a common bag,
  and the set of nodes whose bag contains a fixed vertex is connected in `T`.
* `SimpleGraph.TreeDecomposition.IsWidthLE D k`: every bag of `D` is finite and has at most
  `k + 1` elements, i.e. the width of `D` is at most `k`.
* `SimpleGraph.TreeDecomposition.width D`: the width `⨆ t, |bag t| - 1` of a decomposition
  indexed by a finite tree.
* `SimpleGraph.treeWidth G`: the least `k` such that `G` admits a tree decomposition of
  width at most `k`.

## Main results

* `SimpleGraph.TreeDecomposition.trivial`: the one-bag decomposition, which shows that the
  set of admissible widths is never empty.
* `SimpleGraph.treeWidth_le_card_sub_one`: `treeWidth G ≤ |V| - 1`.
* `SimpleGraph.treeWidth_mono`: `treeWidth` is monotone under taking subgraphs on the same
  vertex type.
* `SimpleGraph.treeWidth_eq_zero_iff`: `treeWidth G = 0` iff `G` has no edges.
* `SimpleGraph.treeWidth_eq_zero_of_subsingleton`: empty and one-vertex graphs have
  treewidth zero.

## Implementation notes

The connectedness condition is stated by quantifying over *all* paths of `T` between two
nodes whose bags contain `x`, rather than over the unique such path. In a tree the two
formulations agree, but the present one avoids having to name the unique path and is
directly usable as a rewriting rule.

Widths are compared through the predicate `IsWidthLE` rather than through a numeric
`width`, so that no finiteness assumption on the index type is needed. The predicate
explicitly requires finite bags: this is essential because `Set.ncard` of an infinite set
is `0`. The natural-number-valued parameter `treeWidth` is restricted to finite vertex
types; an infinite-graph version would naturally take values in `WithTop ℕ` instead.

The index type of a decomposition ranges over the same universe as the vertex type. This
is harmless: the trivial decomposition uses `PUnit`, and the decompositions built below
are indexed by spanning trees on `V` itself.
-/

universe u v

namespace SimpleGraph

variable {V : Type u} {ι : Type v} {G : SimpleGraph V} {T : SimpleGraph ι}

/-- A *tree decomposition* of a graph `G` indexed by a graph `T`, which is required to be a
tree. The family `bag : ι → Set V` must cover every vertex, must contain both ends of every
edge in a common bag, and for each vertex `x` the set of nodes whose bag contains `x` must
be connected in `T` (Diestel, *Graph Theory* 5th ed., §12.3). -/
structure TreeDecomposition (G : SimpleGraph V) (T : SimpleGraph ι) where
  /-- The bag attached to a node of the decomposition tree. -/
  bag : ι → Set V
  /-- The index graph is a tree. -/
  isTree : T.IsTree
  /-- Every vertex of `G` lies in some bag. -/
  cover : ∀ x : V, ∃ t, x ∈ bag t
  /-- Both ends of every edge of `G` lie in a common bag. -/
  edge_mem : ∀ ⦃x y : V⦄, G.Adj x y → ∃ t, x ∈ bag t ∧ y ∈ bag t
  /-- The nodes whose bag contains a fixed vertex `x` form a connected subgraph of `T`:
  any path between two such nodes stays inside that set. -/
  bag_connected : ∀ (x : V) {s t : ι} (p : T.Walk s t), p.IsPath →
    x ∈ bag s → x ∈ bag t → ∀ ⦃r : ι⦄, r ∈ p.support → x ∈ bag r

namespace TreeDecomposition

/-- The width of a decomposition is at most `k`, i.e. every bag is finite and has at most
`k + 1` elements. The finiteness conjunct prevents `Set.ncard` from assigning width zero
to an infinite bag. -/
def IsWidthLE (D : G.TreeDecomposition T) (k : ℕ) : Prop :=
  ∀ t, (D.bag t).Finite ∧ (D.bag t).ncard ≤ k + 1

theorem IsWidthLE.mono {D : G.TreeDecomposition T} {k l : ℕ} (h : D.IsWidthLE k)
    (hkl : k ≤ l) : D.IsWidthLE l := fun t => ⟨(h t).1, (h t).2.trans (by omega)⟩

/-- The width of a decomposition indexed by a finite tree, namely `max_t |bag t| - 1`. -/
noncomputable def width [Fintype ι] (D : G.TreeDecomposition T) : ℕ :=
  Finset.univ.sup fun t => (D.bag t).ncard - 1

theorem isWidthLE_iff_width_le [Finite V] [Fintype ι] (D : G.TreeDecomposition T) (k : ℕ) :
    D.IsWidthLE k ↔ D.width ≤ k := by
  constructor
  · intro h
    simp only [width, Finset.sup_le_iff, Finset.mem_univ, forall_const]
    intro t
    have := (h t).2
    omega
  · intro h t
    refine ⟨Set.toFinite _, ?_⟩
    simp only [width, Finset.sup_le_iff, Finset.mem_univ, forall_const] at h
    have := h t
    rcases Nat.eq_zero_or_pos (D.bag t).ncard with h0 | h1
    · omega
    · omega

/-- Restricting a tree decomposition of `G` along a subgraph inclusion `H ≤ G`. The bags are
unchanged. -/
def mono (D : G.TreeDecomposition T) {H : SimpleGraph V} (h : H ≤ G) :
    H.TreeDecomposition T where
  bag := D.bag
  isTree := D.isTree
  cover := D.cover
  edge_mem _ _ hxy := D.edge_mem (h hxy)
  bag_connected := D.bag_connected

@[simp] theorem mono_bag (D : G.TreeDecomposition T) {H : SimpleGraph V} (h : H ≤ G) :
    (D.mono h).bag = D.bag := rfl

/-- The trivial tree decomposition: a single node whose bag is the whole vertex set. -/
def trivial (G : SimpleGraph V) : G.TreeDecomposition (⊥ : SimpleGraph PUnit.{u + 1}) where
  bag _ := Set.univ
  isTree := IsTree.of_subsingleton
  cover _ := ⟨PUnit.unit, Set.mem_univ _⟩
  edge_mem _ _ _ := ⟨PUnit.unit, Set.mem_univ _, Set.mem_univ _⟩
  bag_connected := by intros; exact Set.mem_univ _

@[simp] theorem trivial_bag (G : SimpleGraph V) (t : PUnit.{u + 1}) :
    (TreeDecomposition.trivial G).bag t = Set.univ := rfl

theorem trivial_isWidthLE [Finite V] (G : SimpleGraph V) :
    (TreeDecomposition.trivial G).IsWidthLE (Nat.card V - 1) := by
  intro t
  refine ⟨Set.toFinite _, ?_⟩
  rw [trivial_bag, Set.ncard_univ]
  have : 0 < Nat.card V ∨ Nat.card V = 0 := by omega
  omega

end TreeDecomposition

/-- The set of numbers that bound the width of some tree decomposition of `G`. -/
def widthSet [Finite V] (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ (ι : Type u) (T : SimpleGraph ι) (D : G.TreeDecomposition T), D.IsWidthLE k}

/-- The *treewidth* of `G`: the least `k` such that `G` has a tree decomposition all of
whose bags have at most `k + 1` elements. -/
noncomputable def treeWidth [Finite V] (G : SimpleGraph V) : ℕ := sInf G.widthSet

theorem widthSet_nonempty [Finite V] (G : SimpleGraph V) : G.widthSet.Nonempty :=
  ⟨Nat.card V - 1, PUnit.{u + 1}, ⊥, TreeDecomposition.trivial G,
    TreeDecomposition.trivial_isWidthLE G⟩

theorem treeWidth_le_of_isWidthLE [Finite V] {ι' : Type u} {T' : SimpleGraph ι'}
    (D : G.TreeDecomposition T') {k : ℕ} (h : D.IsWidthLE k) : G.treeWidth ≤ k :=
  Nat.sInf_le ⟨ι', T', D, h⟩

/-- Treewidth is attained: some tree decomposition of `G` has width exactly `treeWidth G`. -/
theorem exists_treeDecomposition_isWidthLE_treeWidth [Finite V] (G : SimpleGraph V) :
    ∃ (ι' : Type u) (T' : SimpleGraph ι') (D : G.TreeDecomposition T'),
      D.IsWidthLE G.treeWidth :=
  Nat.sInf_mem (G.widthSet_nonempty)

theorem treeWidth_le_card_sub_one [Finite V] (G : SimpleGraph V) :
    G.treeWidth ≤ Nat.card V - 1 :=
  treeWidth_le_of_isWidthLE _ (TreeDecomposition.trivial_isWidthLE G)

theorem treeWidth_le_card_sub_one' [Fintype V] (G : SimpleGraph V) :
    G.treeWidth ≤ Fintype.card V - 1 := by
  simpa [Nat.card_eq_fintype_card] using G.treeWidth_le_card_sub_one

/-- Treewidth is monotone under taking subgraphs on the same vertex type. -/
theorem treeWidth_mono [Finite V] {H G : SimpleGraph V} (h : H ≤ G) :
    H.treeWidth ≤ G.treeWidth := by
  obtain ⟨ι', T', D, hD⟩ := G.exists_treeDecomposition_isWidthLE_treeWidth
  exact treeWidth_le_of_isWidthLE (D.mono h) hD

/-- Every bag of a decomposition with `IsWidthLE 0` has at most one element, so a graph of
treewidth `0` has no edges. -/
theorem eq_bot_of_isWidthLE_zero [Finite V] {ι' : Type u} {T' : SimpleGraph ι'}
    (D : G.TreeDecomposition T') (h : D.IsWidthLE 0) : G = ⊥ := by
  ext x y
  simp only [bot_adj, iff_false]
  intro hxy
  obtain ⟨t, hx, hy⟩ := D.edge_mem hxy
  have hne : x ≠ y := hxy.ne
  have hsub : ({x, y} : Set V) ⊆ D.bag t := by
    intro z hz
    rcases hz with rfl | rfl <;> assumption
  have h2 : ({x, y} : Set V).ncard = 2 := Set.ncard_pair hne
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have := (h t).2
  omega

/-- The empty graph has treewidth `0`: index the decomposition by a spanning tree of the
complete graph and let every bag be a singleton. -/
theorem treeWidth_bot [Finite V] : (⊥ : SimpleGraph V).treeWidth = 0 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · -- No vertices: a single empty bag works.
    refine Nat.le_antisymm (treeWidth_le_of_isWidthLE (T' := (⊥ : SimpleGraph PUnit.{u + 1}))
      { bag := fun _ => ∅
        isTree := IsTree.of_subsingleton
        cover := fun x => (hV.false x).elim
        edge_mem := fun _ _ h => absurd h (by simp)
        bag_connected := fun x => (hV.false x).elim } ?_) (Nat.zero_le _)
    intro t
    exact ⟨Set.toFinite _, by simp⟩
  · -- Otherwise take a spanning tree of the complete graph and use singleton bags.
    obtain ⟨T', -, hT'⟩ := (connected_top (V := V)).exists_isTree_le
    refine Nat.le_antisymm (treeWidth_le_of_isWidthLE (T' := T')
      { bag := fun t => {t}
        isTree := hT'
        cover := fun x => ⟨x, rfl⟩
        edge_mem := fun _ _ h => absurd h (by simp)
        bag_connected := ?_ } ?_) (Nat.zero_le _)
    · intro x s t p hp hs ht r hr
      simp only [Set.mem_singleton_iff] at hs ht ⊢
      subst hs; subst ht
      rw [Walk.isPath_iff_eq_nil] at hp
      subst hp
      have hrx : r = x := by simpa using hr
      exact hrx.symm
    · intro t
      exact ⟨Set.toFinite _, by simp⟩

theorem treeWidth_eq_zero_iff [Finite V] (G : SimpleGraph V) : G.treeWidth = 0 ↔ G = ⊥ := by
  constructor
  · intro h
    obtain ⟨ι', T', D, hD⟩ := G.exists_treeDecomposition_isWidthLE_treeWidth
    rw [h] at hD
    exact eq_bot_of_isWidthLE_zero D hD
  · rintro rfl
    exact treeWidth_bot

/-- Every graph on an empty or one-element vertex type has treewidth zero. This records the
two degenerate cases of the definition explicitly. -/
@[simp] theorem treeWidth_eq_zero_of_subsingleton [Finite V] [Subsingleton V]
    (G : SimpleGraph V) : G.treeWidth = 0 := by
  rw [treeWidth_eq_zero_iff]
  ext x y
  simp only [bot_adj, iff_false]
  intro hxy
  exact hxy.ne (Subsingleton.elim x y)

end SimpleGraph
