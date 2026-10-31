/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic
import GraphTheory.SimpleGraph.Domination.Basic

/-!
# Lower Bounds on Dominating Set Size

We prove that if `D` is a dominating set of a finite simple graph `G`, then
|D| * (maxDegree(G) + 1) >= |V|.

The intuition is that each vertex in `D` can dominate at most `deg(v) + 1`
vertices (itself plus its neighbors), and `deg(v) <= maxDegree(G)`.

## Main definitions

* `SimpleGraph.IsDominatingSetFinset` -- a `Finset`-based dominating set predicate.
* `SimpleGraph.closedNeighborFinset` -- the closed neighborhood N[v] = {v} ∪ N(v).

## Main results

* `SimpleGraph.closedNeighborFinset_card_le` -- |N[v]| <= maxDegree(G) + 1.
* `SimpleGraph.IsDominatingSetFinset.card_mul_maxDegree_add_one_le` -- the lower bound
  Fintype.card V <= D.card * (G.maxDegree + 1).
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A `Finset` version of `IsDominatingSet`: every vertex is in `D` or adjacent
to some member of `D`. -/
def IsDominatingSetFinset (D : Finset V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

/-- A finite independent dominating set: `D` dominates `G` and its vertices
are pairwise nonadjacent. -/
def IsIndependentDominatingSetFinset (D : Finset V) : Prop :=
  G.IsDominatingSetFinset D ∧ G.IsIndepSet (D : Set V)

/-- A minimum dominating set is a dominating `Finset` whose cardinality is no
larger than that of any other dominating `Finset`. -/
def IsMinimumDominatingSetFinset (D : Finset V) : Prop :=
  G.IsDominatingSetFinset D ∧
    ∀ D' : Finset V, G.IsDominatingSetFinset D' → D.card ≤ D'.card

variable {G}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The `Finset` and `Set` versions of domination agree under coercion. -/
theorem isDominatingSetFinset_iff_coe {D : Finset V} :
    G.IsDominatingSetFinset D ↔ G.IsDominatingSet (D : Set V) := by
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The `Finset` and `Set` versions of independent domination agree under
coercion. -/
theorem isIndependentDominatingSetFinset_iff_coe {D : Finset V} :
    G.IsIndependentDominatingSetFinset D ↔
      G.IsIndependentDominatingSet (D : Set V) := by
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A finite independent dominating set is dominating. -/
theorem IsIndependentDominatingSetFinset.isDominatingSetFinset {D : Finset V}
    (hD : G.IsIndependentDominatingSetFinset D) : G.IsDominatingSetFinset D :=
  hD.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A finite independent dominating set is independent. -/
theorem IsIndependentDominatingSetFinset.isIndepSet {D : Finset V}
    (hD : G.IsIndependentDominatingSetFinset D) : G.IsIndepSet (D : Set V) :=
  hD.2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A minimum dominating set is dominating. -/
theorem IsMinimumDominatingSetFinset.isDominatingSetFinset {D : Finset V}
    (hD : G.IsMinimumDominatingSetFinset D) : G.IsDominatingSetFinset D :=
  hD.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A minimum dominating set is no larger than any dominating set. -/
theorem IsMinimumDominatingSetFinset.card_le {D D' : Finset V}
    (hD : G.IsMinimumDominatingSetFinset D) (hD' : G.IsDominatingSetFinset D') :
    D.card ≤ D'.card :=
  hD.2 D' hD'

/-- The closed neighborhood of a vertex as a `Finset`: `{v} ∪ N(v)`. -/
def closedNeighborFinset (v : V) : Finset V :=
  {v} ∪ G.neighborFinset v

theorem mem_closedNeighborFinset {v w : V} :
    w ∈ G.closedNeighborFinset v ↔ w = v ∨ G.Adj v w := by
  simp [closedNeighborFinset, SimpleGraph.mem_neighborFinset]

theorem card_closedNeighborFinset (v : V) :
    (G.closedNeighborFinset v).card = G.degree v + 1 := by
  unfold closedNeighborFinset
  rw [Finset.card_union_of_disjoint (G.singleton_disjoint_neighborFinset v)]
  simp [G.card_neighborFinset_eq_degree]
  omega

theorem closedNeighborFinset_card_le (v : V) :
    (G.closedNeighborFinset v).card ≤ G.maxDegree + 1 := by
  rw [card_closedNeighborFinset]
  exact Nat.add_le_add_right (G.degree_le_maxDegree v) 1

/-- If `D` dominates `G`, then every vertex belongs to the closed neighborhood
of some member of `D`. -/
theorem IsDominatingSetFinset.subset_biUnion_closedNeighborFinset
    {D : Finset V} (hD : G.IsDominatingSetFinset D) :
    Finset.univ ⊆ D.biUnion (fun d => G.closedNeighborFinset d) := by
  intro v _
  rw [Finset.mem_biUnion]
  rcases hD v with hv | ⟨w, hw, hadj⟩
  · exact ⟨v, hv, by rw [mem_closedNeighborFinset]; left; rfl⟩
  · exact ⟨w, hw, by rw [mem_closedNeighborFinset]; right; exact G.adj_symm hadj⟩

/-- **Dominating set lower bound**: |V| ≤ |D| * (maxDegree(G) + 1). -/
theorem IsDominatingSetFinset.card_mul_maxDegree_add_one_le
    {D : Finset V} (hD : G.IsDominatingSetFinset D) :
    Fintype.card V ≤ D.card * (G.maxDegree + 1) := by
  have h1 : Fintype.card V = Finset.univ.card := (Finset.card_univ).symm
  have h2 : Finset.univ.card ≤ (D.biUnion (fun d => G.closedNeighborFinset d)).card :=
    Finset.card_le_card hD.subset_biUnion_closedNeighborFinset
  have h3 : (D.biUnion (fun d => G.closedNeighborFinset d)).card ≤
      ∑ d ∈ D, (G.closedNeighborFinset d).card :=
    Finset.card_biUnion_le
  have h4 : ∑ d ∈ D, (G.closedNeighborFinset d).card ≤
      ∑ _d ∈ D, (G.maxDegree + 1) :=
    Finset.sum_le_sum (fun d _ => closedNeighborFinset_card_le d)
  have h5 : ∑ _d ∈ D, (G.maxDegree + 1) = D.card * (G.maxDegree + 1) := by
    simp [Finset.sum_const, smul_eq_mul]
  linarith

/-!
## Upper bound: γ(G) ≤ n/2 for graphs without isolated vertices

Ore (1962) proved that if every vertex of `G` has degree at least 1
(i.e., `G` has no isolated vertices), then `G` has a dominating set of
size at most n/2.

**Proof strategy**: We use the maximal independent set approach.
1. A maximal independent set S is a dominating set (by maximality).
2. The complement V \ S is also a dominating set when minDegree >= 1
   (every vertex in S has a neighbor, which must be outside S by independence).
3. One of |S| or |V \ S| is <= n/2.
-/

omit [Fintype V] in
/-- A maximal independent set is a dominating set. -/
private theorem maximalIndepSet_isDominatingSetFinset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hmax : Maximal G.IsIndepSet (S : Set V)) :
    G.IsDominatingSetFinset S := by
  intro v
  by_cases hv : v ∈ S
  · left; exact hv
  · right
    -- v is not in S. By maximality, inserting v breaks independence.
    -- So there exists w in S adjacent to v.
    by_contra h
    push Not at h
    -- h : for all w in S, not G.Adj v w
    -- Then S ∪ {v} would be independent, contradicting maximality.
    have hindep := hmax.prop
    have hind2 : G.IsIndepSet ((S : Set V) ∪ {v}) := by
      intro a ha b hb hab
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | rfl
      · rcases hb with hb | rfl
        · exact hindep ha hb hab
        · intro hadj; exact h a ha (G.adj_symm hadj)
      · rcases hb with hb | rfl
        · intro hadj; exact h b hb hadj
        · exact absurd rfl hab
    have hsub : (S : Set V) ⊆ (S : Set V) ∪ {v} := Set.subset_union_left
    have hle := hmax.2 hind2 hsub
    have : v ∈ (S : Set V) := hle (Set.mem_union_right _ rfl)
    exact hv (Finset.mem_coe.mp this)

/-- Every finite graph has an independent dominating set.  Take a maximum
independent set; maximality forces every outside vertex to have a neighbor in
the set. -/
theorem exists_independentDominatingSetFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : Finset V, G.IsIndependentDominatingSetFinset D := by
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  have hmax : Maximal G.IsIndepSet (S : Set V) := hS.isMaximalIndepSet S
  exact ⟨S, maximalIndepSet_isDominatingSetFinset G S hmax, hmax.prop⟩

/-- Complement of an independent set is dominating when minDegree >= 1. -/
private theorem compl_indepSet_isDominatingSetFinset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V]
    (S : Finset V)
    (hindep : G.IsIndepSet (S : Set V))
    (hmin : 1 ≤ G.minDegree) :
    G.IsDominatingSetFinset (Finset.univ \ S) := by
  intro v
  by_cases hv : v ∈ Finset.univ \ S
  · left; exact hv
  · right
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hv
    -- v ∈ S, and v has degree >= 1
    have hdeg : 0 < G.degree v :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans hmin (G.minDegree_le_degree v))
    rw [SimpleGraph.degree_pos_iff_exists_adj] at hdeg
    obtain ⟨w, hadj⟩ := hdeg
    have hw : w ∉ S := by
      intro hw
      exact hindep hv hw (G.ne_of_adj hadj) hadj
    exact ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩, hadj⟩

/-- Either S.card or (univ \ S).card is at most n/2. -/
private theorem exists_le_half_card (S : Finset V) :
    S.card ≤ Fintype.card V / 2 ∨
    (Finset.univ \ S).card ≤ Fintype.card V / 2 := by
  rw [Finset.card_univ_diff]
  omega

/-- **Ore's theorem (1962)**: If `G` has no isolated vertices (`minDegree >= 1`),
then there exists a dominating set of size at most `n/2`. -/
theorem exists_dominatingSetFinset_card_le_half
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V]
    (hmin : 1 ≤ G.minDegree) :
    ∃ D : Finset V, G.IsDominatingSetFinset D ∧ D.card ≤ Fintype.card V / 2 := by
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  have hmax : Maximal G.IsIndepSet (S : Set V) := hS.isMaximalIndepSet S
  have hdom_S := maximalIndepSet_isDominatingSetFinset G S hmax
  have hdom_Sc := compl_indepSet_isDominatingSetFinset G S hmax.prop hmin
  rcases exists_le_half_card S with h | h
  · exact ⟨S, hdom_S, h⟩
  · exact ⟨Finset.univ \ S, hdom_Sc, h⟩

end SimpleGraph
