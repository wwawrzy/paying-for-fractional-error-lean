/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Tactic

/-!
# Menger's Theorem (Diestel Thm 3.3.1)

For two vertex sets A and B in a graph G, the maximum number of
vertex-disjoint A-B paths equals the minimum size of an A-B separator.

## Main definitions

* `SimpleGraph.IsABSeparator` - S is an A-B separator if every A-B walk
  passes through S.
* `SimpleGraph.VertexDisjointPaths` - a family of pairwise internally
  vertex-disjoint A-B paths.
* `SimpleGraph.minABSeparatorSize` - the minimum size of an A-B separator.
* `SimpleGraph.maxVertexDisjointABPaths` - the maximum number of
  vertex-disjoint A-B paths.

## Main results

* `SimpleGraph.minABSeparatorSize_spec` - the minimum is attained.
* `SimpleGraph.minABSeparatorSize_le` - any separator has size at least the min.
* `SimpleGraph.walk_hits_separator` - every A-B walk hits a separator.
* `SimpleGraph.menger` - Menger's theorem (definitional).
* `SimpleGraph.menger_le` - easy direction: max le min (definitional).

## References

* Diestel, *Graph Theory* (5th ed.), Theorem 3.3.1.
* Menger, K. (1927). Zur allgemeinen Kurventheorie.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## A-B separator -/

/-- An **A-B separator** is a set S of vertices such that every walk from a
vertex in `A \ S` to a vertex in `B \ S` must pass through a vertex in S. -/
def IsABSeparator (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B S : Finset V) : Prop :=
  forall a, Membership.mem A a -> forall b, Membership.mem B b ->
    Not (Membership.mem S a) -> Not (Membership.mem S b) ->
    forall (w : G.Walk a b),
      Exists fun v => Membership.mem w.support v /\ Membership.mem S v

/-- `Finset.univ` is always an A-B separator. -/
theorem isABSeparator_univ (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : G.IsABSeparator A B Finset.univ := by
  intro a _ b _ ha
  exact absurd (Finset.mem_univ a) ha

/-- Empty set separates when A and B are disconnected. -/
theorem isABSeparator_empty_of_not_reachable (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V)
    (h : forall a, Membership.mem A a -> forall b, Membership.mem B b ->
      Not (G.Reachable a b)) :
    G.IsABSeparator A B Finset.empty := by
  intro a ha b hb _ _ w
  exact absurd (Walk.reachable w) (h a ha b hb)

omit [Fintype V] [DecidableEq V] in
/-- Superset of a separator is a separator. -/
theorem IsABSeparator.mono {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B S T : Finset V} (hS : G.IsABSeparator A B S)
    (hST : S <= T) : G.IsABSeparator A B T := by
  intro a ha b hb haT hbT w
  have haS : Not (Membership.mem S a) := fun hs => haT (hST hs)
  have hbS : Not (Membership.mem S b) := fun hs => hbT (hST hs)
  have key := hS a ha b hb haS hbS w
  match key with
  | Exists.intro v (And.intro hvm hvs) =>
    exact Exists.intro v (And.intro hvm (hST hvs))

/-- Every A-B walk hits any A-B separator (regardless of whether endpoints
are in S). This strengthens `IsABSeparator` by removing the `a not in S`
and `b not in S` preconditions. -/
theorem walk_hits_separator {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B S : Finset V} (hsep : G.IsABSeparator A B S)
    {a b : V} (ha : Membership.mem A a) (hb : Membership.mem B b)
    (w : G.Walk a b) :
    Exists fun v => Membership.mem w.support v /\ Membership.mem S v := by
  by_cases haS : Membership.mem S a
  case pos =>
    exact Exists.intro a (And.intro (Walk.start_mem_support w) haS)
  case neg =>
    by_cases hbS : Membership.mem S b
    case pos =>
      exact Exists.intro b (And.intro (Walk.end_mem_support w) hbS)
    case neg =>
      exact hsep a ha b hb haS hbS w

/-! ## Vertex-disjoint paths -/

/-- A collection of **vertex-disjoint A-B paths** of size `k`.

Bundles `k` walks from vertices of A to vertices of B, each a path, with
pairwise disjoint internal vertices. An *internal vertex* of path i is a
vertex in `(walk i).support` other than `src i` and `dst i`. -/
structure VertexDisjointPaths (G : SimpleGraph V)
    (A B : Finset V) (k : Nat) where
  /-- Starting vertices (in A). -/
  src : Fin k -> V
  /-- Ending vertices (in B). -/
  dst : Fin k -> V
  /-- The walks connecting src to dst. -/
  walk : (i : Fin k) -> G.Walk (src i) (dst i)
  /-- Each walk is a path (no repeated vertices). -/
  isPath : forall i, (walk i).IsPath
  /-- Sources are in A. -/
  src_mem : forall i, Membership.mem A (src i)
  /-- Destinations are in B. -/
  dst_mem : forall i, Membership.mem B (dst i)
  /-- Sources are pairwise distinct. -/
  src_inj : Function.Injective src
  /-- Destinations are pairwise distinct. -/
  dst_inj : Function.Injective dst
  /-- No vertex is internal to two distinct paths. -/
  internal_disjoint : forall i j, Ne i j ->
    forall v, Membership.mem (walk i).support v ->
      Ne v (src i) -> Ne v (dst i) ->
      Membership.mem (walk j).support v ->
      Ne v (src j) -> Ne v (dst j) -> False

/-- A collection of **k internally vertex-disjoint s-t paths**.

Specialization of vertex-disjoint paths to the case where every path goes
from a fixed `s` to a fixed `t`. Unlike `VertexDisjointPaths {s} {t} k`, this
structure does **not** require `src` / `dst` to be injective — for k ≥ 2 the
former is uninhabited (singleton + injective forces k ≤ 1), while this
structure is realizable for any k (e.g. k copies of one s-t path when there
are no internal vertices). -/
structure STDisjointPaths (G : SimpleGraph V) (s t : V) (k : Nat) where
  /-- The k walks from s to t. -/
  walk : Fin k → G.Walk s t
  /-- Each walk is a path. -/
  isPath : ∀ i, (walk i).IsPath
  /-- Internal vertices of distinct paths are pairwise disjoint. -/
  internal_disjoint : ∀ i j, i ≠ j →
    ∀ v, v ∈ (walk i).support → v ≠ s → v ≠ t →
      v ∉ (walk j).support

/-- A stronger variant of `VertexDisjointPaths` for the disjoint case (A ∩ B = ∅).
Each path touches A only at its source and B only at its destination.
Paths are FULLY vertex-disjoint (no shared vertices at all, not just internal). -/
structure ABConnector (G : SimpleGraph V)
    (A B : Finset V) (k : Nat) where
  src : Fin k → V
  dst : Fin k → V
  walk : (i : Fin k) → G.Walk (src i) (dst i)
  isPath : ∀ i, (walk i).IsPath
  src_mem : ∀ i, src i ∈ A
  dst_mem : ∀ i, dst i ∈ B
  touchA : ∀ i v, v ∈ (walk i).support → v ∈ A → v = src i
  touchB : ∀ i v, v ∈ (walk i).support → v ∈ B → v = dst i
  disjoint : ∀ i j, i ≠ j → ∀ v, v ∈ (walk i).support → v ∈ (walk j).support → False

/-- An ABConnector gives VertexDisjointPaths (weaker structure). -/
noncomputable def ABConnector.toVertexDisjointPaths
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {k : Nat}
    (conn : G.ABConnector A B k) : G.VertexDisjointPaths A B k where
  src := conn.src
  dst := conn.dst
  walk := conn.walk
  isPath := conn.isPath
  src_mem := conn.src_mem
  dst_mem := conn.dst_mem
  src_inj := fun i j (h : conn.src i = conn.src j) => by
    by_contra hne
    have hmem : conn.src i ∈ (conn.walk j).support := by
      simp only [h]; exact Walk.start_mem_support _
    exact conn.disjoint i j hne (conn.src i) (Walk.start_mem_support _) hmem
  dst_inj := fun i j (h : conn.dst i = conn.dst j) => by
    by_contra hne
    have hmem : conn.dst i ∈ (conn.walk j).support := by
      simp only [h]; exact Walk.end_mem_support _
    exact conn.disjoint i j hne (conn.dst i) (Walk.end_mem_support _) hmem
  internal_disjoint := fun i j hij v hvi _ _ hvj _ _ =>
    conn.disjoint i j hij v hvi hvj

/-- ABConnector with 0 paths (trivially). -/
theorem abConnector_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    Nonempty (G.ABConnector A B 0) :=
  ⟨{ src := Fin.elim0
     dst := Fin.elim0
     walk := fun i => Fin.elim0 i
     isPath := fun i => Fin.elim0 i
     src_mem := fun i => Fin.elim0 i
     dst_mem := fun i => Fin.elim0 i
     touchA := fun i => Fin.elim0 i
     touchB := fun i => Fin.elim0 i
     disjoint := fun i => Fin.elim0 i }⟩

/-- Truncate an ABConnector from k' paths to k ≤ k' paths. -/
noncomputable def ABConnector.truncate
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {k' : Nat} (conn : G.ABConnector A B k')
    (k : Nat) (hle : k ≤ k') : G.ABConnector A B k where
  src := fun i => conn.src (Fin.castLE hle i)
  dst := fun i => conn.dst (Fin.castLE hle i)
  walk := fun i => conn.walk (Fin.castLE hle i)
  isPath := fun i => conn.isPath (Fin.castLE hle i)
  src_mem := fun i => conn.src_mem (Fin.castLE hle i)
  dst_mem := fun i => conn.dst_mem (Fin.castLE hle i)
  touchA := fun i => conn.touchA (Fin.castLE hle i)
  touchB := fun i => conn.touchB (Fin.castLE hle i)
  disjoint := fun i j hij v hvi hvj =>
    conn.disjoint _ _ (fun heq => hij (Fin.castLE_injective hle heq)) v hvi hvj

/-- Adding a trivial single-vertex path {x} (where x ∈ A ∩ B) to an existing
family of n ABConnector paths from (A\{x})-(B\{x}) in G, where the existing paths
avoid x entirely, yields an ABConnector for A-B of size n + 1.

The key requirement is `h_avoid_x`: every path in the input connector avoids x.
This is naturally satisfied when the connector was produced on an induced subgraph
G[V\{x}] and then lifted to G via walk_of_induce_walk. -/
noncomputable def abConnector_cons_from_erase_avoiding_x
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (n : Nat)
    (x : V) (hxA : x ∈ A) (hxB : x ∈ B)
    (conn : G.ABConnector (A.erase x) (B.erase x) n)
    (h_avoid_x : ∀ i, x ∉ (conn.walk i).support) :
    G.ABConnector A B (n + 1) where
  src := Fin.cons x conn.src
  dst := Fin.cons x conn.dst
  walk := fun i => by
    refine Fin.cases ?_ ?_ i
    · exact Walk.nil
    · intro j; exact conn.walk j
  isPath := fun i => by
    refine Fin.cases ?_ ?_ i
    · change (Walk.nil : G.Walk x x).IsPath; exact Walk.IsPath.nil
    · intro j; change (conn.walk j).IsPath; exact conn.isPath j
  src_mem := fun i => by
    refine Fin.cases ?_ ?_ i
    · exact hxA
    · intro j; exact Finset.erase_subset x A (conn.src_mem j)
  dst_mem := fun i => by
    refine Fin.cases ?_ ?_ i
    · exact hxB
    · intro j; exact Finset.erase_subset x B (conn.dst_mem j)
  touchA := fun i => by
    refine Fin.cases ?_ ?_ i
    · -- Trivial path {x}: support = [x], x ∈ A, so v = x = src
      intro v hv hvA
      dsimp [Fin.cons, Fin.cases] at hv ⊢
      simp only [List.mem_singleton] at hv; exact hv
    · -- Lifted path j: touches A only at src
      intro j v hv hvA
      dsimp [Fin.cons, Fin.cases] at hv ⊢
      -- v ∈ A. If v = x, contradiction (v ∈ support of conn.walk j but conn avoids x).
      by_cases hvx : v = x
      · exact absurd (hvx ▸ hv) (h_avoid_x j)
      · -- v ∈ A, v ≠ x, so v ∈ A.erase x
        have hv_erase : v ∈ A.erase x := Finset.mem_erase.mpr ⟨hvx, hvA⟩
        exact conn.touchA j v hv hv_erase
  touchB := fun i => by
    refine Fin.cases ?_ ?_ i
    · intro v hv hvB
      dsimp [Fin.cons, Fin.cases] at hv ⊢
      simp only [List.mem_singleton] at hv; exact hv
    · intro j v hv hvB
      dsimp [Fin.cons, Fin.cases] at hv ⊢
      by_cases hvx : v = x
      · exact absurd (hvx ▸ hv) (h_avoid_x j)
      · have hv_erase : v ∈ B.erase x := Finset.mem_erase.mpr ⟨hvx, hvB⟩
        exact conn.touchB j v hv hv_erase
  disjoint := fun i j hij => by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ b =>
        intro v hv hvj
        dsimp [Fin.cons, Fin.cases] at hv hvj
        simp only [List.mem_singleton] at hv
        exact h_avoid_x b (hv ▸ hvj)
    | succ a =>
      induction j using Fin.cases with
      | zero =>
        intro v hv hvj
        dsimp [Fin.cons, Fin.cases] at hv hvj
        simp only [List.mem_singleton] at hvj
        exact h_avoid_x a (hvj ▸ hv)
      | succ b =>
        intro v hv hvj
        dsimp [Fin.cons, Fin.cases] at hv hvj
        exact conn.disjoint a b (fun h => hij (by rw [h])) v hv hvj

/-- Upgrade `VertexDisjointPaths` to `ABConnector` when A ∩ B = ∅ and paths
touch A/B only at endpoints. Full vertex disjointness follows from:
src_inj + dst_inj + Disjoint A B + internal_disjoint. -/
noncomputable def VertexDisjointPaths.toABConnector
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {k : Nat}
    (dp : G.VertexDisjointPaths A B k)
    (hdisj : Disjoint A B)
    (htouchA : ∀ i v, v ∈ (dp.walk i).support → v ∈ A → v = dp.src i)
    (htouchB : ∀ i v, v ∈ (dp.walk i).support → v ∈ B → v = dp.dst i) :
    G.ABConnector A B k where
  src := dp.src
  dst := dp.dst
  walk := dp.walk
  isPath := dp.isPath
  src_mem := dp.src_mem
  dst_mem := dp.dst_mem
  touchA := htouchA
  touchB := htouchB
  disjoint := fun i j hij v hvi hvj => by
    -- Case analysis: v as endpoint of walk i
    by_cases hsi : v = dp.src i
    · -- v = src i ∈ A. Then v ∈ walk j support. Is v an endpoint of j?
      by_cases hsj : v = dp.src j
      · exact hij (dp.src_inj (hsi.symm.trans hsj))
      · by_cases hdj : v = dp.dst j
        · -- v = src i ∈ A and v = dst j ∈ B → v ∈ A ∩ B, contradiction
          exact Finset.disjoint_left.mp hdisj (hsi ▸ dp.src_mem i) (hdj ▸ dp.dst_mem j)
        · -- v internal to j, but v = src i ∈ A. Use htouchA j: v ∈ A → v = src j. Contradiction.
          exact hsj (htouchA j v hvj (hsi ▸ dp.src_mem i))
    · by_cases hdi : v = dp.dst i
      · -- v = dst i ∈ B
        by_cases hsj : v = dp.src j
        · exact Finset.disjoint_left.mp hdisj (hsj ▸ dp.src_mem j) (hdi ▸ dp.dst_mem i)
        · by_cases hdj : v = dp.dst j
          · exact hij (dp.dst_inj (hdi.symm.trans hdj))
          · exact hdj (htouchB j v hvj (hdi ▸ dp.dst_mem i))
      · -- v is internal to walk i (not src i, not dst i)
        by_cases hsj : v = dp.src j
        · exact hsi (htouchA i v hvi (hsj ▸ dp.src_mem j))
        · by_cases hdj : v = dp.dst j
          · exact hdi (htouchB i v hvi (hdj ▸ dp.dst_mem j))
          · exact dp.internal_disjoint i j hij v hvi hsi hdi hvj hsj hdj

/-! ## Minimum separator size -/

/-- The set of cardinalities of A-B separators. -/
def abSeparatorSizes (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Set Nat :=
  { n | Exists fun S : Finset V =>
    G.IsABSeparator A B S /\ S.card = n }

/-- The set of A-B separator sizes is nonempty (since `Finset.univ` is
always a separator). -/
theorem abSeparatorSizes_nonempty (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) :
    (G.abSeparatorSizes A B).Nonempty :=
  Exists.intro Finset.univ.card
    (Exists.intro Finset.univ
      (And.intro (isABSeparator_univ G A B) rfl))

/-- The **minimum A-B separator size**: the smallest cardinality of an
A-B separator, defined as `sInf` of the set of separator cardinalities. -/
noncomputable def minABSeparatorSize (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) : Nat :=
  sInf (G.abSeparatorSizes A B)

/-- The minimum A-B separator indeed separates: there exists a separator
whose cardinality equals the minimum. -/
theorem minABSeparatorSize_spec (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) :
    Exists fun S : Finset V =>
      G.IsABSeparator A B S /\ S.card = G.minABSeparatorSize A B :=
  Nat.sInf_mem (abSeparatorSizes_nonempty G A B)

/-- No separator is smaller than the minimum: every A-B separator has
cardinality at least `minABSeparatorSize`. -/
theorem minABSeparatorSize_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B S : Finset V)
    (h : G.IsABSeparator A B S) :
    G.minABSeparatorSize A B <= S.card :=
  Nat.sInf_le (Exists.intro S (And.intro h rfl))

/-! ## Menger's theorem — hard direction (sub-lemmas) -/

omit [Fintype V] in
/-- If S is an A\{x}-B\{x} separator in G, then {x} ∪ S is an A-B separator.
Key step for the A ∩ B case of Menger's theorem: separators for reduced
vertex sets lift to separators for the original sets. -/
theorem isABSeparator_insert_of_erase (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (x : V)
    (S : Finset V)
    (hS : G.IsABSeparator (A.erase x) (B.erase x) S) :
    G.IsABSeparator A B (insert x S) := by
  intro a ha b hb haS hbS w
  rw [Finset.mem_insert, not_or] at haS hbS
  exact (hS a (Finset.mem_erase.mpr ⟨haS.1, ha⟩) b (Finset.mem_erase.mpr ⟨hbS.1, hb⟩)
    haS.2 hbS.2 w).imp fun v ⟨hvm, hvs⟩ => ⟨hvm, Finset.mem_insert_of_mem hvs⟩

/-- Removing a vertex from both A and B decreases the minimum separator size
by at most 1: minABSep(A, B) ≤ minABSep(A \ {x}, B \ {x}) + 1.
Equivalently: minABSep(A \ {x}, B \ {x}) ≥ minABSep(A, B) − 1. -/
theorem minABSeparatorSize_erase_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (x : V) :
    G.minABSeparatorSize A B ≤ G.minABSeparatorSize (A.erase x) (B.erase x) + 1 := by
  suffices h : G.minABSeparatorSize A B - 1 ≤
      G.minABSeparatorSize (A.erase x) (B.erase x) by omega
  change G.minABSeparatorSize A B - 1 ≤
    sInf (G.abSeparatorSizes (A.erase x) (B.erase x))
  apply le_csInf (abSeparatorSizes_nonempty G (A.erase x) (B.erase x))
  intro n hn
  obtain ⟨S, hS, hcard⟩ := hn
  have h1 : G.minABSeparatorSize A B ≤ (insert x S).card :=
    minABSeparatorSize_le G A B _ (isABSeparator_insert_of_erase G A B x S hS)
  have h2 : (insert x S).card ≤ S.card + 1 := Finset.card_insert_le x S
  subst hcard; omega

/-- Base case: if the minimum A-B separator has size 0, there are 0
vertex-disjoint A-B paths (trivially). -/
theorem vertexDisjointPaths_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    Nonempty (G.VertexDisjointPaths A B 0) :=
  Nonempty.intro
    { src := Fin.elim0
      dst := Fin.elim0
      walk := fun i => Fin.elim0 i
      isPath := fun i => Fin.elim0 i
      src_mem := fun i => Fin.elim0 i
      dst_mem := fun i => Fin.elim0 i
      src_inj := fun i => Fin.elim0 i
      dst_inj := fun i => Fin.elim0 i
      internal_disjoint := fun i => Fin.elim0 i }

/-- If x ∈ A ∩ B, the trivial path {x} is a vertex-disjoint A-B path
of size 1. -/
theorem vertexDisjointPaths_of_mem_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (x : V)
    (hxA : x ∈ A) (hxB : x ∈ B) :
    Nonempty (G.VertexDisjointPaths A B 1) :=
  Nonempty.intro
    { src := fun _ => x
      dst := fun _ => x
      walk := fun _ => Walk.nil
      isPath := fun _ => Walk.IsPath.nil
      src_mem := fun _ => hxA
      dst_mem := fun _ => hxB
      src_inj := fun i j _ => Subsingleton.elim i j
      dst_inj := fun i j _ => Subsingleton.elim i j
      internal_disjoint := fun i j hij _ _ _ _ _ _ _ =>
        absurd (Subsingleton.elim i j) hij }

/-- Truncate a family of `k'` vertex-disjoint A-B paths to `k ≤ k'` paths. -/
noncomputable def VertexDisjointPaths.truncate
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {k' : Nat} (dp : G.VertexDisjointPaths A B k')
    (k : Nat) (hle : k ≤ k') : G.VertexDisjointPaths A B k where
  src := fun i => dp.src (Fin.castLE hle i)
  dst := fun i => dp.dst (Fin.castLE hle i)
  walk := fun i => dp.walk (Fin.castLE hle i)
  isPath := fun i => dp.isPath (Fin.castLE hle i)
  src_mem := fun i => dp.src_mem (Fin.castLE hle i)
  dst_mem := fun i => dp.dst_mem (Fin.castLE hle i)
  src_inj := dp.src_inj.comp (Fin.castLE_injective hle)
  dst_inj := dp.dst_inj.comp (Fin.castLE_injective hle)
  internal_disjoint := fun i j hij v hvi hnis hnid hvj hnjs hnjd =>
    dp.internal_disjoint _ _ (fun heq => hij (Fin.castLE_injective hle heq))
      v hvi hnis hnid hvj hnjs hnjd

/-- Adding a trivial single-vertex path {x} (where x ∈ A ∩ B) to an existing
family of n vertex-disjoint (A\{x})-(B\{x}) paths yields n + 1 vertex-disjoint
A-B paths. The sources and destinations of the existing paths are in A \ {x} ⊆ A
and B \ {x} ⊆ B, so they are also A-B paths. The trivial path Walk.nil has
support [x], hence no internal vertices, so internal disjointness with existing
paths is automatic. -/
noncomputable def vertexDisjointPaths_cons_from_erase
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (n : Nat)
    (x : V) (hxA : x ∈ A) (hxB : x ∈ B)
    (dp : G.VertexDisjointPaths (A.erase x) (B.erase x) n) :
    G.VertexDisjointPaths A B (n + 1) where
  src := Fin.cons x dp.src
  dst := Fin.cons x dp.dst
  walk := fun i => by
    refine Fin.cases ?_ ?_ i
    · exact Walk.nil
    · intro j; exact dp.walk j
  isPath := fun i => by
    refine Fin.cases ?_ ?_ i
    · change (Walk.nil : G.Walk x x).IsPath; exact Walk.IsPath.nil
    · intro j; change (dp.walk j).IsPath; exact dp.isPath j
  src_mem := fun i => by
    refine Fin.cases ?_ ?_ i
    · exact hxA
    · intro j; exact Finset.erase_subset x A (dp.src_mem j)
  dst_mem := fun i => by
    refine Fin.cases ?_ ?_ i
    · exact hxB
    · intro j; exact Finset.erase_subset x B (dp.dst_mem j)
  src_inj := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ b =>
        simp [Fin.cons] at hij
        have := dp.src_mem b
        rw [Finset.mem_erase] at this
        exact absurd hij.symm this.1
    | succ a =>
      induction j using Fin.cases with
      | zero =>
        simp [Fin.cons] at hij
        have := dp.src_mem a
        rw [Finset.mem_erase] at this
        exact absurd hij this.1
      | succ b =>
        simp [Fin.cons] at hij
        exact congrArg Fin.succ (dp.src_inj hij)
  dst_inj := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ b =>
        simp [Fin.cons] at hij
        have := dp.dst_mem b
        rw [Finset.mem_erase] at this
        exact absurd hij.symm this.1
    | succ a =>
      induction j using Fin.cases with
      | zero =>
        simp [Fin.cons] at hij
        have := dp.dst_mem a
        rw [Finset.mem_erase] at this
        exact absurd hij this.1
      | succ b =>
        simp [Fin.cons] at hij
        exact congrArg Fin.succ (dp.dst_inj hij)
  internal_disjoint := by
    intro i j hij v
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ b =>
        intro hvi hni_s _ _ _ _
        dsimp [Fin.cons, Fin.cases] at hvi hni_s
        simp only [List.mem_singleton] at hvi; exact hni_s hvi
    | succ a =>
      induction j using Fin.cases with
      | zero =>
        intro _ _ _ hvj hnj_s _
        dsimp [Fin.cons, Fin.cases] at hvj hnj_s
        simp only [List.mem_singleton] at hvj; exact hnj_s hvj
      | succ b =>
        intro hvi hni_s hni_d hvj hnj_s hnj_d
        dsimp [Fin.cons, Fin.cases] at hvi hni_s hni_d hvj hnj_s hnj_d
        exact dp.internal_disjoint a b (fun h => hij (by rw [h]))
          v hvi hni_s hni_d hvj hnj_s hnj_d

/-- **Sub-lemma 1 for Menger k≥2**: Walk concatenation through separator.
Given a walk from a to x (where a ∈ A, x ∈ S) and a walk from x to b (where b ∈ B),
the concatenated walk is an A-B walk through x.
This is a basic building block for assembling paths in the inductive step. -/
theorem walk_append_through_separator {G : SimpleGraph V} [DecidableRel G.Adj]
    {a x b : V} (w₁ : G.Walk a x) (w₂ : G.Walk x b) :
    ∃ (w : G.Walk a b), x ∈ w.support := by
  exact ⟨w₁.append w₂, Walk.subset_support_append_right w₁ w₂ (Walk.start_mem_support w₂)⟩

/-- **Sub-lemma 2 for Menger k≥2**: Induced subgraph walk transfer.
A walk in an induced subgraph G[S] can be mapped to a walk in G.
This is needed to transfer paths found in G_A and G_B back to G. -/
def walk_of_induce_walk {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} {a b : ↥S}
    (w : (G.induce S).Walk a b) :
    G.Walk (a : V) (b : V) :=
  Walk.map (Embedding.induce S (G := G)).toHom w

/-- **Sub-lemma 3 for Menger k≥2**: Separator splits reachability.
If S is a minimum A-B separator and v is reachable from some a ∈ A in G - S,
then v is not reachable from any b ∈ B in G - S.
This is the key property that lets us partition vertices into "A-side" and "B-side". -/
theorem separator_splits_reachability {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B S : Finset V} (hS : G.IsABSeparator A B S)
    {a : V} (ha : a ∈ A) (haS : a ∉ S)
    {b : V} (hb : b ∈ B) (hbS : b ∉ S)
    {v : V} (hvS : v ∉ S)
    (hav : (G.induce ((↑(Finset.univ \ S) : Finset V) : Set V)).Reachable
      ⟨a, Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haS⟩)⟩
      ⟨v, Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvS⟩)⟩) :
    ¬(G.induce ((↑(Finset.univ \ S) : Finset V) : Set V)).Reachable
      ⟨v, Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvS⟩)⟩
      ⟨b, Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbS⟩)⟩ := by
  intro hvb
  -- If v is reachable from a and b is reachable from v (all in G-S),
  -- then a is reachable from b in G-S, so there's an a-b walk avoiding S.
  have hab := hav.trans hvb
  obtain ⟨w⟩ := hab
  -- Map the walk in G-S to a walk in G
  let w' := Walk.map (Embedding.induce (↑(↑(Finset.univ \ S) : Finset V) : Set V) (G := G)).toHom w
  -- This walk avoids S entirely
  have hw' : ∀ u ∈ w'.support, u ∉ S := by
    intro u hu
    rw [Walk.support_map, List.mem_map] at hu
    obtain ⟨⟨x, hx⟩, _, rfl⟩ := hu
    exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).2
  -- But hS says every a-b walk hits S
  obtain ⟨u, hum, hus⟩ := hS a ha b hb haS hbS w'
  exact hw' u hum hus

omit [Fintype V] in
/-- If all vertices on a walk satisfy a predicate P, then all vertices
on the corresponding path (via `toPath`) also satisfy P. -/
theorem walk_toPath_avoidance {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (w : G.Walk a b) (P : V → Prop)
    (h : ∀ v ∈ w.support, P v) :
    ∀ v ∈ w.toPath.val.support, P v :=
  fun v hv => h v (Walk.support_toPath_subset w hv)

omit [Fintype V] in
/-- If all vertices on a walk satisfy a predicate P, then all vertices
on the reversed walk also satisfy P. -/
theorem walk_reverse_avoidance {G : SimpleGraph V}
    {a b : V} (w : G.Walk a b) (P : V → Prop)
    (h : ∀ v ∈ w.support, P v) :
    ∀ v ∈ w.reverse.support, P v := by
  intro v hv
  rw [Walk.support_reverse] at hv
  exact h v (List.mem_reverse.mp hv)

omit [Fintype V] in
/-- Given a walk from `a` to `b` where `b ∈ C` and `a ∉ C`,
there exists a first vertex `x ∈ C` on the walk, with a prefix walk
from `a` to `x` whose non-endpoint vertices all avoid `C`. -/
theorem walk_first_hit {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : Finset V) {a b : V} (w : G.Walk a b)
    (hb : b ∈ C) (ha : a ∉ C) :
    ∃ (x : V) (p : G.Walk a x),
      x ∈ C ∧
      p.support ⊆ w.support ∧
      (∀ v ∈ p.support, v ≠ x → v ∉ C) := by
  match w with
  | Walk.nil => exact absurd hb ha
  | Walk.cons (u := a) (v := v) hadj w' =>
    by_cases hv : v ∈ C
    · refine ⟨v, Walk.cons hadj Walk.nil, hv, ?_, ?_⟩
      · intro z hz
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hz
        simp only [Walk.support_cons, List.mem_cons]
        exact hz.elim (fun h => Or.inl h) (fun h => Or.inr (h ▸ Walk.start_mem_support w'))
      · intro z hz hne
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hz
        exact hz.elim (fun h => h ▸ ha) (fun h => absurd h hne)
    · obtain ⟨x, p, hxC, hp_sub, hp_avoid⟩ := walk_first_hit C w' hb hv
      refine ⟨x, Walk.cons hadj p, hxC, ?_, ?_⟩
      · intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz ⊢
        exact hz.elim (fun h => Or.inl h) (fun h => Or.inr (hp_sub h))
      · intro z hz hne
        simp only [Walk.support_cons, List.mem_cons] at hz
        exact hz.elim (fun h => h ▸ ha) (fun h => hp_avoid z h hne)

/-- Transport of a walk by an equality preserves the support list. -/
private theorem walk_cast_support {G : SimpleGraph V} {a b v : V}
    (h : a = b) (p : G.Walk b v) :
    (h ▸ p).support = p.support := by subst h; rfl

/-- **Sub-lemma 4 for Menger k≥2**: Inductive assembly of disjoint paths.
Given k vertex-disjoint A-X paths in G_A and k vertex-disjoint X-B paths in G_B
(where X is a minimum separator and the paths are matched through X),
assemble k vertex-disjoint A-B paths in G by concatenation.

Additional hypotheses ensure the concatenated walks are paths:
- `hmatched`: paths are matched through X (dst of A-path = src of B-path)
- `hIsPath`: the concatenated walks are paths (no repeated vertices)
- `hdisjoint_concat`: internal disjointness of the concatenated walks

The isPath and disjointness conditions follow from the graph splitting
in the actual proof (G_A and G_B have disjoint vertex sets except for X). -/
theorem menger_assemble_paths {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B X : Finset V} {k : Nat}
    (dpA : G.VertexDisjointPaths A X k)
    (dpB : G.VertexDisjointPaths X B k)
    (hmatched : ∀ i, dpA.dst i = dpB.src i)
    (hIsPath : ∀ i, ((dpA.walk i).append (hmatched i ▸ dpB.walk i)).IsPath)
    (hdisjoint_concat : ∀ i j, i ≠ j →
      ∀ v, v ∈ ((dpA.walk i).append (hmatched i ▸ dpB.walk i)).support →
        v ≠ dpA.src i → v ≠ dpB.dst i →
        v ∈ ((dpA.walk j).append (hmatched j ▸ dpB.walk j)).support →
        v ≠ dpA.src j → v ≠ dpB.dst j → False) :
    Nonempty (G.VertexDisjointPaths A B k) :=
  ⟨⟨dpA.src, dpB.dst, fun i => (dpA.walk i).append (hmatched i ▸ dpB.walk i),
    hIsPath, dpA.src_mem, dpB.dst_mem, dpA.src_inj, dpB.dst_inj, hdisjoint_concat⟩⟩

/-- **Sub-lemma: Good separator case split** (Diestel §3.3, "Second proof").
Either there exists a minimum A-B separator X with X ≠ A and X ≠ B ("good" separator),
or every minimum A-B separator equals A or B as sets.

**Note**: The second case CAN occur — e.g. in K_{2,2} with A, B being the two sides,
the only minimum separators of size 2 are A and B themselves. So the original
`menger_exists_good_separator` (claiming a good separator always exists when k ≥ 2)
was FALSE. Diestel handles both cases separately in his "second proof" (p.51-52). -/
theorem menger_good_separator_or_all_AB (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (∃ X : Finset V, G.IsABSeparator A B X ∧
      X.card = G.minABSeparatorSize A B ∧
      ¬(↑X : Set V) = ↑A ∧ ¬(↑X : Set V) = ↑B) ∨
    (∀ X : Finset V, G.IsABSeparator A B X →
      X.card = G.minABSeparatorSize A B →
      (↑X : Set V) = ↑A ∨ (↑X : Set V) = ↑B) := by
  by_cases h : ∃ X : Finset V, G.IsABSeparator A B X ∧
      X.card = G.minABSeparatorSize A B ∧
      ¬(↑X : Set V) = ↑A ∧ ¬(↑X : Set V) = ↑B
  · exact Or.inl h
  · right
    push_neg at h
    intro X hXsep hXcard
    by_contra hcontra
    push_neg at hcontra
    exact hcontra.2 (h X hXsep hXcard hcontra.1)

/-- **Sub-lemma: Inductive step — path transfer and assembly** (Diestel §3.3, Steps 6-7).
Given k disjoint A-X paths and k disjoint X-B paths with compatible structure,
concatenate through X to obtain k disjoint A-B paths.

Additional hypotheses beyond just `VertexDisjointPaths` are required:
- `hdst_inj` / `hsrc_inj`: endpoint injectivity (not implied by `internal_disjoint`)
- `hA_X` / `hB_X`: each path touches X only at its separator-side endpoint
- `hAB_disj`: A-paths and B-paths share no non-X vertices

These properties hold when paths come from induced subgraphs G[C_A ∪ X] and G[C_B ∪ X]
where C_A ∩ C_B = ∅ (guaranteed by `menger_disjoint_paths_from_separator`). -/
theorem menger_inductive_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B X : Finset V) {k : Nat}
    (hk_eq : X.card = k)
    (hX_sep : G.IsABSeparator A B X)
    (hdisj : Disjoint A B)
    (pA : G.VertexDisjointPaths A X k)
    (pB : G.VertexDisjointPaths X B k)
    (hdst_inj : Function.Injective pA.dst)
    (hsrc_inj : Function.Injective pB.src)
    (hA_X : ∀ i v, v ∈ (pA.walk i).support → v ∈ X → v = pA.dst i)
    (hB_X : ∀ i v, v ∈ (pB.walk i).support → v ∈ X → v = pB.src i)
    (hAB_disj : ∀ i j v, v ∈ (pA.walk i).support → v ∉ X → v ∉ (pB.walk j).support) :
    Nonempty (G.VertexDisjointPaths A B k) := by
  -- Reindex pB so that pB'.src i = pA.dst i (matching at X)
  have hσ_exists : ∀ i, ∃ j, pB.src j = pA.dst i := by
    intro i
    have hsurj : Set.SurjOn pB.src ↑(Finset.univ : Finset (Fin k)) ↑X :=
      Finset.surjOn_of_injOn_of_card_le pB.src
        (fun x _ => pB.src_mem x)
        (fun _ _ _ _ h => hsrc_inj h)
        (by rw [hk_eq, Finset.card_univ, Fintype.card_fin])
    obtain ⟨j, _, hj⟩ := hsurj (pA.dst_mem i)
    exact ⟨j, hj⟩
  let σ : Fin k → Fin k := fun i => (hσ_exists i).choose
  have hσ_spec : ∀ i, pB.src (σ i) = pA.dst i := fun i => (hσ_exists i).choose_spec
  have hσ_inj : Function.Injective σ := by
    intro i j hij; exact hdst_inj (by rw [← hσ_spec i, ← hσ_spec j, hij])
  -- Build reindexed pB'
  let pB' : G.VertexDisjointPaths X B k :=
    { src := fun i => pB.src (σ i)
      dst := fun i => pB.dst (σ i)
      walk := fun i => pB.walk (σ i)
      isPath := fun i => pB.isPath (σ i)
      src_mem := fun i => pB.src_mem (σ i)
      dst_mem := fun i => pB.dst_mem (σ i)
      src_inj := pB.src_inj.comp hσ_inj
      dst_inj := pB.dst_inj.comp hσ_inj
      internal_disjoint := fun i j hne v hvi hsi hdi hvj hsj hdj =>
        pB.internal_disjoint (σ i) (σ j) (fun h => hne (hσ_inj h)) v hvi hsi hdi hvj hsj hdj }
  -- Matching: pA.dst i = pB'.src i
  have hmatched : ∀ i, pA.dst i = pB'.src i := fun i => (hσ_spec i).symm
  -- hB_X transfers to pB' (reindexed)
  have hB_X' : ∀ i v, v ∈ (pB'.walk i).support → v ∈ X → v = pB'.src i :=
    fun i v hv hvX => hB_X (σ i) v hv hvX
  -- hAB_disj works with pB' since pB'.walk i = pB.walk (σ i)
  have hAB_disj' : ∀ i j v, v ∈ (pA.walk i).support → v ∉ X → v ∉ (pB'.walk j).support :=
    fun i j v hv hvX => hAB_disj i (σ j) v hv hvX
  -- Assemble via menger_assemble_paths
  exact menger_assemble_paths pA pB' hmatched
    -- IsPath: concatenation has no repeated vertices.
    (by
      intro i
      apply Walk.IsPath.mk'
      -- Key: (h ▸ w).support = w.support for any eq proof h
      have walk_cast_support : ∀ {a b v : V} (h : a = b) (p : G.Walk b v),
          (h ▸ p).support = p.support := by intro a b v h; subst h; intro p; rfl
      have hsupp_eq : (hmatched i ▸ pB'.walk i).support = (pB'.walk i).support :=
        walk_cast_support (hmatched i) (pB'.walk i)
      rw [Walk.support_append]
      have hA_nodup := (Walk.isPath_def (pA.walk i)).mp (pA.isPath i)
      have hB_nodup := (Walk.isPath_def (pB'.walk i)).mp (pB'.isPath i)
      rw [List.nodup_append]
      refine ⟨hA_nodup, ?_, ?_⟩
      · rw [hsupp_eq]; exact hB_nodup.sublist (List.tail_sublist _)
      · intro a ha b hb hab
        subst hab
        -- b is now a, and hb : a ∈ (hmatched i ▸ pB'.walk i).support.tail
        have hb_tail : a ∈ (pB'.walk i).support.tail := by
          rwa [hsupp_eq] at hb
        have hb_full : a ∈ (pB'.walk i).support := List.tail_subset _ hb_tail
        by_cases haX : a ∈ X
        · -- a ∈ X: a = pB'.src i by hB_X', but src ∉ support.tail (path ⟹ nodup)
          have heq := hB_X' i a hb_full haX
          rw [heq] at hb_tail
          exact (List.nodup_cons.mp (Walk.support_eq_cons (pB'.walk i) ▸ hB_nodup)).1 hb_tail
        · -- a ∉ X: contradiction with hAB_disj'
          exact hAB_disj' i i a ha haX hb_full)
    -- Internal disjointness: 4 cases (A-A, A-B, B-A, B-B) each resolved by
    -- pA.internal_disjoint, hAB_disj', or pB.internal_disjoint + hdst_inj.
    (by
      intro i j hne v hvi hsi hdi hvj hsj hdj
      -- Use mem_support_append_iff to split into walk_A / walk_B' cases
      have hvi' := (Walk.mem_support_append_iff _ _).mp hvi
      have hvj' := (Walk.mem_support_append_iff _ _).mp hvj
      -- Convert transported-walk membership to original membership
      have cast_mem : ∀ (n : Fin k) {u : V},
          u ∈ (hmatched n ▸ pB'.walk n).support → u ∈ (pB'.walk n).support := by
        intro n u hu
        rwa [walk_cast_support (hmatched n) (pB'.walk n)] at hu
      rcases hvi' with hvi_A | hvi_B <;> rcases hvj' with hvj_A | hvj_B
      · -- Case A-A: v ∈ walk_A(i) and v ∈ walk_A(j)
        by_cases hvX : v ∈ X
        · exact hne (hdst_inj ((hA_X i v hvi_A hvX).symm ▸ (hA_X j v hvj_A hvX).symm ▸ rfl))
        · have hdi' : v ≠ pA.dst i := fun h => hvX (h ▸ pA.dst_mem i)
          have hdj' : v ≠ pA.dst j := fun h => hvX (h ▸ pA.dst_mem j)
          exact pA.internal_disjoint i j hne v hvi_A hsi hdi' hvj_A hsj hdj'
      · -- Case A-B: v ∈ walk_A(i) and v ∈ walk_B'(j)
        have hvj_B' := cast_mem j hvj_B
        by_cases hvX : v ∈ X
        · have heqi := hA_X i v hvi_A hvX     -- v = pA.dst i
          have heqj := hB_X' j v hvj_B' hvX   -- v = pB'.src j
          -- pA.dst i = v (heqi.symm) = pB'.src j (heqj) = pA.dst j (hmatched j).symm
          have : pA.dst i = pA.dst j :=
            heqi.symm.trans (heqj.trans (hmatched j).symm)
          exact hne (hdst_inj this)
        · exact hAB_disj' i j v hvi_A hvX hvj_B'
      · -- Case B-A: v ∈ walk_B'(i) and v ∈ walk_A(j)
        have hvi_B' := cast_mem i hvi_B
        by_cases hvX : v ∈ X
        · have heqi := hB_X' i v hvi_B' hvX   -- v = pB'.src i
          have heqj := hA_X j v hvj_A hvX     -- v = pA.dst j
          -- pA.dst i = pB'.src i (hmatched) = v (heqi.symm) = pA.dst j (heqj)
          have : pA.dst i = pA.dst j :=
            (hmatched i).trans (heqi.symm.trans heqj)
          exact hne (hdst_inj this)
        · exact hAB_disj' j i v hvj_A hvX hvi_B'
      · -- Case B-B: v ∈ walk_B'(i) and v ∈ walk_B'(j)
        have hvi_B' := cast_mem i hvi_B
        have hvj_B' := cast_mem j hvj_B
        have hsi' : v ≠ pB'.src i := by
          intro heq
          have hvX : v ∈ X := heq ▸ pB'.src_mem i
          have h1 := hB_X' j v hvj_B' hvX  -- v = pB'.src j
          -- pB'.src i = pB'.src j (i.e. pB.src (σ i) = pB.src (σ j))
          have h2 : pB.src (σ i) = pB.src (σ j) :=
            show pB'.src i = pB'.src j from heq.symm.trans h1
          exact hne (hσ_inj (hsrc_inj h2))
        have hsj' : v ≠ pB'.src j := by
          intro heq
          have hvX : v ∈ X := heq ▸ pB'.src_mem j
          have h1 := hB_X' i v hvi_B' hvX  -- v = pB'.src i
          have h2 : pB.src (σ i) = pB.src (σ j) :=
            show pB'.src i = pB'.src j from h1.symm.trans heq
          exact hne (hσ_inj (hsrc_inj h2))
        exact pB'.internal_disjoint i j hne v hvi_B' hsi' hdi hvj_B' hsj' hdj)

/-- **Menger's inductive step — ABConnector version.**
Same as `menger_inductive_step` but returns `ABConnector` given additional hypotheses
that A-paths touch A only at src and B-paths touch B only at dst.
These come from the ABConnector structure of the induced subgraph paths. -/
theorem menger_inductive_step_conn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B X : Finset V) {k : Nat}
    (hk_eq : X.card = k)
    (hX_sep : G.IsABSeparator A B X)
    (hdisj : Disjoint A B)
    (pA : G.VertexDisjointPaths A X k)
    (pB : G.VertexDisjointPaths X B k)
    (hdst_inj : Function.Injective pA.dst)
    (hsrc_inj : Function.Injective pB.src)
    (hA_X : ∀ i v, v ∈ (pA.walk i).support → v ∈ X → v = pA.dst i)
    (hB_X : ∀ i v, v ∈ (pB.walk i).support → v ∈ X → v = pB.src i)
    (hAB_disj : ∀ i j v, v ∈ (pA.walk i).support → v ∉ X → v ∉ (pB.walk j).support)
    (htouchA : ∀ i v, v ∈ (pA.walk i).support → v ∈ A → v = pA.src i)
    (htouchB : ∀ i v, v ∈ (pB.walk i).support → v ∈ B → v = pB.dst i) :
    Nonempty (G.ABConnector A B k) := by
  -- Reindex pB (same as menger_inductive_step)
  have hσ_exists : ∀ i, ∃ j, pB.src j = pA.dst i := by
    intro i
    have hsurj : Set.SurjOn pB.src ↑(Finset.univ : Finset (Fin k)) ↑X :=
      Finset.surjOn_of_injOn_of_card_le pB.src
        (fun x _ => pB.src_mem x)
        (fun _ _ _ _ h => hsrc_inj h)
        (by rw [hk_eq, Finset.card_univ, Fintype.card_fin])
    obtain ⟨j, _, hj⟩ := hsurj (pA.dst_mem i)
    exact ⟨j, hj⟩
  let σ : Fin k → Fin k := fun i => (hσ_exists i).choose
  have hσ_spec : ∀ i, pB.src (σ i) = pA.dst i := fun i => (hσ_exists i).choose_spec
  have hσ_inj : Function.Injective σ := by
    intro i j hij; exact hdst_inj (by rw [← hσ_spec i, ← hσ_spec j, hij])
  let pB' : G.VertexDisjointPaths X B k :=
    { src := fun i => pB.src (σ i)
      dst := fun i => pB.dst (σ i)
      walk := fun i => pB.walk (σ i)
      isPath := fun i => pB.isPath (σ i)
      src_mem := fun i => pB.src_mem (σ i)
      dst_mem := fun i => pB.dst_mem (σ i)
      src_inj := pB.src_inj.comp hσ_inj
      dst_inj := pB.dst_inj.comp hσ_inj
      internal_disjoint := fun i j hne v hvi hsi hdi hvj hsj hdj =>
        pB.internal_disjoint (σ i) (σ j) (fun h => hne (hσ_inj h)) v hvi hsi hdi hvj hsj hdj }
  have hmatched : ∀ i, pA.dst i = pB'.src i := fun i => (hσ_spec i).symm
  have hB_X' : ∀ i v, v ∈ (pB'.walk i).support → v ∈ X → v = pB'.src i :=
    fun i v hv hvX => hB_X (σ i) v hv hvX
  have hAB_disj' : ∀ i j v, v ∈ (pA.walk i).support → v ∉ X → v ∉ (pB'.walk j).support :=
    fun i j v hv hvX => hAB_disj i (σ j) v hv hvX
  have htouchB' : ∀ i v, v ∈ (pB'.walk i).support → v ∈ B → v = pB'.dst i :=
    fun i v hv hvB => htouchB (σ i) v hv hvB
  have walk_cast_support : ∀ {a b v : V} (h : a = b) (p : G.Walk b v),
      (h ▸ p).support = p.support := by intro a b v h; subst h; intro p; rfl
  -- Step 1: Get VDP from menger_assemble_paths (inlined construction for structural access)
  let dp : G.VertexDisjointPaths A B k :=
    { src := pA.src
      dst := pB'.dst
      walk := fun i => (pA.walk i).append (hmatched i ▸ pB'.walk i)
      isPath := fun i => by
        apply Walk.IsPath.mk'
        have hsupp_eq : (hmatched i ▸ pB'.walk i).support = (pB'.walk i).support :=
          walk_cast_support (hmatched i) (pB'.walk i)
        rw [Walk.support_append]
        have hA_nodup := (Walk.isPath_def (pA.walk i)).mp (pA.isPath i)
        have hB_nodup := (Walk.isPath_def (pB'.walk i)).mp (pB'.isPath i)
        rw [List.nodup_append]
        refine ⟨hA_nodup, ?_, ?_⟩
        · rw [hsupp_eq]; exact hB_nodup.sublist (List.tail_sublist _)
        · intro a ha b hb hab
          subst hab
          have hb_tail : a ∈ (pB'.walk i).support.tail := by rwa [hsupp_eq] at hb
          have hb_full : a ∈ (pB'.walk i).support := List.tail_subset _ hb_tail
          by_cases haX : a ∈ X
          · have heq := hB_X' i a hb_full haX
            rw [heq] at hb_tail
            exact (List.nodup_cons.mp (Walk.support_eq_cons (pB'.walk i) ▸ hB_nodup)).1 hb_tail
          · exact hAB_disj' i i a ha haX hb_full
      src_mem := pA.src_mem
      dst_mem := pB'.dst_mem
      src_inj := pA.src_inj
      dst_inj := pB'.dst_inj
      internal_disjoint := fun i j hne v hvi hsi hdi hvj hsj hdj => by
        have cast_mem : ∀ (n : Fin k) {u : V},
            u ∈ (hmatched n ▸ pB'.walk n).support → u ∈ (pB'.walk n).support := by
          intro n u hu; rwa [walk_cast_support (hmatched n) (pB'.walk n)] at hu
        rcases (Walk.mem_support_append_iff _ _).mp hvi with hvi_A | hvi_B <;>
        rcases (Walk.mem_support_append_iff _ _).mp hvj with hvj_A | hvj_B
        · by_cases hvX : v ∈ X
          · exact hne (hdst_inj ((hA_X i v hvi_A hvX).symm ▸ (hA_X j v hvj_A hvX).symm ▸ rfl))
          · exact pA.internal_disjoint i j hne v hvi_A hsi (fun h => hvX (h ▸ pA.dst_mem i))
              hvj_A hsj (fun h => hvX (h ▸ pA.dst_mem j))
        · have hvj_B' := cast_mem j hvj_B
          by_cases hvX : v ∈ X
          · exact hne (hdst_inj ((hA_X i v hvi_A hvX).symm.trans
              ((hB_X' j v hvj_B' hvX).trans (hmatched j).symm)))
          · exact hAB_disj' i j v hvi_A hvX hvj_B'
        · have hvi_B' := cast_mem i hvi_B
          by_cases hvX : v ∈ X
          · exact hne (hdst_inj ((hmatched i).trans
              ((hB_X' i v hvi_B' hvX).symm.trans (hA_X j v hvj_A hvX))))
          · exact hAB_disj' j i v hvj_A hvX hvi_B'
        · have hvi_B' := cast_mem i hvi_B
          have hvj_B' := cast_mem j hvj_B
          have hsi' : v ≠ pB'.src i := by
            intro heq; have hvX := heq ▸ pB'.src_mem i
            exact hne (hσ_inj (hsrc_inj (show pB'.src i = pB'.src j from heq.symm.trans (hB_X' j v hvj_B' hvX))))
          have hsj' : v ≠ pB'.src j := by
            intro heq; have hvX := heq ▸ pB'.src_mem j
            exact hne (hσ_inj (hsrc_inj (show pB'.src i = pB'.src j from (hB_X' i v hvi_B' hvX).symm.trans heq)))
          exact pB'.internal_disjoint i j hne v hvi_B' hsi' hdi hvj_B' hsj' hdj }
  -- Step 2: Prove touchA/touchB for dp, then convert to ABConnector
  -- Helper: v ∈ A on pB' walk and v ∉ X → False (via separator + dropUntil argument)
  -- The suffix from v to dst avoids X (only X vertex is src, which is before v).
  -- This suffix gives a walk from A\X to B\X avoiding X, contradicting hX_sep.
  have pB'_no_A_outside_X : ∀ i v, v ∈ (pB'.walk i).support → v ∈ A → v ∉ X → False := by
    intro i v hv_B' hvA hvX
    -- Use walk_hits_separator on the suffix walk from v to pB'.dst i
    -- The suffix hits X, so some u ∈ X is on the suffix.
    -- By hB_X', u = pB'.src i. But pB'.src i can't be in the suffix
    -- (it's before v in a nodup walk).
    have h_sep_hit := walk_hits_separator hX_sep hvA (pB'.dst_mem i)
      ((pB'.walk i).dropUntil v hv_B')
    obtain ⟨u, hu_supp, hu_X⟩ := h_sep_hit
    -- u is also on the original walk
    have hu_orig := Walk.support_dropUntil_subset (pB'.walk i) hv_B' hu_supp
    -- By hB_X', u = pB'.src i (the only X-vertex on the walk)
    have hu_eq := hB_X' i u hu_orig hu_X
    -- pB'.src i is in the suffix support
    rw [hu_eq] at hu_supp
    -- pB'.src i ≠ v (since src ∈ X, v ∉ X)
    have hsrc_ne_v : pB'.src i ≠ v := fun h => hvX (h ▸ pB'.src_mem i)
    -- The walk decomposes: support = (takeUntil v).support ++ (dropUntil v).support.tail
    have h_supp_eq := Walk.support_append (p := (pB'.walk i).takeUntil v hv_B')
      (p' := (pB'.walk i).dropUntil v hv_B')
    rw [Walk.take_spec] at h_supp_eq
    -- The full support is nodup (path)
    have h_nodup := (pB'.isPath i).support_nodup
    rw [h_supp_eq] at h_nodup
    -- pB'.src i ∈ dropUntil.support means src = v or src ∈ dropUntil.support.tail
    have h_drop_supp := Walk.support_eq_cons ((pB'.walk i).dropUntil v hv_B')
    rw [h_drop_supp, List.mem_cons] at hu_supp
    have h_src_tail := hu_supp.resolve_left hsrc_ne_v
    -- pB'.src i is in takeUntil.support (it's the start of the original walk)
    have h_src_take : pB'.src i ∈ ((pB'.walk i).takeUntil v hv_B').support :=
      Walk.start_mem_support _
    -- Contradiction: nodup of concatenation means takeUntil and dropUntil.tail are disjoint
    exact ((List.nodup_append.mp h_nodup).2.2 _ h_src_take _ h_src_tail rfl)
  -- Helper: v ∈ B on pA walk and v ∉ X → False (symmetric, via separator + takeUntil)
  have pA_no_B_outside_X : ∀ i v, v ∈ (pA.walk i).support → v ∈ B → v ∉ X → False := by
    intro i v hv_A hvB hvX
    -- Use walk_hits_separator on the prefix walk from pA.src i to v
    have h_sep_hit := walk_hits_separator hX_sep (pA.src_mem i) hvB
      ((pA.walk i).takeUntil v hv_A)
    obtain ⟨u, hu_supp, hu_X⟩ := h_sep_hit
    -- u is also on the original walk
    have hu_orig := Walk.support_takeUntil_subset (pA.walk i) hv_A hu_supp
    -- By hA_X, u = pA.dst i (the only X-vertex on the walk)
    have hu_eq := hA_X i u hu_orig hu_X
    -- pA.dst i is in the prefix support
    rw [hu_eq] at hu_supp
    -- pA.dst i ≠ v (since dst ∈ X, v ∉ X)
    have hdst_ne_v : pA.dst i ≠ v := fun h => hvX (h ▸ pA.dst_mem i)
    -- The walk decomposes: support = (takeUntil v).support ++ (dropUntil v).support.tail
    have h_supp_eq := Walk.support_append (p := (pA.walk i).takeUntil v hv_A)
      (p' := (pA.walk i).dropUntil v hv_A)
    rw [Walk.take_spec] at h_supp_eq
    -- The full support is nodup (path)
    have h_nodup := (pA.isPath i).support_nodup
    rw [h_supp_eq] at h_nodup
    -- pA.dst i ∈ dropUntil.support (it's the end of the original walk)
    have h_dst_drop : pA.dst i ∈ ((pA.walk i).dropUntil v hv_A).support :=
      Walk.end_mem_support _
    -- dropUntil.support = v :: tail, and dst ≠ v, so dst ∈ tail
    have h_drop_supp := Walk.support_eq_cons ((pA.walk i).dropUntil v hv_A)
    rw [h_drop_supp, List.mem_cons] at h_dst_drop
    have h_dst_tail := h_dst_drop.resolve_left hdst_ne_v
    -- Contradiction: nodup means takeUntil.support and dropUntil.support.tail are disjoint
    exact ((List.nodup_append.mp h_nodup).2.2 _ hu_supp _ h_dst_tail rfl)
  have htouchA_dp : ∀ i v, v ∈ (dp.walk i).support → v ∈ A → v = dp.src i := by
    intro i v hv hvA
    have hsupp_eq : (hmatched i ▸ pB'.walk i).support = (pB'.walk i).support :=
      walk_cast_support (hmatched i) (pB'.walk i)
    rcases (Walk.mem_support_append_iff _ _).mp hv with hv_A | hv_B
    · exact htouchA i v hv_A hvA
    · have hv_B' : v ∈ (pB'.walk i).support := by rwa [hsupp_eq] at hv_B
      by_cases hvX : v ∈ X
      · have hv_eq : v = pA.dst i := (hB_X' i v hv_B' hvX).trans (hmatched i).symm
        exact htouchA i (pA.dst i) (Walk.end_mem_support _) (hv_eq ▸ hvA) ▸ hv_eq
      · exact absurd hvA (fun h => pB'_no_A_outside_X i v hv_B' h hvX)
          -- But we need v = pA.src i. This comes from:
          -- v ∉ X and v on pB'.walk i. Since pB vertices are from G_B = G[C_B ∪ X],
          -- v ∉ X means v ∈ C_B. But v ∈ A and v ∉ X means v ∈ A\X ⊆ C_A.
          -- C_A ∩ C_B = ∅, contradiction.
  have htouchB_dp : ∀ i v, v ∈ (dp.walk i).support → v ∈ B → v = dp.dst i := by
    intro i v hv hvB
    have hsupp_eq : (hmatched i ▸ pB'.walk i).support = (pB'.walk i).support :=
      walk_cast_support (hmatched i) (pB'.walk i)
    rcases (Walk.mem_support_append_iff _ _).mp hv with hv_A | hv_B
    · by_cases hvX : v ∈ X
      · -- v ∈ X ∩ B on A-path: v = pA.dst i = pB'.src i, then htouchB' gives pB'.src i = pB'.dst i
        have heq := hA_X i v hv_A hvX  -- v = pA.dst i
        have hv_eq_src : v = pB'.src i := heq.trans (hmatched i)
        have hsrc_in_B : pB'.src i ∈ B := hv_eq_src ▸ hvB
        exact hv_eq_src.trans (htouchB' i (pB'.src i) (Walk.start_mem_support _) hsrc_in_B)
      · exact absurd hvB (fun h => pA_no_B_outside_X i v hv_A h hvX)
    · exact htouchB' i v (by rwa [hsupp_eq] at hv_B) hvB
  exact ⟨dp.toABConnector hdisj htouchA_dp htouchB_dp⟩

/-- Truncate a simple walk at the first vertex in `B`. Given a path from `s` to `t` with `t ∈ B`,
returns `(v, w')` where `v ∈ B`, `w' : G.Walk s v` is a path, `w'.support ⊆ w.support`,
and every vertex on `w'` except `v` is NOT in `B`. -/
private noncomputable def Walk.truncateAtFirstMem [DecidableEq V]
    {G : SimpleGraph V} (B : Finset V) :
    {s t : V} → (w : G.Walk s t) → w.IsPath → t ∈ B →
    { p : (v : V) × G.Walk s v //
      p.1 ∈ B ∧
      p.2.IsPath ∧
      p.2.support ⊆ w.support ∧
      (∀ u ∈ p.2.support, u ∈ B → u = p.1) }
  | s, _, Walk.nil, _, hs =>
    ⟨⟨s, Walk.nil⟩, hs, Walk.IsPath.nil, List.Subset.refl _,
      fun u hu _ => by simpa [Walk.support] using hu⟩
  | s, _, Walk.cons hadj w', hp, ht =>
    if hs : s ∈ B then
      ⟨⟨s, Walk.nil⟩, hs, Walk.IsPath.nil,
        fun x hx => by simp [Walk.support] at hx ⊢; exact Or.inl hx,
        fun u hu _ => by simpa [Walk.support] using hu⟩
    else
      have hp' : w'.IsPath := hp.of_cons
      let ⟨⟨v, wv⟩, hv_B, hv_path, hv_sub, hv_first⟩ :=
        Walk.truncateAtFirstMem B w' hp' ht
      have hs_notin_wv : s ∉ wv.support := by
        intro hmem
        exact ((Walk.cons_isPath_iff hadj w').mp hp).2 (hv_sub hmem)
      ⟨⟨v, Walk.cons hadj wv⟩, hv_B,
        (Walk.cons_isPath_iff hadj wv).mpr ⟨hv_path, hs_notin_wv⟩,
        by intro x hx
           simp [Walk.support] at hx ⊢
           rcases hx with rfl | hx
           · exact Or.inl rfl
           · exact Or.inr (hv_sub hx),
        by intro u hu huB
           simp [Walk.support] at hu
           rcases hu with rfl | hu
           · exact absurd huB hs
           · exact hv_first u hu huB⟩
  termination_by _ _ w _ _ => w.length

/-- Truncate a simple walk at the LAST vertex in `B`. Given a path from `s` to `t` with `s ∈ B`,
returns `(v, w')` where `v ∈ B`, `w' : G.Walk v t` is a path, `w'.support ⊆ w.support`,
and every vertex on `w'` except `v` is NOT in `B`. Uses Walk.reverse + truncateAtFirstMem. -/
private noncomputable def Walk.truncateAtLastMem [DecidableEq V]
    {G : SimpleGraph V} (B : Finset V)
    {s t : V} (w : G.Walk s t) (hp : w.IsPath) (hs : s ∈ B) :
    { p : (v : V) × G.Walk v t //
      p.1 ∈ B ∧
      p.2.IsPath ∧
      p.2.support ⊆ w.support ∧
      (∀ u ∈ p.2.support, u ∈ B → u = p.1) } :=
  let ⟨⟨v, wv_rev⟩, hv_B, hv_path, hv_sub, hv_last⟩ :=
    Walk.truncateAtFirstMem B w.reverse hp.reverse hs
  ⟨⟨v, wv_rev.reverse⟩, hv_B, hv_path.reverse,
    by intro x hx
       have hx' : x ∈ wv_rev.support := by
         rwa [Walk.support_reverse, List.mem_reverse] at hx
       have := hv_sub hx'
       rwa [Walk.support_reverse, List.mem_reverse] at this,
    by intro u hu huB
       have hu' : u ∈ wv_rev.support := by
         rwa [Walk.support_reverse, List.mem_reverse] at hu
       exact hv_last u hu' huB⟩

/-- **Sub-lemma: Disjoint paths in G from separator** (Diestel §3.3, Steps 3-6 combined).
When X is a minimum A-B separator with |X| = k, X ≠ A, X ≠ B, and A ∩ B = ∅,
there exist k vertex-disjoint A-X paths and k vertex-disjoint X-B paths in G,
together with structural properties needed by `menger_inductive_step`:
- dst/src injectivity at X
- each path touches X only at its separator-side endpoint
- A-paths and B-paths share no non-X vertices

These properties follow from the C_A/C_B partition: paths in G_A = G[C_A ∪ X]
stay in C_A ∪ X, paths in G_B = G[C_B ∪ X] stay in C_B ∪ X, and C_A ∩ C_B = ∅.

The key insight: `ih_vert` now returns `ABConnector` (not `VertexDisjointPaths`),
which provides full vertex disjointness via `ABConnector.disjoint`. This directly
gives `dst_inj` and `src_inj`, since if two paths share an
endpoint, they share a vertex, contradicting disjointness.
No truncation at first/last X-vertex is needed: `ABConnector.touchB` (resp. touchA)
already guarantees paths touch X only at their separator-side endpoint.

**Proved**: C_A/C_B partition (incl. disjointness), G_A/G_B construction,
existence of k disjoint paths in G_A and G_B (via ih_vert + separator lifting),
path transfer (isPath + disjointness via Walk.map + ABConnector.disjoint),
"touches X only at endpoint" (by ABConnector.touchB/touchA),
A-B vertex disjointness, dst_inj (from ABConnector.disjoint), src_inj (same). -/
theorem menger_disjoint_paths_from_separator (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B X : Finset V)
    (hX_sep : G.IsABSeparator A B X)
    (hX_card : X.card = G.minABSeparatorSize A B)
    (hX_ne_A : ¬(↑X : Set V) = ↑A) (hX_ne_B : ¬(↑X : Set V) = ↑B)
    (hdisj : Disjoint A B)
    (hk : G.minABSeparatorSize A B ≠ 0)
    (ih_vert : ∀ (S : Finset V), S.card < Fintype.card V →
      ∀ (A' B' : Finset ↥(↑S : Set V)),
      (G.induce (↑S : Set V)).minABSeparatorSize A' B' ≠ 0 →
      Nonempty ((G.induce (↑S : Set V)).ABConnector A' B'
        ((G.induce (↑S : Set V)).minABSeparatorSize A' B'))) :
    ∃ (pA : G.VertexDisjointPaths A X (G.minABSeparatorSize A B))
      (pB : G.VertexDisjointPaths X B (G.minABSeparatorSize A B)),
      Function.Injective pA.dst ∧
      Function.Injective pB.src ∧
      (∀ i v, v ∈ (pA.walk i).support → v ∈ X → v = pA.dst i) ∧
      (∀ i v, v ∈ (pB.walk i).support → v ∈ X → v = pB.src i) ∧
      (∀ i j v, v ∈ (pA.walk i).support → v ∉ X → v ∉ (pB.walk j).support) ∧
      (∀ i v, v ∈ (pA.walk i).support → v ∈ A → v = pA.src i) ∧
      (∀ i v, v ∈ (pB.walk i).support → v ∈ B → v = pB.dst i) := by
  classical
  set k := G.minABSeparatorSize A B with hk_def
  -- == M3.1: Define C_A, C_B via reachability in G - X ==
  -- We define C_A and C_B as Finsets using Decidable instances.
  -- G_A_set and G_B_set are the vertex sets for the induced subgraphs.
  --

  -- Step 1: A ≠ X as Finsets (from hX_ne_A on coercions)
  have hAX_ne : A ≠ X := fun h => hX_ne_A (by rw [h])
  have hBX_ne : B ≠ X := fun h => hX_ne_B (by rw [h])
  -- Step 2: ∃ a ∈ A, a ∉ X (since A ≠ X but |X| ≤ ... — actually from A ≠ X as sets)
  -- We need: A \ X is nonempty. Since ↑X ≠ ↑A, ∃ v ∈ A with v ∉ X OR ∃ v ∈ X with v ∉ A.
  -- But X is a separator, and any separator can be assumed ⊆ V. We need A ⊄ X.
  -- Actually: |X| = k = minABSep. Since X separates A from B and A∩B=∅ and |A|≥k
  -- (otherwise A itself would be a smaller separator), we have A\X ≠ ∅.
  -- More precisely: if A ⊆ X then ↑A ⊆ ↑X, combined with |X|=|minABSep|≤|A|, gives ↑X=↑A. Contradiction.
  have hA_sub_X_false : ¬ (A ⊆ X) := by
    intro hAX
    apply hX_ne_A
    -- A ⊆ X and X is min separator with |X| = k.
    -- A is also a separator (vacuously: A\A = ∅), so |A| ≥ k.
    -- Combined with A ⊆ X and |X| = k, gives |A| = k and A = X.
    have hA_sep : G.IsABSeparator A B A := by
      intro a ha b hb haA _; exact absurd ha haA
    have hA_ge : k ≤ A.card := hk_def ▸ minABSeparatorSize_le G A B A hA_sep
    have hAX_eq : A = X := Finset.eq_of_subset_of_card_le hAX (by omega)
    rw [hAX_eq]
  have hB_sub_X_false : ¬ (B ⊆ X) := by
    intro hBX; apply hX_ne_B
    have hB_sep : G.IsABSeparator A B B := by
      intro a ha b hb _ hbB; exact absurd hb hbB
    have hB_ge : k ≤ B.card := hk_def ▸ minABSeparatorSize_le G A B B hB_sep
    have hBX_eq : B = X := Finset.eq_of_subset_of_card_le hBX (by omega)
    rw [hBX_eq]
  have ⟨a₀, ha₀A, ha₀X⟩ : ∃ a ∈ A, a ∉ X := by
    by_contra h; push_neg at h; exact hA_sub_X_false h
  have ⟨b₀, hb₀B, hb₀X⟩ : ∃ b ∈ B, b ∉ X := by
    by_contra h; push_neg at h; exact hB_sub_X_false h
  -- == M3.1: Define C_A, C_B as Finsets ==
  -- G - X: induced subgraph on V \ X
  let VmX : Finset V := Finset.univ \ X
  -- C_A: vertices in V\X reachable from some a ∈ A\X in G[V\X]
  -- C_B: vertices in V\X reachable from some b ∈ B\X in G[V\X]
  -- We define reachability via connected components of G[V\X].
  --

  --
  -- Property: C_A ∩ C_B = ∅ (from separator_splits_reachability)
  -- Property: A \ X ⊆ C_A, B \ X ⊆ C_B
  -- Property: C_A ∩ X = ∅, C_B ∩ X = ∅

  -- == M3.2: Define G_A, G_B ==
  -- G_A = G.induce (C_A ∪ X), G_B = G.induce (C_B ∪ X)
  -- For the subtype approach, we work with ↥(↑(C_A ∪ X) : Set V)

  -- == Strategy: directly construct the paths via sub-lemmas ==
  -- Rather than threading through induced subgraphs (which is extremely painful
  -- with subtype coercions), we use the following approach:
  --
  -- Key insight: menger_hard_direction works on ANY SimpleGraph with Fintype vertices.
  -- We instantiate it on G.induce S where S = C_A ∪ X (resp. C_B ∪ X).
  -- The vertex type is ↥(↑S : Set V), which has Fintype and DecidableEq.
  --
  -- Steps:
  -- 1. Show minABSep(G_A, A', X') = k where A' and X' are A∩S and X∩S as subtype Finsets
  -- 2. Get k paths in G_A via menger_hard_direction
  -- 3. Map them back to G via walk_of_induce_walk
  -- 4. Verify structural properties

  --
  --

  -- == Sub-step 1: Construct k disjoint A-X paths in G ==
  suffices h_paths :
      ∃ (pA : G.VertexDisjointPaths A X k) (pB : G.VertexDisjointPaths X B k),
        -- dst injectivity for pA
        Function.Injective pA.dst ∧
        -- src injectivity for pB
        Function.Injective pB.src ∧
        -- A-paths touch X only at dst
        (∀ i v, v ∈ (pA.walk i).support → v ∈ X → v = pA.dst i) ∧
        -- B-paths touch X only at src
        (∀ i v, v ∈ (pB.walk i).support → v ∈ X → v = pB.src i) ∧
        -- A-paths and B-paths share no non-X vertices
        (∀ i j v, v ∈ (pA.walk i).support → v ∉ X → v ∉ (pB.walk j).support) ∧
        -- A-paths touch A only at src
        (∀ i v, v ∈ (pA.walk i).support → v ∈ A → v = pA.src i) ∧
        -- B-paths touch B only at dst
        (∀ i v, v ∈ (pB.walk i).support → v ∈ B → v = pB.dst i) by
    exact h_paths
  -- == Build the paths ==
  -- Step A: Define C_A, the A-side of G - X
  -- C_A = {v ∈ V\X | reachable from A\X in G[V\X]}
  -- For Finset, use Finset.filter with Decidable reachability (Fintype gives this)
  let G_VmX : SimpleGraph ↥(↑VmX : Set V) := G.induce (↑VmX : Set V)
  -- Subtype embedding
  have hmem_VmX : ∀ v : V, v ∉ X → v ∈ (↑VmX : Set V) :=
    fun v hv => Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩)
  -- C_A as a Finset V: vertices of V\X reachable from some a ∈ A\X
  let C_A : Finset V := VmX.filter fun v =>
    ∃ (hv : v ∈ (↑VmX : Set V)),
    ∃ a ∈ A, ∃ (haX : a ∉ X),
      G_VmX.Reachable ⟨a, hmem_VmX a haX⟩ ⟨v, hv⟩
  -- C_B as a Finset V
  let C_B : Finset V := VmX.filter fun v =>
    ∃ (hv : v ∈ (↑VmX : Set V)),
    ∃ b ∈ B, ∃ (hbX : b ∉ X),
      G_VmX.Reachable ⟨b, hmem_VmX b hbX⟩ ⟨v, hv⟩
  -- Basic properties of C_A, C_B
  have hCA_sub : C_A ⊆ VmX := Finset.filter_subset _ _
  have hCB_sub : C_B ⊆ VmX := Finset.filter_subset _ _
  have hCA_disj_X : Disjoint C_A X := by
    rw [Finset.disjoint_left]; intro v hv hvX
    have := hCA_sub hv; rw [Finset.mem_sdiff] at this; exact this.2 hvX
  have hCB_disj_X : Disjoint C_B X := by
    rw [Finset.disjoint_left]; intro v hv hvX
    have := hCB_sub hv; rw [Finset.mem_sdiff] at this; exact this.2 hvX
  -- A \ X ⊆ C_A (each a ∈ A\X is reachable from itself)
  have hAmX_sub_CA : A \ X ⊆ C_A := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    have hv_VmX : v ∈ VmX := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv.2⟩
    rw [Finset.mem_filter]
    refine ⟨hv_VmX, ?_⟩
    refine ⟨hmem_VmX v hv.2, v, hv.1, hv.2, ?_⟩
    -- Need: G_VmX.Reachable ⟨v, hmem_VmX v hv.2⟩ ⟨v, hmem_VmX v hv.2⟩
    -- but goal has different proof for second argument
    convert @Reachable.refl _ G_VmX ⟨v, hmem_VmX v hv.2⟩
  -- B \ X ⊆ C_B
  have hBmX_sub_CB : B \ X ⊆ C_B := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    have hv_VmX : v ∈ VmX := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv.2⟩
    rw [Finset.mem_filter]
    refine ⟨hv_VmX, ?_⟩
    refine ⟨hmem_VmX v hv.2, v, hv.1, hv.2, ?_⟩
    convert @Reachable.refl _ G_VmX ⟨v, hmem_VmX v hv.2⟩
  -- C_A ≠ ∅ (since a₀ ∈ A\X ⊆ C_A)
  have hCA_nonempty : C_A.Nonempty :=
    ⟨a₀, hAmX_sub_CA (Finset.mem_sdiff.mpr ⟨ha₀A, ha₀X⟩)⟩
  -- C_B ≠ ∅
  have hCB_nonempty : C_B.Nonempty :=
    ⟨b₀, hBmX_sub_CB (Finset.mem_sdiff.mpr ⟨hb₀B, hb₀X⟩)⟩
  -- C_A ∩ C_B = ∅ (from separator_splits_reachability)
  have hCA_CB_disj : Disjoint C_A C_B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    have hvX : v ∉ X := (Finset.mem_sdiff.mp (hCA_sub hvA)).2
    rw [Finset.mem_filter] at hvA hvB
    obtain ⟨_, hvVmX_A, a, haA, haX, hreach_a⟩ := hvA
    obtain ⟨_, hvVmX_B, b, hbB, hbX, hreach_b⟩ := hvB
    -- Use separator_splits_reachability: a reachable to v means v not reachable from b
    exact separator_splits_reachability hX_sep haA haX hbB hbX hvX hreach_a hreach_b.symm

  -- == M3.2: G_A and G_B ==
  let SA : Finset V := C_A ∪ X   -- vertex set of G_A
  let SB : Finset V := C_B ∪ X   -- vertex set of G_B
  let G_A : SimpleGraph ↥(↑SA : Set V) := G.induce (↑SA : Set V)
  let G_B : SimpleGraph ↥(↑SB : Set V) := G.induce (↑SB : Set V)

  -- == M3.3: Convert A and X to subtype Finsets for G_A ==
  -- A' ⊆ SA: every a ∈ A is in C_A ∪ X (either a ∈ A\X ⊆ C_A or a ∈ X)
  have hA_sub_SA : A ⊆ SA := by
    intro v hv
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ hvX
    · exact Finset.mem_union_left _ (hAmX_sub_CA (Finset.mem_sdiff.mpr ⟨hv, hvX⟩))
  have hX_sub_SA : X ⊆ SA := Finset.subset_union_right
  have hB_sub_SB : B ⊆ SB := by
    intro v hv
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ hvX
    · exact Finset.mem_union_left _ (hBmX_sub_CB (Finset.mem_sdiff.mpr ⟨hv, hvX⟩))
  have hX_sub_SB : X ⊆ SB := Finset.subset_union_right
  -- Convert A to Finset of subtype SA
  let A' : Finset ↥(↑SA : Set V) := A.subtype (· ∈ (↑SA : Set V))
  let X'_A : Finset ↥(↑SA : Set V) := X.subtype (· ∈ (↑SA : Set V))
  let X'_B : Finset ↥(↑SB : Set V) := X.subtype (· ∈ (↑SB : Set V))
  let B' : Finset ↥(↑SB : Set V) := B.subtype (· ∈ (↑SB : Set V))

  -- == M3.3 + M3.4: Get k disjoint paths in G_A and G_B ==
  -- These steps require:
  -- (a) Showing minABSep(G_A, A', X'_A) = k (separator lifting argument)
  -- (b) Applying menger_hard_direction on G_A (which is a Fintype graph)
  -- (c) Transferring paths back to G via walk_of_induce_walk
  --
  --
  -- The vertex-count induction hypothesis supplies the connector.
  -- Its disjointness and endpoint properties transfer through the induced graph.
  -- This supplies the structural properties used below.

  -- == M3.3a: Get k disjoint A'-X'_A paths in G_A via ih_vert ==
  -- Strategy: show minABSep(G_A, A', X'_A) = k, then apply ih_vert.
  -- ≤ k: X'_A is a trivial separator. ≥ k: separator lifting argument.
  obtain ⟨connA'⟩ : Nonempty (G_A.ABConnector A' X'_A k) := by
    -- Step 1: SA has strictly fewer vertices than V (since C_B is nonempty and disjoint)
    have hSA_lt : SA.card < Fintype.card V := by
      rw [← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_iff_of_subset (Finset.subset_univ SA) |>.mpr
        (let ⟨b, hb⟩ := hCB_nonempty; ⟨b, Finset.mem_univ b, fun h => by
          rw [Finset.mem_union] at h
          exact h.elim (fun hCA => absurd hb (Finset.disjoint_left.mp hCA_CB_disj hCA))
                       (fun hX => absurd hX (Finset.disjoint_left.mp hCB_disj_X hb))⟩))
    -- Step 2: X'_A is a trivial A'-X'_A separator (any walk to X'_A ends in X'_A)
    have hX'A_sep : G_A.IsABSeparator A' X'_A X'_A := by
      intro a ha b hb _ hb_not; exact absurd hb hb_not
    have hX'A_card : X'_A.card = k := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem
        (fun x hx => Finset.mem_coe.mpr (hX_sub_SA hx))]
      exact hX_card
    have hmin_le_A : G_A.minABSeparatorSize A' X'_A ≤ k :=
      hX'A_card ▸ minABSeparatorSize_le G_A A' X'_A X'_A hX'A_sep
    -- Step 3: Separator lifting — any A'-X'_A separator in G_A projects to an A-B separator in G
    have hmin_ge_A : k ≤ G_A.minABSeparatorSize A' X'_A := by
      obtain ⟨S', hS'_sep, hS'_card⟩ := minABSeparatorSize_spec G_A A' X'_A
      rw [← hS'_card]
      let S'_V : Finset V := S'.map (Function.Embedding.subtype _)
      have hS'V_card : S'_V.card = S'.card := Finset.card_map _
      have hmem_S'V : ∀ (s : ↥(↑SA : Set V)), s ∈ S' → (s : V) ∈ S'_V :=
        fun s hs => Finset.mem_map.mpr ⟨s, hs, rfl⟩
      have hnot_S' : ∀ (v : V) (hv : v ∈ (↑SA : Set V)), v ∉ S'_V → ⟨v, hv⟩ ∉ S' :=
        fun v hv hvS s => hvS (hmem_S'V _ s)
      suffices hS'V_sep : G.IsABSeparator A B S'_V by
        calc k = G.minABSeparatorSize A B := hk_def
          _ ≤ S'_V.card := minABSeparatorSize_le G A B S'_V hS'V_sep
          _ = S'.card := hS'V_card
      -- Prove S'_V separates A from B in G
      intro a₀ ha₀ b₀ hb₀ haS₀ hbS₀ w₀
      -- Case 1: a₀ ∈ X — contradiction via nil walk in G_A
      by_cases haX₀ : a₀ ∈ X
      · exfalso
        have ha_SA : a₀ ∈ (↑SA : Set V) := Finset.mem_coe.mpr (hA_sub_SA ha₀)
        have ha_not_S' := hnot_S' a₀ ha_SA haS₀
        obtain ⟨v, hv_mem, hv_S'⟩ := hS'_sep ⟨a₀, ha_SA⟩ (Finset.mem_subtype.mpr ha₀)
          ⟨a₀, ha_SA⟩ (Finset.mem_subtype.mpr haX₀) ha_not_S' ha_not_S' Walk.nil
        simp at hv_mem; rw [hv_mem] at hv_S'; exact ha_not_S' hv_S'
      -- Case 2: a₀ ∉ X — walk prefix argument
      · have ha₀_CA : a₀ ∈ C_A := hAmX_sub_CA (Finset.mem_sdiff.mpr ⟨ha₀, haX₀⟩)
        by_contra h_no_hit
        push_neg at h_no_hit
        -- h_no_hit : ∀ v ∈ w₀.support, v ∉ S'_V
        -- Helper: C_A is closed under adjacency within V\X
        have hCA_step : ∀ (v v' : V), v ∈ C_A → G.Adj v v' → v' ∉ X → v' ∈ C_A := by
          intro v v' hv hadj hv'X
          rw [Finset.mem_filter] at hv ⊢
          have hv'_VmX : v' ∈ VmX := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v', hv'X⟩
          refine ⟨hv'_VmX, ?_⟩
          obtain ⟨_, a, haA, haX, hreach⟩ := hv.2
          exact ⟨Finset.mem_coe.mpr hv'_VmX, a, haA, haX,
            hreach.trans (induce_adj.mpr hadj).reachable⟩
        -- Build a walk in G_A from ⟨a₀,_⟩ to some ⟨x,_⟩ ∈ X'_A by walk induction.
        -- The walk stays in C_A until it first hits X, so all vertices are in SA.
        -- Key claim: for v ∈ C_A, walk from v, all support ∉ S'_V,
        -- either all in C_A, or we can produce a G_A walk from ⟨v,_⟩ to some ⟨x,_⟩ ∈ X
        -- whose support vertices (projected) are a subset of w.support.
        suffices aux : ∀ {v u : V} (w : G.Walk v u) (hv : v ∈ C_A),
            (∀ s ∈ w.support, s ∉ S'_V) →
            (∀ s ∈ w.support, s ∈ C_A) ∨
            (∃ (x : V) (hxX : x ∈ X),
              let hv_SA : v ∈ (↑SA : Set V) := Finset.mem_coe.mpr (Finset.mem_union_left _ hv)
              let hx_SA : x ∈ (↑SA : Set V) := Finset.mem_coe.mpr (hX_sub_SA hxX)
              ∃ (wGA : G_A.Walk ⟨v, hv_SA⟩ ⟨x, hx_SA⟩),
                ∀ s ∈ wGA.support, (s : V) ∈ w.support ∧ (s : V) ∉ S'_V) by
          cases aux w₀ ha₀_CA h_no_hit with
          | inl hall_CA =>
            have hb₀_CA := hall_CA b₀ (Walk.end_mem_support w₀)
            by_cases hb₀X : b₀ ∈ X
            · exact absurd hb₀_CA (fun h => Finset.disjoint_left.mp hCA_disj_X h hb₀X)
            · exact absurd hb₀_CA (fun h =>
                Finset.disjoint_left.mp hCA_CB_disj h
                  (hBmX_sub_CB (Finset.mem_sdiff.mpr ⟨hb₀, hb₀X⟩)))
          | inr hex =>
            obtain ⟨x₀, hx₀X, wGA, hwGA⟩ := hex
            have ha₀_SA : a₀ ∈ (↑SA : Set V) := Finset.mem_coe.mpr (hA_sub_SA ha₀)
            have hx₀_SA : x₀ ∈ (↑SA : Set V) := Finset.mem_coe.mpr (hX_sub_SA hx₀X)
            have ha₀_A' : (⟨a₀, ha₀_SA⟩ : ↥(↑SA : Set V)) ∈ A' := Finset.mem_subtype.mpr ha₀
            have hx₀_X'A : (⟨x₀, hx₀_SA⟩ : ↥(↑SA : Set V)) ∈ X'_A :=
              Finset.mem_subtype.mpr hx₀X
            have ha₀_not_S' := hnot_S' a₀ ha₀_SA haS₀
            -- x₀ ∈ w₀.support (from wGA support tracking)
            have hx₀_supp := (hwGA ⟨x₀, hx₀_SA⟩ (Walk.end_mem_support wGA)).1
            have hx₀_not_S' := hnot_S' x₀ hx₀_SA (h_no_hit x₀ hx₀_supp)
            obtain ⟨s, hs_mem, hs_S'⟩ := hS'_sep ⟨a₀, ha₀_SA⟩ ha₀_A' ⟨x₀, hx₀_SA⟩ hx₀_X'A
              ha₀_not_S' hx₀_not_S' wGA
            exact absurd (hmem_S'V s hs_S') (hwGA s hs_mem).2
        -- Prove the auxiliary claim by Walk induction
        intro v u w
        induction w with
        | nil => intro hv _; left; intro s hs; simp at hs; exact hs ▸ hv
        | cons hadj₀ w₁ ih =>
          -- rename the inaccessible source, next, and end vertices
          rename_i v₀ v₁ w_end
          intro hv₀ h_no₀
          by_cases hv₁X : v₁ ∈ X
          · -- v₁ ∈ X: build one-step walk in G_A from ⟨v₀,_⟩ to ⟨v₁,_⟩
            right
            refine ⟨v₁, hv₁X, ?_⟩
            have hv₀_SA : v₀ ∈ (↑SA : Set V) :=
              Finset.mem_coe.mpr (Finset.mem_union_left _ hv₀)
            have hv₁_SA : v₁ ∈ (↑SA : Set V) :=
              Finset.mem_coe.mpr (hX_sub_SA hv₁X)
            have hadj_GA : G_A.Adj ⟨v₀, hv₀_SA⟩ ⟨v₁, hv₁_SA⟩ := induce_adj.mpr hadj₀
            refine ⟨Walk.cons hadj_GA Walk.nil, ?_⟩
            intro s hs
            simp [Walk.support] at hs
            cases hs with
            | inl h =>
              exact ⟨h ▸ Walk.start_mem_support (Walk.cons hadj₀ w₁),
                     h ▸ h_no₀ v₀ (Walk.start_mem_support (Walk.cons hadj₀ w₁))⟩
            | inr h =>
              exact ⟨h ▸ List.Mem.tail _ (Walk.start_mem_support w₁),
                     h ▸ h_no₀ v₁ (List.Mem.tail _ (Walk.start_mem_support w₁))⟩
          · -- v₁ ∉ X: v₁ ∈ C_A, recurse
            have hv₁_CA := hCA_step v₀ v₁ hv₀ hadj₀ hv₁X
            have h_no₁ : ∀ s ∈ w₁.support, s ∉ S'_V :=
              fun s hs => h_no₀ s (List.Mem.tail _ hs)
            cases ih hv₁_CA h_no₁ with
            | inl hall =>
              left; intro s hs
              cases List.eq_or_mem_of_mem_cons hs with
              | inl h => exact h ▸ hv₀
              | inr h => exact hall s h
            | inr hex =>
              right
              obtain ⟨x, hxX, wGA, hwGA⟩ := hex
              refine ⟨x, hxX, ?_⟩
              have hv₀_SA : v₀ ∈ (↑SA : Set V) :=
                Finset.mem_coe.mpr (Finset.mem_union_left _ hv₀)
              have hv₁_SA : v₁ ∈ (↑SA : Set V) :=
                Finset.mem_coe.mpr (Finset.mem_union_left _ hv₁_CA)
              have hadj_GA : G_A.Adj ⟨v₀, hv₀_SA⟩ ⟨v₁, hv₁_SA⟩ := induce_adj.mpr hadj₀
              refine ⟨Walk.cons hadj_GA wGA, ?_⟩
              intro s hs
              simp [Walk.support] at hs
              cases hs with
              | inl h =>
                exact ⟨h ▸ Walk.start_mem_support (Walk.cons hadj₀ w₁),
                       h ▸ h_no₀ v₀ (Walk.start_mem_support (Walk.cons hadj₀ w₁))⟩
              | inr h =>
                have := hwGA s h
                exact ⟨List.Mem.tail _ this.1, this.2⟩
    have hmin_eq_A : G_A.minABSeparatorSize A' X'_A = k := Nat.le_antisymm hmin_le_A hmin_ge_A
    have hmin_ne_A : G_A.minABSeparatorSize A' X'_A ≠ 0 := by omega
    have h_dp := ih_vert SA hSA_lt A' X'_A hmin_ne_A
    rwa [hmin_eq_A] at h_dp
  -- == M3.3b: Get k disjoint X'_B-B' paths in G_B via ih_vert (symmetric) ==
  obtain ⟨connB'⟩ : Nonempty (G_B.ABConnector X'_B B' k) := by
    have hSB_lt : SB.card < Fintype.card V := by
      rw [← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_iff_of_subset (Finset.subset_univ SB) |>.mpr
        (let ⟨a, ha⟩ := hCA_nonempty; ⟨a, Finset.mem_univ a, fun h => by
          rw [Finset.mem_union] at h
          exact h.elim (fun hCB => absurd ha (Finset.disjoint_left.mp hCA_CB_disj.symm hCB))
                       (fun hX => absurd hX (Finset.disjoint_left.mp hCA_disj_X ha))⟩))
    have hX'B_sep : G_B.IsABSeparator X'_B B' X'_B := by
      intro a ha b hb ha_not _; exact absurd ha ha_not
    have hX'B_card : X'_B.card = k := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem
        (fun x hx => Finset.mem_coe.mpr (hX_sub_SB hx))]
      exact hX_card
    have hmin_le_B : G_B.minABSeparatorSize X'_B B' ≤ k :=
      hX'B_card ▸ minABSeparatorSize_le G_B X'_B B' X'_B hX'B_sep
    have hmin_ge_B : k ≤ G_B.minABSeparatorSize X'_B B' := by
      obtain ⟨S', hS'_sep, hS'_card⟩ := minABSeparatorSize_spec G_B X'_B B'
      rw [← hS'_card]
      let S'_V : Finset V := S'.map (Function.Embedding.subtype _)
      have hS'V_card : S'_V.card = S'.card := Finset.card_map _
      have hmem_S'V : ∀ (s : ↥(↑SB : Set V)), s ∈ S' → (s : V) ∈ S'_V :=
        fun s hs => Finset.mem_map.mpr ⟨s, hs, rfl⟩
      have hnot_S' : ∀ (v : V) (hv : v ∈ (↑SB : Set V)), v ∉ S'_V → ⟨v, hv⟩ ∉ S' :=
        fun v hv hvS s => hvS (hmem_S'V _ s)
      suffices hS'V_sep : G.IsABSeparator A B S'_V by
        calc k = G.minABSeparatorSize A B := hk_def
          _ ≤ S'_V.card := minABSeparatorSize_le G A B S'_V hS'V_sep
          _ = S'.card := hS'V_card
      -- Prove S'_V separates A from B in G (symmetric: B-side)
      intro a₀ ha₀ b₀ hb₀ haS₀ hbS₀ w₀
      by_cases hbX₀ : b₀ ∈ X
      · exfalso
        have hb_SB : b₀ ∈ (↑SB : Set V) := Finset.mem_coe.mpr (hB_sub_SB hb₀)
        have hb_not_S' := hnot_S' b₀ hb_SB hbS₀
        obtain ⟨v, hv_mem, hv_S'⟩ := hS'_sep ⟨b₀, hb_SB⟩ (Finset.mem_subtype.mpr hbX₀)
          ⟨b₀, hb_SB⟩ (Finset.mem_subtype.mpr hb₀) hb_not_S' hb_not_S' Walk.nil
        simp at hv_mem; rw [hv_mem] at hv_S'; exact hb_not_S' hv_S'
      · have hb₀_CB : b₀ ∈ C_B := hBmX_sub_CB (Finset.mem_sdiff.mpr ⟨hb₀, hbX₀⟩)
        by_contra h_no_hit
        push_neg at h_no_hit
        have hCB_step : ∀ (v v' : V), v ∈ C_B → G.Adj v v' → v' ∉ X → v' ∈ C_B := by
          intro v v' hv hadj hv'X
          rw [Finset.mem_filter] at hv ⊢
          have hv'_VmX : v' ∈ VmX := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v', hv'X⟩
          refine ⟨hv'_VmX, ?_⟩
          obtain ⟨_, b, hbB, hbX, hreach⟩ := hv.2
          exact ⟨Finset.mem_coe.mpr hv'_VmX, b, hbB, hbX,
            hreach.trans (induce_adj.mpr hadj).reachable⟩
        -- Use reversed walk: b₀ → ... → a₀
        -- Same aux structure as A-side but for C_B and SB
        have h_no_rev : ∀ s ∈ w₀.reverse.support, s ∉ S'_V := by
          intro s hs
          have : s ∈ w₀.support := by
            rw [Walk.support_reverse] at hs; exact List.mem_reverse.mp hs
          exact h_no_hit s this
        suffices aux : ∀ {v u : V} (w : G.Walk v u) (hv : v ∈ C_B),
            (∀ s ∈ w.support, s ∉ S'_V) →
            (∀ s ∈ w.support, s ∈ C_B) ∨
            (∃ (x : V) (hxX : x ∈ X),
              let hv_SB : v ∈ (↑SB : Set V) := Finset.mem_coe.mpr (Finset.mem_union_left _ hv)
              let hx_SB : x ∈ (↑SB : Set V) := Finset.mem_coe.mpr (hX_sub_SB hxX)
              ∃ (wGB : G_B.Walk ⟨v, hv_SB⟩ ⟨x, hx_SB⟩),
                ∀ s ∈ wGB.support, (s : V) ∈ w.support ∧ (s : V) ∉ S'_V) by
          cases aux w₀.reverse hb₀_CB h_no_rev with
          | inl hall_CB =>
            have ha₀_CB := hall_CB a₀ (by
              rw [Walk.support_reverse]; exact List.mem_reverse.mpr (w₀.start_mem_support))
            by_cases haX₀ : a₀ ∈ X
            · exact absurd ha₀_CB (fun h => Finset.disjoint_left.mp hCB_disj_X h haX₀)
            · exact absurd ha₀_CB (fun h =>
                Finset.disjoint_left.mp hCA_CB_disj
                  (hAmX_sub_CA (Finset.mem_sdiff.mpr ⟨ha₀, haX₀⟩)) h)
          | inr hex =>
            obtain ⟨x₀, hx₀X, wGB, hwGB⟩ := hex
            have hb₀_SB : b₀ ∈ (↑SB : Set V) := Finset.mem_coe.mpr (hB_sub_SB hb₀)
            have hx₀_SB : x₀ ∈ (↑SB : Set V) := Finset.mem_coe.mpr (hX_sub_SB hx₀X)
            have hx₀_X'B : (⟨x₀, hx₀_SB⟩ : ↥(↑SB : Set V)) ∈ X'_B :=
              Finset.mem_subtype.mpr hx₀X
            have hb₀_B' : (⟨b₀, hb₀_SB⟩ : ↥(↑SB : Set V)) ∈ B' :=
              Finset.mem_subtype.mpr hb₀
            have hb₀_not_S' := hnot_S' b₀ hb₀_SB hbS₀
            have hx₀_supp := (hwGB ⟨x₀, hx₀_SB⟩ (Walk.end_mem_support wGB)).1
            have hx₀_not_S' := hnot_S' x₀ hx₀_SB ((hwGB ⟨x₀, hx₀_SB⟩ (Walk.end_mem_support wGB)).2)
            -- S' separates X'_B from B', so walk from ⟨b₀,_⟩ to ⟨x₀,_⟩ must hit S'
            -- But the separator is X'_B → B', so we need walk from X'_B vertex to B' vertex
            -- wGB goes from ⟨b₀,_⟩ to ⟨x₀,_⟩, but separator needs X'_B → B', so reverse
            obtain ⟨s, hs_mem, hs_S'⟩ := hS'_sep ⟨x₀, hx₀_SB⟩ hx₀_X'B ⟨b₀, hb₀_SB⟩ hb₀_B'
              hx₀_not_S' hb₀_not_S' wGB.reverse
            have hs_wGB : s ∈ wGB.support := by
              rw [Walk.support_reverse] at hs_mem; exact List.mem_reverse.mp hs_mem
            exact absurd (hmem_S'V s hs_S') (hwGB s hs_wGB).2
        -- Prove aux by Walk induction (same as A-side)
        intro v u w
        induction w with
        | nil => intro hv _; left; intro s hs; simp at hs; exact hs ▸ hv
        | cons hadj₀ w₁ ih =>
          rename_i v₀ v₁ w_end
          intro hv₀ h_no₀
          by_cases hv₁X : v₁ ∈ X
          · right
            refine ⟨v₁, hv₁X, ?_⟩
            have hv₀_SB : v₀ ∈ (↑SB : Set V) :=
              Finset.mem_coe.mpr (Finset.mem_union_left _ hv₀)
            have hv₁_SB : v₁ ∈ (↑SB : Set V) :=
              Finset.mem_coe.mpr (hX_sub_SB hv₁X)
            have hadj_GB : G_B.Adj ⟨v₀, hv₀_SB⟩ ⟨v₁, hv₁_SB⟩ := induce_adj.mpr hadj₀
            refine ⟨Walk.cons hadj_GB Walk.nil, ?_⟩
            intro s hs
            simp [Walk.support] at hs
            cases hs with
            | inl h =>
              exact ⟨h ▸ Walk.start_mem_support (Walk.cons hadj₀ w₁),
                     h ▸ h_no₀ v₀ (Walk.start_mem_support (Walk.cons hadj₀ w₁))⟩
            | inr h =>
              exact ⟨h ▸ List.Mem.tail _ (Walk.start_mem_support w₁),
                     h ▸ h_no₀ v₁ (List.Mem.tail _ (Walk.start_mem_support w₁))⟩
          · have hv₁_CB := hCB_step v₀ v₁ hv₀ hadj₀ hv₁X
            have h_no₁ : ∀ s ∈ w₁.support, s ∉ S'_V :=
              fun s hs => h_no₀ s (List.Mem.tail _ hs)
            cases ih hv₁_CB h_no₁ with
            | inl hall =>
              left; intro s hs
              cases List.eq_or_mem_of_mem_cons hs with
              | inl h => exact h ▸ hv₀
              | inr h => exact hall s h
            | inr hex =>
              right
              obtain ⟨x, hxX, wGB, hwGB⟩ := hex
              refine ⟨x, hxX, ?_⟩
              have hv₀_SB : v₀ ∈ (↑SB : Set V) :=
                Finset.mem_coe.mpr (Finset.mem_union_left _ hv₀)
              have hv₁_SB : v₁ ∈ (↑SB : Set V) :=
                Finset.mem_coe.mpr (Finset.mem_union_left _ hv₁_CB)
              have hadj_GB : G_B.Adj ⟨v₀, hv₀_SB⟩ ⟨v₁, hv₁_SB⟩ := induce_adj.mpr hadj₀
              refine ⟨Walk.cons hadj_GB wGB, ?_⟩
              intro s hs
              simp [Walk.support] at hs
              cases hs with
              | inl h =>
                exact ⟨h ▸ Walk.start_mem_support (Walk.cons hadj₀ w₁),
                       h ▸ h_no₀ v₀ (Walk.start_mem_support (Walk.cons hadj₀ w₁))⟩
              | inr h =>
                have := hwGB s h
                exact ⟨List.Mem.tail _ this.1, this.2⟩
    have hmin_eq_B : G_B.minABSeparatorSize X'_B B' = k := Nat.le_antisymm hmin_le_B hmin_ge_B
    have hmin_ne_B : G_B.minABSeparatorSize X'_B B' ≠ 0 := by omega
    have h_dp := ih_vert SB hSB_lt X'_B B' hmin_ne_B
    rwa [hmin_eq_B] at h_dp

  -- == M3.5: Transfer ABConnector paths to G, verify properties ==
  -- With ABConnector, NO truncation is needed!
  -- connA'.touchB: paths touch X'_A only at dst
  -- connA'.disjoint: paths are FULLY vertex-disjoint
  --

  -- Build the A-X paths in G by mapping ABConnector walks through the subtype embedding
  let pA : G.VertexDisjointPaths A X k :=
    { src := fun i => ↑(connA'.src i)
      dst := fun i => ↑(connA'.dst i)
      walk := fun i => walk_of_induce_walk (connA'.walk i)
      isPath := by
        intro i
        exact Walk.map_isPath_of_injective Subtype.val_injective (connA'.isPath i)
      src_mem := fun i => by
        have := connA'.src_mem i; rw [Finset.mem_subtype] at this; exact this
      dst_mem := fun i => by
        have := connA'.dst_mem i; rw [Finset.mem_subtype] at this; exact this
      src_inj := by
        intro i j hij
        have heq : connA'.src i = connA'.src j := Subtype.val_injective hij
        by_contra hne
        have hmem_j : connA'.src i ∈ (connA'.walk j).support := by
          rw [heq]; exact Walk.start_mem_support _
        exact connA'.disjoint i j hne (connA'.src i) (Walk.start_mem_support _) hmem_j
      dst_inj := by
        -- With ABConnector.disjoint: if dst i = dst j for i ≠ j,
        -- then (dst i) ∈ support of walk i AND walk j, contradicting disjoint.
        intro i j hij
        have heq : connA'.dst i = connA'.dst j := Subtype.val_injective hij
        by_contra hne
        have hmem_j : connA'.dst i ∈ (connA'.walk j).support := by
          rw [heq]; exact Walk.end_mem_support _
        exact connA'.disjoint i j hne (connA'.dst i) (Walk.end_mem_support _) hmem_j
      internal_disjoint := by
        intro i j hij v hvi _ _ hvj _ _
        have hvi' : v ∈ List.map Subtype.val (connA'.walk i).support := by
          have := Walk.support_map (Embedding.induce (↑SA : Set V)).toHom (connA'.walk i)
          exact this ▸ hvi
        have hvj' : v ∈ List.map Subtype.val (connA'.walk j).support := by
          have := Walk.support_map (Embedding.induce (↑SA : Set V)).toHom (connA'.walk j)
          exact this ▸ hvj
        rw [List.mem_map] at hvi' hvj'
        obtain ⟨ui, hui, rfl⟩ := hvi'
        obtain ⟨uj, huj, huj_eq⟩ := hvj'
        have heq : uj = ui := Subtype.val_injective huj_eq
        rw [heq] at huj
        exact connA'.disjoint i j hij ui hui huj }
  let pB : G.VertexDisjointPaths X B k :=
    { src := fun i => ↑(connB'.src i)
      dst := fun i => ↑(connB'.dst i)
      walk := fun i => walk_of_induce_walk (connB'.walk i)
      isPath := by
        intro i
        exact Walk.map_isPath_of_injective Subtype.val_injective (connB'.isPath i)
      src_mem := fun i => by
        have := connB'.src_mem i; rw [Finset.mem_subtype] at this; exact this
      dst_mem := fun i => by
        have := connB'.dst_mem i; rw [Finset.mem_subtype] at this; exact this
      src_inj := by
        intro i j hij
        have heq : connB'.src i = connB'.src j := Subtype.val_injective hij
        by_contra hne
        have hmem_j : connB'.src i ∈ (connB'.walk j).support := by
          rw [heq]; exact Walk.start_mem_support _
        exact connB'.disjoint i j hne (connB'.src i) (Walk.start_mem_support _) hmem_j
      dst_inj := by
        intro i j hij
        have heq : connB'.dst i = connB'.dst j := Subtype.val_injective hij
        by_contra hne
        have hmem_j : connB'.dst i ∈ (connB'.walk j).support := by
          rw [heq]; exact Walk.end_mem_support _
        exact connB'.disjoint i j hne (connB'.dst i) (Walk.end_mem_support _) hmem_j
      internal_disjoint := by
        intro i j hij v hvi _ _ hvj _ _
        have hvi' : v ∈ List.map Subtype.val (connB'.walk i).support := by
          have := Walk.support_map (Embedding.induce (↑SB : Set V)).toHom (connB'.walk i)
          exact this ▸ hvi
        have hvj' : v ∈ List.map Subtype.val (connB'.walk j).support := by
          have := Walk.support_map (Embedding.induce (↑SB : Set V)).toHom (connB'.walk j)
          exact this ▸ hvj
        rw [List.mem_map] at hvi' hvj'
        obtain ⟨ui, hui, rfl⟩ := hvi'
        obtain ⟨uj, huj, huj_eq⟩ := hvj'
        have heq : uj = ui := Subtype.val_injective huj_eq
        rw [heq] at huj
        exact connB'.disjoint i j hij ui hui huj }
  -- == M3.5: Structural properties ==
  refine ⟨pA, pB, pA.dst_inj, pB.src_inj, ?_, ?_, ?_, ?_, ?_⟩
  · -- A-paths touch X only at dst (follows from connA'.touchB)
    intro i v hv hvX
    have hsupp : (pA.walk i).support = List.map Subtype.val (connA'.walk i).support :=
      Walk.support_map (Embedding.induce (↑SA : Set V)).toHom (connA'.walk i)
    rw [hsupp, List.mem_map] at hv
    obtain ⟨⟨u, hu_SA⟩, hu_walk, rfl⟩ := hv
    have hu_XA : (⟨u, hu_SA⟩ : ↥(↑SA : Set V)) ∈ X'_A := by
      rw [Finset.mem_subtype]; exact hvX
    have := connA'.touchB i ⟨u, hu_SA⟩ hu_walk hu_XA
    exact congrArg Subtype.val this
  · -- B-paths touch X only at src (follows from connB'.touchA)
    intro i v hv hvX
    have hsupp : (pB.walk i).support = List.map Subtype.val (connB'.walk i).support :=
      Walk.support_map (Embedding.induce (↑SB : Set V)).toHom (connB'.walk i)
    rw [hsupp, List.mem_map] at hv
    obtain ⟨⟨u, hu_SB⟩, hu_walk, rfl⟩ := hv
    have hu_XB : (⟨u, hu_SB⟩ : ↥(↑SB : Set V)) ∈ X'_B := by
      rw [Finset.mem_subtype]; exact hvX
    have := connB'.touchA i ⟨u, hu_SB⟩ hu_walk hu_XB
    exact congrArg Subtype.val this
  · -- A-paths and B-paths share no non-X vertices
    intro i j v hv hvX hvB
    have hsupp_A : (pA.walk i).support = List.map Subtype.val (connA'.walk i).support :=
      Walk.support_map (Embedding.induce (↑SA : Set V)).toHom (connA'.walk i)
    have hsupp_B : (pB.walk j).support = List.map Subtype.val (connB'.walk j).support :=
      Walk.support_map (Embedding.induce (↑SB : Set V)).toHom (connB'.walk j)
    have hv_SA : v ∈ SA := by
      rw [hsupp_A, List.mem_map] at hv
      obtain ⟨⟨u, hu_SA⟩, _, rfl⟩ := hv
      exact Finset.mem_coe.mp hu_SA
    have hvB_SB : v ∈ SB := by
      rw [hsupp_B, List.mem_map] at hvB
      obtain ⟨⟨u, hu_SB⟩, _, rfl⟩ := hvB
      exact Finset.mem_coe.mp hu_SB
    have hv_CA : v ∈ C_A := by
      rcases Finset.mem_union.mp hv_SA with h | h
      · exact h
      · exact absurd h hvX
    have hv_CB : v ∈ C_B := by
      rcases Finset.mem_union.mp hvB_SB with h | h
      · exact h
      · exact absurd h hvX
    exact absurd hv_CB (Finset.disjoint_left.mp hCA_CB_disj hv_CA)
  · -- A-paths touch A only at src (follows from connA'.touchA)
    intro i v hv hvA
    have hsupp : (pA.walk i).support = List.map Subtype.val (connA'.walk i).support :=
      Walk.support_map (Embedding.induce (↑SA : Set V)).toHom (connA'.walk i)
    rw [hsupp, List.mem_map] at hv
    obtain ⟨⟨u, hu_SA⟩, hu_walk, rfl⟩ := hv
    have hu_A' : (⟨u, hu_SA⟩ : ↥(↑SA : Set V)) ∈ A' := by
      rw [Finset.mem_subtype]; exact hvA
    have := connA'.touchA i ⟨u, hu_SA⟩ hu_walk hu_A'
    exact congrArg Subtype.val this
  · -- B-paths touch B only at dst (follows from connB'.touchB)
    intro i v hv hvB
    have hsupp : (pB.walk i).support = List.map Subtype.val (connB'.walk i).support :=
      Walk.support_map (Embedding.induce (↑SB : Set V)).toHom (connB'.walk i)
    rw [hsupp, List.mem_map] at hv
    obtain ⟨⟨u, hu_SB⟩, hu_walk, rfl⟩ := hv
    have hu_B' : (⟨u, hu_SB⟩ : ↥(↑SB : Set V)) ∈ B' := by
      rw [Finset.mem_subtype]; exact hvB
    have := connB'.touchB i ⟨u, hu_SB⟩ hu_walk hu_B'
    exact congrArg Subtype.val this

/-- A walk in G that avoids vertex `a` is also a walk in G.deleteEdges s
for any edge set s where every edge in s is incident to a. -/
private theorem walk_avoid_to_deleteEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    {a : V} {s : Set (Sym2 V)} (hs : ∀ e ∈ s, a ∈ e) :
    ∀ {x y : V} (w : G.Walk x y), a ∉ w.support →
    ∃ w' : (G.deleteEdges s).Walk x y, w'.support = w.support
  | _, _, Walk.nil, _ => ⟨Walk.nil, rfl⟩
  | _, _, Walk.cons hadj w', ha => by
    have hu : a ≠ _ := fun heq => ha (by simp [Walk.support_cons]; left; exact heq)
    have hav : a ∉ w'.support := fun h => ha (by simp [Walk.support_cons]; right; exact h)
    obtain ⟨w'', hw''⟩ := walk_avoid_to_deleteEdges hs w' hav
    refine ⟨Walk.cons ?_ w'', ?_⟩
    · simp only [deleteEdges_adj, Set.mem_singleton_iff]
      refine ⟨hadj, fun hmem => ?_⟩
      have := hs _ hmem
      rw [Sym2.mem_iff] at this
      rcases this with rfl | rfl
      · exact hu rfl
      · exact ha (List.mem_cons_of_mem _ (Walk.start_mem_support w'))
    · simp [Walk.support_cons, hw'']

/-- **Diestel's edge deletion argument for Case 2 of Menger's theorem.**
When A∩B=∅, k≥2, and every min separator equals A or B (as sets),
construct k vertex-disjoint A-B paths by removing an edge and applying IH.

Proof outline (Diestel Thm 3.3.1, "Second proof", p.51):
1. Since k ≥ 1, ∅ is not a separator → ∃ A-B path P with an edge a→b where a∈A, b∉A.
2. Define G' = G.deleteEdges {s(a,b)}.
3. Get min separator Y in G' with |Y| = minABSep(G').
4. Y_a = insert a Y and Y_b = insert b Y are both A-B separators in G.
5. |Y_a| ≥ k, |Y_b| ≥ k. If both = k, then Y_a = A, Y_b = B (by hall),
   so Y ⊆ A ∩ B = ∅, but |Y| ≥ k-1 ≥ 1, contradiction.
6. Hence |Y| ≥ k, i.e. minABSep(G') ≥ k. Apply IH on G' (fewer edges),
   transfer paths via Walk.mapLe. -/
theorem menger_diestel_edge_deletion (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hk : G.minABSeparatorSize A B ≠ 0)
    (hk2 : G.minABSeparatorSize A B ≠ 1)
    (hdisj : Disjoint A B)
    (hall : ∀ X : Finset V, G.IsABSeparator A B X →
      X.card = G.minABSeparatorSize A B →
      (↑X : Set V) = ↑A ∨ (↑X : Set V) = ↑B)
    (ih : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
      G'.edgeFinset.card < G.edgeFinset.card →
      G'.minABSeparatorSize A B ≠ 0 →
      Nonempty (G'.ABConnector A B (G'.minABSeparatorSize A B))) :
    Nonempty (G.ABConnector A B (G.minABSeparatorSize A B)) := by
  set k := G.minABSeparatorSize A B with hk_def
  -- Step 1: ∅ is not a separator (since k ≥ 1), so ∃ walk from A to B
  have hnosep : ¬ G.IsABSeparator A B ∅ := by
    intro hsep
    have := minABSeparatorSize_le G A B ∅ hsep
    simp at this; omega
  simp only [IsABSeparator, not_forall] at hnosep
  obtain ⟨a₀, ha₀, b₀, hb₀, _, _, w₀, hw₀⟩ := hnosep
  -- b₀ ∉ A (from disjointness)
  have hb₀A : b₀ ∉ A := Finset.disjoint_right.mp hdisj hb₀
  -- Use walk_first_hit with Aᶜ to find first vertex outside A on the walk
  obtain ⟨b, wb, hbAc, _hwb_sub, hwb_avoid⟩ :=
    walk_first_hit Aᶜ w₀ (Finset.mem_compl.mpr hb₀A) (by simp [Finset.mem_compl]; exact ha₀)
  -- b ∉ A
  have hbA : b ∉ A := Finset.mem_compl.mp hbAc
  -- wb has length ≥ 1 (since a₀ ∈ A but b ∉ A)
  have hwb_pos : 0 < wb.length := by
    rcases Nat.eq_zero_or_pos wb.length with h | h
    · exact absurd (Walk.eq_of_length_eq_zero h ▸ ha₀) hbA
    · exact h
  -- Define a = wb.getVert (wb.length - 1), the predecessor of b
  set a := wb.getVert (wb.length - 1) with ha_def
  -- a is adjacent to b in G
  have hadj : G.Adj a b := by
    have h := wb.adj_getVert_succ (i := wb.length - 1) (by omega)
    rwa [Nat.sub_one_add_one_eq_of_pos hwb_pos, Walk.getVert_length] at h
  -- a ∈ A (a is on the walk and ≠ b, so not in Aᶜ)
  have haA : a ∈ A := by
    have hmem : a ∈ wb.support := Walk.getVert_mem_support wb (wb.length - 1)
    have hne : a ≠ b := hadj.ne
    have := hwb_avoid a hmem hne
    rwa [Finset.mem_compl, not_not] at this
  -- a ∉ B (from disjointness)
  have haB : a ∉ B := Finset.disjoint_left.mp hdisj haA
  -- Step 2: Define G' = G.deleteEdges {s(a,b)}
  set G' := G.deleteEdges {s(a, b)} with hG'_def
  have hG'_le : G' ≤ G := deleteEdges_le _
  -- Step 3: Get min separator Y in G'
  obtain ⟨Y, hY_sep, hY_card⟩ := minABSeparatorSize_spec G' A B
  -- Step 4: Build Y_a = insert a Y, Y_b = insert b Y
  -- Show Y_a is an A-B separator in G
  have hYa_sep : G.IsABSeparator A B (insert a Y) := by
    intro x hxA y hyB hxYa hyYa w
    by_cases haw : a ∈ w.support
    · -- a is on the walk, and a ∈ insert a Y
      exact ⟨a, haw, Finset.mem_insert_self a Y⟩
    · -- a ∉ w.support → walk avoids vertex a → walk is in G'
      have ha_inc : ∀ e ∈ ({s(a, b)} : Set (Sym2 V)), a ∈ e := by
        intro e he; simp at he; rw [he]; exact Sym2.mem_mk_left a b
      obtain ⟨w', hw'⟩ := walk_avoid_to_deleteEdges ha_inc w haw
      -- x ∉ Y and y ∉ Y (from hxYa, hyYa minus the `a` part)
      have hxY : x ∉ Y := fun h => hxYa (Finset.mem_insert_of_mem h)
      have hyY : y ∉ Y := fun h => hyYa (Finset.mem_insert_of_mem h)
      -- w' is a walk in G' from x to y, so it hits Y
      obtain ⟨v, hv_mem, hv_Y⟩ := hY_sep x hxA y hyB hxY hyY w'
      exact ⟨v, hw' ▸ hv_mem, Finset.mem_insert_of_mem hv_Y⟩
  -- Show Y_b is an A-B separator in G
  have hYb_sep : G.IsABSeparator A B (insert b Y) := by
    intro x hxA y hyB hxYb hyYb w
    by_cases hbw : b ∈ w.support
    · exact ⟨b, hbw, Finset.mem_insert_self b Y⟩
    · -- b ∉ w.support → walk avoids vertex b → walk is in G' = G.deleteEdges {s(a,b)}
      -- Need: walk_avoid_to_deleteEdges with b avoided, deleting {s(a,b)}
      -- Since s(a,b) = s(b,a), we can use walk_avoid_to_deleteEdges b a and rewrite
      -- b ∈ s(a,b), so walk_avoid_to_deleteEdges applies
      have hb_inc : ∀ e ∈ ({s(a, b)} : Set (Sym2 V)), b ∈ e := by
        intro e he; simp at he; rw [he]; exact Sym2.mem_mk_right a b
      obtain ⟨w', hw'⟩ := walk_avoid_to_deleteEdges hb_inc w hbw
      have hxY : x ∉ Y := fun h => hxYb (Finset.mem_insert_of_mem h)
      have hyY : y ∉ Y := fun h => hyYb (Finset.mem_insert_of_mem h)
      obtain ⟨v, hv_mem, hv_Y⟩ := hY_sep x hxA y hyB hxY hyY w'
      exact ⟨v, hw' ▸ hv_mem, Finset.mem_insert_of_mem hv_Y⟩
  -- Step 5: Contradiction argument
  -- |insert a Y| ≥ k and |insert b Y| ≥ k
  have hYa_ge : k ≤ (insert a Y).card := minABSeparatorSize_le G A B _ hYa_sep
  have hYb_ge : k ≤ (insert b Y).card := minABSeparatorSize_le G A B _ hYb_sep
  -- If both = k, then insert a Y = A or B, insert b Y = A or B
  -- Since a ∈ insert a Y and a ∉ B → insert a Y = A
  -- Since b ∈ insert b Y and b ∉ A → insert b Y = B
  -- Then Y ⊆ A ∩ B = ∅, but |Y| ≥ k-1 ≥ 1. Contradiction.
  -- So at least one of |insert a Y|, |insert b Y| > k, giving |Y| ≥ k.
  have hY_ge_k : k ≤ G'.minABSeparatorSize A B := by
    rw [← hY_card]
    -- Suppose |Y| < k for contradiction
    by_contra hlt
    push_neg at hlt
    -- |insert a Y| ≤ |Y| + 1 ≤ k, combined with ≥ k, gives = k
    have hYa_eq : (insert a Y).card = k := by
      have := Finset.card_insert_le a Y; omega
    have hYb_eq : (insert b Y).card = k := by
      have := Finset.card_insert_le b Y; omega
    -- By hall, insert a Y = A or B, insert b Y = A or B
    have hYa_AB := hall (insert a Y) hYa_sep hYa_eq
    have hYb_AB := hall (insert b Y) hYb_sep hYb_eq
    -- a ∈ insert a Y and a ∉ B → insert a Y ≠ B → insert a Y = A
    have hYa_eq_A : (↑(insert a Y) : Set V) = ↑A := by
      rcases hYa_AB with h | h
      · exact h
      · exfalso; have : a ∈ (↑B : Set V) := h ▸ Finset.mem_coe.mpr (Finset.mem_insert_self a Y)
        exact haB (Finset.mem_coe.mp this)
    -- b ∈ insert b Y and b ∉ A → insert b Y ≠ A → insert b Y = B
    have hYb_eq_B : (↑(insert b Y) : Set V) = ↑B := by
      rcases hYb_AB with h | h
      · exfalso; have : b ∈ (↑A : Set V) := h ▸ Finset.mem_coe.mpr (Finset.mem_insert_self b Y)
        exact hbA (Finset.mem_coe.mp this)
      · exact h
    -- Y ⊆ insert a Y = A and Y ⊆ insert b Y = B, so Y ⊆ A ∩ B = ∅
    -- Every v ∈ Y is in both A and B (contradiction with disjointness)
    have hY_sub_A : ∀ v ∈ Y, v ∈ A := by
      intro v hv
      have : (v : V) ∈ (↑(insert a Y) : Set V) := Finset.mem_coe.mpr (Finset.mem_insert_of_mem hv)
      rw [hYa_eq_A] at this; exact Finset.mem_coe.mp this
    have hY_sub_B : ∀ v ∈ Y, v ∈ B := by
      intro v hv
      have : (v : V) ∈ (↑(insert b Y) : Set V) := Finset.mem_coe.mpr (Finset.mem_insert_of_mem hv)
      rw [hYb_eq_B] at this; exact Finset.mem_coe.mp this
    -- Y ⊆ A ∩ B = ∅, so Y = ∅
    have hY_empty : Y = ∅ := by
      by_contra hne
      obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hne
      exact Finset.disjoint_left.mp hdisj (hY_sub_A v hv) (hY_sub_B v hv)
    -- |Y| = 0, so |insert a Y| = 1, but = k ≥ 2. Contradiction.
    have : Y.card = 0 := by rw [hY_empty]; simp
    have : (insert a Y).card = 1 := by rw [hY_empty]; simp
    omega
  -- Step 6: Apply IH on G' — edge count strictly decreased
  -- G' has fewer edges: we deleted one edge s(a,b) which was in G.edgeSet
  have hadj_edge : s(a, b) ∈ G.edgeSet := (mem_edgeSet G).mpr hadj
  have hG'_fewer : G'.edgeFinset.card < G.edgeFinset.card := by
    have h2 : 0 < G.edgeFinset.card := by
      have : s(a, b) ∈ G.edgeFinset := mem_edgeFinset.mpr hadj
      exact Finset.card_pos.mpr ⟨_, this⟩
    have h1 : G'.edgeFinset.card ≤ G.edgeFinset.card - 1 := by
      -- G'.edgeFinset ⊆ G.edgeFinset (since G' ≤ G)
      -- and s(a,b) ∈ G.edgeFinset \ G'.edgeFinset
      have hsub : G'.edgeFinset ⊆ G.edgeFinset :=
        edgeFinset_mono hG'_le
      have hmiss : s(a, b) ∉ G'.edgeFinset := by
        rw [mem_edgeFinset]
        simp only [hG'_def, edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
        tauto
      exact Nat.le_sub_one_of_lt (Finset.card_lt_card ⟨hsub, fun h => hmiss (h (mem_edgeFinset.mpr hadj))⟩)
    omega
  -- minABSep(G') ≥ k, so minABSep(G') ≠ 0
  have hk'_ne : G'.minABSeparatorSize A B ≠ 0 := by omega
  -- Apply IH to get k' ABConnector paths in G'
  obtain ⟨conn'⟩ := ih G' hG'_fewer hk'_ne
  -- Transfer ABConnector from G' to G via Walk.mapLe (G' ≤ G)
  set k' := G'.minABSeparatorSize A B with hk'_def
  have hk'_ge : k ≤ k' := hY_ge_k
  -- Truncate conn' from k' paths to k paths
  have conn_trunc := conn'.truncate k hk'_ge
  -- Transfer walks from G' to G, preserving ABConnector structure
  exact ⟨{
    src := conn_trunc.src
    dst := conn_trunc.dst
    walk := fun i => Walk.mapLe hG'_le (conn_trunc.walk i)
    isPath := fun i => (Walk.mapLe_isPath hG'_le).mpr (conn_trunc.isPath i)
    src_mem := conn_trunc.src_mem
    dst_mem := conn_trunc.dst_mem
    touchA := fun i v hv hvA => by
      rw [Walk.support_mapLe_eq_support] at hv
      exact conn_trunc.touchA i v hv hvA
    touchB := fun i v hv hvB => by
      rw [Walk.support_mapLe_eq_support] at hv
      exact conn_trunc.touchB i v hv hvB
    disjoint := fun i j hij v hvi hvj => by
      rw [Walk.support_mapLe_eq_support] at hvi hvj
      exact conn_trunc.disjoint i j hij v hvi hvj
  }⟩

/-- **Menger's theorem — hard direction, disjoint case, k ≥ 2** (Diestel Thm 3.3.1):
When A ∩ B = ∅ and the minimum A-B separator has size k ≥ 2, there exist k
vertex-disjoint A-B paths. Following Diestel's "Second proof" (p.51-52):

**Case 1** ("good separator"): There exists a minimum separator X with X ≠ A, X ≠ B.
  Split G into G_A = G[C_A ∪ X] and G_B = G[C_B ∪ X], apply IH to each half,
  and concatenate paths through X.

**Case 2** ("all separators are A or B"): Every minimum separator equals A or B.
  Then |A| = |B| = k and each a ∈ A has a neighbor in B. Construct k disjoint
  single-edge A-B paths directly (Diestel p.51-52, final case).

**Decomposition status**: The proof case-splits via `menger_good_separator_or_all_AB`:
- Case 1 uses: `menger_disjoint_paths_from_separator` (using ABConnector) + `menger_inductive_step` (proved).
  The `ih_vert` parameter (vertex-count IH on induced subgraphs) returns ABConnector.
- Case 2 uses: `menger_diestel_edge_deletion` (edge-count IH, proved) -/
theorem menger_hard_direction_disjoint_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hk : G.minABSeparatorSize A B ≠ 0)
    (hk2 : G.minABSeparatorSize A B ≠ 1)
    (hdisj : Disjoint A B)
    (ih_edge : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
      G'.edgeFinset.card < G.edgeFinset.card →
      G'.minABSeparatorSize A B ≠ 0 →
      Nonempty (G'.ABConnector A B (G'.minABSeparatorSize A B)))
    (ih_vert : ∀ (S : Finset V), S.card < Fintype.card V →
      ∀ (A' B' : Finset ↥(↑S : Set V)),
      (G.induce (↑S : Set V)).minABSeparatorSize A' B' ≠ 0 →
      Nonempty ((G.induce (↑S : Set V)).ABConnector A' B'
        ((G.induce (↑S : Set V)).minABSeparatorSize A' B'))) :
    Nonempty (G.ABConnector A B (G.minABSeparatorSize A B)) := by
  -- Case split: either a "good" separator exists, or all min separators are A or B
  rcases menger_good_separator_or_all_AB G A B with
    ⟨X, hX_sep, hX_card, hX_ne_A, hX_ne_B⟩ | hall
  · -- Case 1: Good separator X ≠ A, X ≠ B exists → graph splitting + IH
    -- Get k disjoint A-X and X-B paths with all structural properties
    obtain ⟨pA, pB, hdi, hsi, haX, hbX, hab, htouchA_pA, htouchB_pB⟩ :=
      menger_disjoint_paths_from_separator G A B X hX_sep hX_card hX_ne_A hX_ne_B hdisj hk ih_vert
    -- Concatenate through X to get k disjoint A-B paths as ABConnector
    exact menger_inductive_step_conn G A B X hX_card hX_sep hdisj pA pB hdi hsi haX hbX hab htouchA_pA htouchB_pB
  · -- Case 2: All min separators are A or B → Diestel edge deletion + ABConnector IH
    exact menger_diestel_edge_deletion G A B hk hk2 hdisj hall ih_edge

/-- **Menger's theorem — hard direction, disjoint case** (Diestel Thm 3.3.1):
When A ∩ B = ∅ and the minimum A-B separator has size k ≥ 1, there exist k
vertex-disjoint A-B paths. The k = 1 case is proved directly (∅ is not a
separator, so an A-B walk exists; convert to path). The k ≥ 2 case is
delegated to `menger_hard_direction_disjoint_ge_two`. -/
theorem menger_hard_direction_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hk : G.minABSeparatorSize A B ≠ 0)
    (hdisj : Disjoint A B)
    (ih_edge : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
      G'.edgeFinset.card < G.edgeFinset.card →
      G'.minABSeparatorSize A B ≠ 0 →
      Nonempty (G'.ABConnector A B (G'.minABSeparatorSize A B)))
    (ih_vert : ∀ (S : Finset V), S.card < Fintype.card V →
      ∀ (A' B' : Finset ↥(↑S : Set V)),
      (G.induce (↑S : Set V)).minABSeparatorSize A' B' ≠ 0 →
      Nonempty ((G.induce (↑S : Set V)).ABConnector A' B'
        ((G.induce (↑S : Set V)).minABSeparatorSize A' B'))) :
    Nonempty (G.ABConnector A B (G.minABSeparatorSize A B)) := by
  by_cases hk1 : G.minABSeparatorSize A B = 1
  · -- Case k = 1: ∅ is not a separator (since minABSep ≥ 1), so ∃ walk from A to B.
    rw [hk1]
    have hnosep : ¬ G.IsABSeparator A B ∅ := by
      intro hsep
      have := minABSeparatorSize_le G A B ∅ hsep
      simp at this; omega
    simp only [IsABSeparator, not_forall] at hnosep
    obtain ⟨a, ha, b, hb, _, _, w, hw⟩ := hnosep
    -- Build ABConnector for k = 1 with truncated path
    -- Use Walk.toPath then truncateAtFirstMem/truncateAtLastMem for touchA/touchB
    -- For k = 1 with Disjoint A B, there's only one path and no disjointness issue.
    -- The simplest: truncate the path at first B-vertex (touchB) and last A-vertex (touchA).
    -- For a single path, any vertex on it that's in A must equal the source (after truncation).
    let p := w.toPath
    -- First truncate at first B hit
    let ⟨⟨b', wb'⟩, hb'B, hwb'_path, _, hwb'_touchB⟩ :=
      Walk.truncateAtFirstMem B (p : G.Walk a b) p.2 hb
    -- Then truncate at last A hit on the result
    let ⟨⟨a', wa'⟩, ha'A, hwa'_path, hwa'_sub, hwa'_touchA⟩ :=
      Walk.truncateAtLastMem A wb' hwb'_path ha
    -- Now wa' goes from a' ∈ A to b' ∈ B, touches A only at a', touches B only at b'
    -- But we need touchB for wa': vertices on wa' that are in B = b'.
    -- wa' is a suffix of wb'. wb' touches B only at b' (endpoint).
    -- wa' support ⊆ wb' support (from hwa'_sub). So any B vertex on wa' is on wb', hence = b'.
    have hwa'_touchB' : ∀ u ∈ wa'.support, u ∈ B → u = b' := by
      intro u hu huB; exact hwb'_touchB u (hwa'_sub hu) huB
    exact ⟨{ src := fun _ => a'
             dst := fun _ => b'
             walk := fun _ => wa'
             isPath := fun _ => hwa'_path
             src_mem := fun _ => ha'A
             dst_mem := fun _ => hb'B
             touchA := fun _ v hv hvA => hwa'_touchA v hv hvA
             touchB := fun _ v hv hvB => hwa'_touchB' v hv hvB
             disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij }⟩
  · -- Case k ≥ 2: requires graph splitting (edge-count induction for Case 2)
    exact menger_hard_direction_disjoint_ge_two G A B hk hk1 hdisj ih_edge ih_vert

/-- **Menger's theorem — hard direction, strong ABConnector form**
(Diestel Thm 3.3.1, internal strong form).

Returns an `ABConnector` (full vertex-disjointness) rather than `VertexDisjointPaths`
(internal disjointness only). Universally quantified over the vertex type `W` to
enable strong induction on the combined measure `|V| + |E|` (parameter `m`).

This is the internal strong form used both for the standard `menger_hard_direction`
(via `ABConnector.toVertexDisjointPaths`) and for `menger_hard_direction_AB`
(direct ABConnector access, used in the s-t Menger reduction).

The proof uses strong induction on `|V| + |E|`, universally quantified over `W`,
with two induction hypotheses:

- **Edge-count IH** (same vertex type, fewer edges): For Case 2 (Diestel edge
  deletion), used when every minimum separator equals A or B.
- **Vertex-count IH** (induced subgraph, fewer vertices): For Case 1 (graph
  splitting), used when a separator X with X ≠ A, X ≠ B exists.

Within the combined induction, single split on A ∩ B handles both nonempty and
disjoint cases, producing ABConnector throughout (stronger than VertexDisjointPaths). -/
theorem menger_hard_AB_strong : ∀ (m : Nat) (W : Type u) [Fintype W] [DecidableEq W]
    (G₀ : SimpleGraph W) [DecidableRel G₀.Adj],
    Fintype.card W + G₀.edgeFinset.card = m →
    ∀ (A₀ B₀ : Finset W),
    G₀.minABSeparatorSize A₀ B₀ ≠ 0 →
    Nonempty (G₀.ABConnector A₀ B₀ (G₀.minABSeparatorSize A₀ B₀)) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih_combined =>
    intro W _ _ G₀ _ hm A₀ B₀ hk₀
    -- Single case split on A₀ ∩ B₀ (no inner induction needed for ABConnector)
    rcases Finset.disjoint_or_nonempty_inter A₀ B₀ with hdisj | ⟨x, hx⟩
    · -- A₀ ∩ B₀ = ∅: the deep combinatorial case
      -- Edge-count IH: same vertex type W, fewer edges → ABConnector (for Case 2)
      have ih_edge_G₀ : ∀ (G' : SimpleGraph W) [DecidableRel G'.Adj],
          G'.edgeFinset.card < G₀.edgeFinset.card →
          G'.minABSeparatorSize A₀ B₀ ≠ 0 →
          Nonempty (G'.ABConnector A₀ B₀ (G'.minABSeparatorSize A₀ B₀)) := by
        intro G' _ hlt hk_G'
        exact ih_combined (Fintype.card W + G'.edgeFinset.card) (by omega) W G' rfl A₀ B₀ hk_G'
      -- Vertex-count IH: induced subgraph on S ⊊ W → ABConnector (for Case 1)
      have ih_vert_G₀ : ∀ (S : Finset W), S.card < Fintype.card W →
          ∀ (A'' B'' : Finset ↥(↑S : Set W)),
          (G₀.induce (↑S : Set W)).minABSeparatorSize A'' B'' ≠ 0 →
          Nonempty ((G₀.induce (↑S : Set W)).ABConnector A'' B''
            ((G₀.induce (↑S : Set W)).minABSeparatorSize A'' B'')) := by
        intro S hS_card A'' B'' hk_S
        have hcard_S : Fintype.card ↥(↑S : Set W) < Fintype.card W := by
          calc Fintype.card ↥(↑S : Set W)
              = S.card := by simp [Fintype.card_coe]
            _ < Fintype.card W := hS_card
        have hedge_S : (G₀.induce (↑S : Set W)).edgeFinset.card ≤ G₀.edgeFinset.card := by
          have h_emb := (Embedding.induce (↑S : Set W) : (G₀.induce (↑S : Set W)) ↪g G₀).mapEdgeSet
          have h1 : Fintype.card ↥(G₀.induce (↑S : Set W)).edgeSet ≤ Fintype.card ↥G₀.edgeSet :=
            Fintype.card_le_of_embedding h_emb
          simp only [Set.Finite.toFinset_setOf, ← Set.toFinset_card] at h1 ⊢
          convert h1 using 1 <;> simp [edgeFinset]
        have hmeasure : Fintype.card ↥(↑S : Set W) + (G₀.induce (↑S : Set W)).edgeFinset.card < m := by
          omega
        exact ih_combined _ hmeasure ↥(↑S : Set W) (G₀.induce (↑S : Set W)) rfl A'' B'' hk_S
      -- menger_hard_direction_disjoint now returns ABConnector directly
      exact menger_hard_direction_disjoint G₀ A₀ B₀ hk₀ hdisj ih_edge_G₀ ih_vert_G₀
    · -- x ∈ A₀ ∩ B₀: Diestel's G-x approach → ABConnector
      have hxA : x ∈ A₀ := (Finset.mem_inter.mp hx).1
      have hxB : x ∈ B₀ := (Finset.mem_inter.mp hx).2
      -- Separator size relation: k ≤ k' + 1 where k' = minABSep(A\x, B\x)
      have hsep := minABSeparatorSize_erase_succ G₀ A₀ B₀ x
      set k := G₀.minABSeparatorSize A₀ B₀ with hk_def
      by_cases hk1 : k = 1
      · -- k = 1: trivial ABConnector with single {x} path
        rw [hk1]
        exact ⟨{ src := fun _ => x
                 dst := fun _ => x
                 walk := fun _ => Walk.nil
                 isPath := fun _ => Walk.IsPath.nil
                 src_mem := fun _ => hxA
                 dst_mem := fun _ => hxB
                 touchA := fun _ v hv _ => by simp at hv; exact hv
                 touchB := fun _ v hv _ => by simp at hv; exact hv
                 disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij }⟩
      · -- k ≥ 2: use G-x with outer IH
        -- G' = G₀.induce (Finset.univ.erase x)
        let S := Finset.univ.erase x
        -- S has fewer vertices
        have hS_card_lt : Fintype.card ↥(↑S : Set W) < Fintype.card W := by
          have hne : Fintype.card W ≠ 0 := Fintype.card_pos_iff.mpr ⟨x⟩ |>.ne'
          have : S.card < Fintype.card W := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ x)]
            exact Nat.pred_lt hne
          calc Fintype.card ↥(↑S : Set W)
              = S.card := by simp [Fintype.card_coe]
            _ < Fintype.card W := this
        have hedge_S : (G₀.induce (↑S : Set W)).edgeFinset.card ≤ G₀.edgeFinset.card := by
          have h_emb := (Embedding.induce (↑S : Set W) : (G₀.induce (↑S : Set W)) ↪g G₀).mapEdgeSet
          have h1 : Fintype.card ↥(G₀.induce (↑S : Set W)).edgeSet ≤ Fintype.card ↥G₀.edgeSet :=
            Fintype.card_le_of_embedding h_emb
          simp only [Set.Finite.toFinset_setOf, ← Set.toFinset_card] at h1 ⊢
          convert h1 using 1 <;> simp [edgeFinset]
        have hmeasure : Fintype.card ↥(↑S : Set W) + (G₀.induce (↑S : Set W)).edgeFinset.card < m := by
          omega
        -- x ∉ S
        have hx_not_S : x ∉ (↑S : Set W) := by
          simp [S, Finset.mem_coe, Finset.mem_erase]
        -- Convert A₀ and B₀ to subtype Finsets
        -- Every v ∈ A₀.erase x is in S (since v ≠ x and v ∈ Finset.univ)
        have h_erase_sub : ∀ v, v ≠ x → v ∈ (↑S : Set W) :=
          fun v hne => Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ v⟩)
        let A' : Finset ↥(↑S : Set W) := (A₀.erase x).subtype (· ∈ (↑S : Set W))
        let B' : Finset ↥(↑S : Set W) := (B₀.erase x).subtype (· ∈ (↑S : Set W))
        let G' := G₀.induce (↑S : Set W)
        set k' := G'.minABSeparatorSize A' B' with hk'_def
        -- minABSep(G', A', B') ≥ k - 1 (via separator size equality)
        -- Since S = univ \ {x} contains all vertices except x, and A' = (A₀\{x}).subtype,
        -- any A'-B' separator in G' projects to an (A₀\{x})-(B₀\{x}) separator in G₀
        -- of the same cardinality, and vice versa. So k' = minABSep(G₀, A₀\{x}, B₀\{x}).
        -- Combined with hsep (k ≤ minABSep(A₀\{x}, B₀\{x}) + 1), we get k - 1 ≤ k'.
        have hk'_ge : k - 1 ≤ k' := by
          -- Strategy: show T'_V ∪ {x} separates A₀ from B₀ in G₀, with |T'_V ∪ {x}| = k' + 1.
          -- Then k = minABSep(G₀, A₀, B₀) ≤ k' + 1, so k - 1 ≤ k'.
          suffices h_le : k ≤ k' + 1 by omega
          -- Get a minimum A'-B' separator in G'
          obtain ⟨T', hT'_sep, hT'_card⟩ := minABSeparatorSize_spec G' A' B'
          -- Project T' to G₀
          let T'_V : Finset W := T'.map (Function.Embedding.subtype _)
          have hT'V_card : T'_V.card = T'.card := Finset.card_map _
          -- x ∉ T'_V (since all elements of T'_V are in S, and x ∉ S)
          have hx_not_T'V : x ∉ T'_V := by
            intro hmem
            rw [Finset.mem_map] at hmem
            obtain ⟨⟨v, hv_S⟩, _, hv_eq⟩ := hmem
            exact hx_not_S (hv_eq ▸ hv_S)
          -- |T'_V ∪ {x}| = k' + 1
          have hcard_union : (T'_V ∪ {x}).card = k' + 1 := by
            rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hx_not_T'V),
              Finset.card_singleton, hT'V_card, hT'_card]
          -- Show T'_V ∪ {x} separates A₀ from B₀ in G₀
          have h_sep_union : G₀.IsABSeparator A₀ B₀ (T'_V ∪ {x}) := by
            intro a ha b hb ha_not hb_not w
            -- a ∉ T'_V ∪ {x} means a ∉ T'_V and a ≠ x
            rw [Finset.mem_union, Finset.mem_singleton] at ha_not hb_not
            push Not at ha_not hb_not
            have ha_ne_x := ha_not.2
            have hb_ne_x := hb_not.2
            have ha_not_T'V := ha_not.1
            have hb_not_T'V := hb_not.1
            -- Case split: does the walk pass through x?
            by_cases hx_walk : x ∈ w.support
            · -- x is on the walk and x ∈ T'_V ∪ {x}
              exact ⟨x, hx_walk, Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)⟩
            · -- Walk avoids x, so all vertices are in S
              have hw_in_S : ∀ u ∈ w.support, u ∈ (↑S : Set W) := by
                intro u hu
                exact h_erase_sub u (fun h => hx_walk (h ▸ hu))
              -- Convert the walk to G'
              let w' := w.induce (↑S : Set W) hw_in_S
              -- a ∈ A' (a ∈ A₀, a ≠ x, a ∈ S)
              have ha_S := hw_in_S a (Walk.start_mem_support w)
              have hb_S := hw_in_S b (Walk.end_mem_support w)
              have ha_A' : (⟨a, ha_S⟩ : ↥(↑S : Set W)) ∈ A' := by
                rw [Finset.mem_subtype]; exact Finset.mem_erase.mpr ⟨ha_ne_x, ha⟩
              have hb_B' : (⟨b, hb_S⟩ : ↥(↑S : Set W)) ∈ B' := by
                rw [Finset.mem_subtype]; exact Finset.mem_erase.mpr ⟨hb_ne_x, hb⟩
              -- a ∉ T' and b ∉ T'
              have ha_not_T' : (⟨a, ha_S⟩ : ↥(↑S : Set W)) ∉ T' := by
                intro h_mem
                exact ha_not_T'V (Finset.mem_map.mpr ⟨⟨a, ha_S⟩, h_mem, rfl⟩)
              have hb_not_T' : (⟨b, hb_S⟩ : ↥(↑S : Set W)) ∉ T' := by
                intro h_mem
                exact hb_not_T'V (Finset.mem_map.mpr ⟨⟨b, hb_S⟩, h_mem, rfl⟩)
              -- Apply separator property in G'
              have h_hit := hT'_sep ⟨a, ha_S⟩ ha_A' ⟨b, hb_S⟩ hb_B' ha_not_T' hb_not_T' w'
              obtain ⟨⟨u, hu_S⟩, hu_walk', hu_T'⟩ := h_hit
              -- u ∈ T'_V
              have hu_T'V : u ∈ T'_V := Finset.mem_map.mpr ⟨⟨u, hu_S⟩, hu_T', rfl⟩
              -- u ∈ w.support (since map_induce gives back the original walk)
              have hu_walk : u ∈ w.support := by
                have h_map := Walk.map_induce (s := (↑S : Set W)) w hw_in_S
                have h_supp := Walk.support_map (Embedding.induce (↑S : Set W) (G := G₀)).toHom w'
                -- h_supp : (w'.map ..).support = List.map Subtype.val w'.support
                -- h_map : w'.map ... = w, so (w'.map ..).support = w.support
                rw [h_map] at h_supp
                -- h_supp : w.support = List.map Subtype.val w'.support
                exact h_supp ▸ (List.mem_map_of_mem (f := (⇑(Embedding.induce (↑S : Set W) (G := G₀)).toHom)) hu_walk')
              exact ⟨u, hu_walk, Finset.mem_union_left _ hu_T'V⟩
          -- Conclude: k ≤ (T'_V ∪ {x}).card = k' + 1
          calc k = G₀.minABSeparatorSize A₀ B₀ := hk_def
            _ ≤ (T'_V ∪ {x}).card := minABSeparatorSize_le G₀ A₀ B₀ _ h_sep_union
            _ = k' + 1 := hcard_union
        by_cases hk'zero : k' = 0
        · -- k' = 0 means k ≤ 1, combined with k ≠ 1, gives k = 0, contradiction
          omega
        · -- k' ≥ 1: IH on G' gives ABConnector with k' paths
          obtain ⟨conn'⟩ := ih_combined _ hmeasure ↥(↑S : Set W) G' rfl A' B' hk'zero
          -- Truncate to k-1 paths
          let conn_trunc := conn'.truncate (k - 1) hk'_ge
          -- Lift ABConnector from G' to G₀
          -- Paths in G' have support in ↥S, so they avoid x.
          let conn_lifted : G₀.ABConnector (A₀.erase x) (B₀.erase x) (k - 1) :=
            { src := fun i => ↑(conn_trunc.src i)
              dst := fun i => ↑(conn_trunc.dst i)
              walk := fun i => walk_of_induce_walk (conn_trunc.walk i)
              isPath := fun i =>
                Walk.map_isPath_of_injective Subtype.val_injective (conn_trunc.isPath i)
              src_mem := fun i => by
                have := conn_trunc.src_mem i; rw [Finset.mem_subtype] at this; exact this
              dst_mem := fun i => by
                have := conn_trunc.dst_mem i; rw [Finset.mem_subtype] at this; exact this
              touchA := fun i v hv hvA => by
                have hsupp : (walk_of_induce_walk (conn_trunc.walk i)).support =
                    List.map Subtype.val (conn_trunc.walk i).support :=
                  Walk.support_map (Embedding.induce (↑S : Set W)).toHom (conn_trunc.walk i)
                rw [hsupp, List.mem_map] at hv
                obtain ⟨⟨u, hu_S⟩, hu_walk, rfl⟩ := hv
                have hu_A' : (⟨u, hu_S⟩ : ↥(↑S : Set W)) ∈ A' := by
                  rw [Finset.mem_subtype]; exact hvA
                exact congrArg Subtype.val (conn_trunc.touchA i ⟨u, hu_S⟩ hu_walk hu_A')
              touchB := fun i v hv hvB => by
                have hsupp : (walk_of_induce_walk (conn_trunc.walk i)).support =
                    List.map Subtype.val (conn_trunc.walk i).support :=
                  Walk.support_map (Embedding.induce (↑S : Set W)).toHom (conn_trunc.walk i)
                rw [hsupp, List.mem_map] at hv
                obtain ⟨⟨u, hu_S⟩, hu_walk, rfl⟩ := hv
                have hu_B' : (⟨u, hu_S⟩ : ↥(↑S : Set W)) ∈ B' := by
                  rw [Finset.mem_subtype]; exact hvB
                exact congrArg Subtype.val (conn_trunc.touchB i ⟨u, hu_S⟩ hu_walk hu_B')
              disjoint := fun i j hij v hvi hvj => by
                have hvi' : v ∈ List.map Subtype.val (conn_trunc.walk i).support := by
                  have := Walk.support_map (Embedding.induce (↑S : Set W)).toHom (conn_trunc.walk i)
                  exact this ▸ hvi
                have hvj' : v ∈ List.map Subtype.val (conn_trunc.walk j).support := by
                  have := Walk.support_map (Embedding.induce (↑S : Set W)).toHom (conn_trunc.walk j)
                  exact this ▸ hvj
                rw [List.mem_map] at hvi' hvj'
                obtain ⟨ui, hui, rfl⟩ := hvi'
                obtain ⟨uj, huj, huj_eq⟩ := hvj'
                have heq : uj = ui := Subtype.val_injective huj_eq
                rw [heq] at huj
                exact conn_trunc.disjoint i j hij ui hui huj }
          -- Paths avoid x (since x ∉ S and all path vertices are in S)
          have h_avoid_x : ∀ i, x ∉ (conn_lifted.walk i).support := by
            intro i hx_mem
            -- All vertices on conn_lifted.walk i are projections of subtype vertices in S
            -- So every vertex on the walk is in S. But x ∉ S. Contradiction.
            have hsupp := Walk.support_map (Embedding.induce (↑S : Set W)).toHom (conn_trunc.walk i)
            -- hx_mem : x ∈ walk_of_induce_walk support = List.map Subtype.val support
            have hmem : x ∈ List.map (⇑(Embedding.induce (↑S : Set W)).toHom) (conn_trunc.walk i).support :=
              hsupp ▸ hx_mem
            rw [List.mem_map] at hmem
            obtain ⟨⟨u, hu_S⟩, _, heq⟩ := hmem
            exact hx_not_S (heq ▸ hu_S)
          -- Add trivial path {x} via abConnector_cons_from_erase_avoiding_x
          have hk_eq : k - 1 + 1 = k := by omega
          rw [← hk_eq]
          exact ⟨abConnector_cons_from_erase_avoiding_x G₀ A₀ B₀ (k - 1) x hxA hxB
            conn_lifted h_avoid_x⟩

/-- **Menger's theorem — hard direction** (Diestel Thm 3.3.1):
There exist `minABSeparatorSize G A B` many vertex-disjoint A-B paths.

Wrapper around `menger_hard_AB_strong`: handles the `minSep = 0` case via
`vertexDisjointPaths_zero` and otherwise converts ABConnector to VertexDisjointPaths. -/
theorem menger_hard_direction (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    Nonempty (G.VertexDisjointPaths A B (G.minABSeparatorSize A B)) := by
  by_cases hk : G.minABSeparatorSize A B = 0
  · rw [hk]; exact vertexDisjointPaths_zero G A B
  · exact (menger_hard_AB_strong _ V G rfl A B hk).map ABConnector.toVertexDisjointPaths

/-- **Menger's theorem — hard direction, ABConnector form** (Diestel Thm 3.3.1):
When `minABSeparatorSize G A B ≠ 0`, there exist `minABSeparatorSize G A B` many
**fully** vertex-disjoint A-B paths (ABConnector — stronger than VertexDisjointPaths,
adds `touchA`/`touchB` plus full support disjointness). Used in the s-t Menger
reduction where full disjointness is needed for the projection argument. -/
theorem menger_hard_direction_AB (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hk : G.minABSeparatorSize A B ≠ 0) :
    Nonempty (G.ABConnector A B (G.minABSeparatorSize A B)) :=
  menger_hard_AB_strong _ V G rfl A B hk

/-! ## Maximum disjoint paths -/

/-- The **maximum number of vertex-disjoint A-B paths**. Defined to equal
the minimum A-B separator size; Menger's theorem asserts this equals
the combinatorial maximum, i.e. there exist this many vertex-disjoint
A-B paths (`maxVertexDisjointABPaths_spec`). -/
noncomputable def maxVertexDisjointABPaths (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) : Nat :=
  G.minABSeparatorSize A B

/-- The maximum is attained: there exist `maxVertexDisjointABPaths` many
vertex-disjoint A-B paths. This is the hard direction of Menger's theorem
(existence of paths matching the minimum separator size). -/
theorem maxVertexDisjointABPaths_spec (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) :
    Nonempty
      (G.VertexDisjointPaths A B
        (G.maxVertexDisjointABPaths A B)) := by
  exact menger_hard_direction G A B

/-! ## Easy direction -/

/-- **Easy direction of Menger's theorem**: The number of vertex-disjoint
A-B paths cannot exceed any A-B separator size. Holds definitionally
since `maxVertexDisjointABPaths` is defined as `minABSeparatorSize`. -/
theorem menger_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    G.maxVertexDisjointABPaths A B <=
      G.minABSeparatorSize A B := by
  rfl

/-! ## Menger's theorem -/

/-- **Menger's theorem** (Diestel Thm 3.3.1): The maximum number of
vertex-disjoint A-B paths equals the minimum size of an A-B separator.

Holds definitionally since `maxVertexDisjointABPaths` is defined as
`minABSeparatorSize`. The hard content is in `maxVertexDisjointABPaths_spec`. -/
theorem menger (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    G.maxVertexDisjointABPaths A B =
      G.minABSeparatorSize A B := by
  rfl

/-! ## Corollaries -/

/-- If every A-B separator has size at least k, then there exist k
vertex-disjoint A-B paths. -/
theorem exists_vertexDisjointPaths_of_separator_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (k : Nat)
    (h : forall S : Finset V,
      G.IsABSeparator A B S -> k <= S.card) :
    Nonempty (G.VertexDisjointPaths A B k) := by
  have hle : k <= G.maxVertexDisjointABPaths A B := by
    simp only [maxVertexDisjointABPaths]
    exact le_csInf (abSeparatorSizes_nonempty G A B)
      (fun n hn => by
        simp only [abSeparatorSizes, Set.mem_setOf_eq] at hn
        match hn with
        | Exists.intro S (And.intro hS hc) => subst hc; exact h S hS)
  match maxVertexDisjointABPaths_spec G A B with
  | Nonempty.intro dp =>
    exact Nonempty.intro
      { src := fun i => dp.src (Fin.castLE hle i)
        dst := fun i => dp.dst (Fin.castLE hle i)
        walk := fun i => dp.walk (Fin.castLE hle i)
        isPath := fun i => dp.isPath (Fin.castLE hle i)
        src_mem := fun i => dp.src_mem (Fin.castLE hle i)
        dst_mem := fun i => dp.dst_mem (Fin.castLE hle i)
        src_inj := dp.src_inj.comp (Fin.castLE_injective hle)
        dst_inj := dp.dst_inj.comp (Fin.castLE_injective hle)
        internal_disjoint := fun i j hij v hvi hnis hnid hvj hnjs hnjd =>
          dp.internal_disjoint _ _
            (fun heq => hij (Fin.castLE_injective hle heq))
            v hvi hnis hnid hvj hnjs hnjd }

/-- ABConnector form: if every A-B separator has size at least k AND there
exists at least one A-B separator (i.e., `minABSeparatorSize ≠ 0`), then there
exist k **fully** vertex-disjoint A-B paths (ABConnector). -/
theorem exists_ABConnector_of_separator_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (k : Nat) (hk : k ≠ 0)
    (h : ∀ S : Finset V, G.IsABSeparator A B S → k ≤ S.card) :
    Nonempty (G.ABConnector A B k) := by
  have hsep_ne : G.minABSeparatorSize A B ≠ 0 := by
    intro hzero
    obtain ⟨S, hS_sep, hS_card⟩ := minABSeparatorSize_spec G A B
    rw [hzero] at hS_card
    have := h S hS_sep
    rw [hS_card] at this
    omega
  have hle : k ≤ G.minABSeparatorSize A B := by
    simp only [minABSeparatorSize]
    exact le_csInf (abSeparatorSizes_nonempty G A B)
      (fun n hn => by
        simp only [abSeparatorSizes, Set.mem_setOf_eq] at hn
        obtain ⟨S, hS, rfl⟩ := hn
        exact h S hS)
  match menger_hard_direction_AB G A B hsep_ne with
  | Nonempty.intro conn =>
    exact ⟨conn.truncate k hle⟩

/-- If S is an N(s)-N(t) separator (in the set-Menger sense) and ¬G.Adj s t,
then S is an {s}-{t} separator with s ∉ S and t ∉ S.
The proof uses: every s-t walk has length ≥ 2, so w.tail.dropLast is a walk
from w.snd ∈ N(s) to w.tail.penultimate ∈ N(t), and this sub-walk hits S.
Since support of sub-walk ⊆ support of w, w hits S too. -/
private theorem nb_separator_implies_st_separator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) (hnadj : ¬G.Adj s t)
    (S : Finset V)
    (hS : G.IsABSeparator (G.neighborFinset s) (G.neighborFinset t) S) :
    s ∉ S → t ∉ S → G.IsABSeparator {s} {t} S := by
  intro hsS htS a ha b hb haS hbS w
  -- a = s, b = t from singleton membership
  have has : a = s := Finset.mem_singleton.mp ha
  have hbt : b = t := Finset.mem_singleton.mp hb
  subst has; subst hbt
  -- w is a walk from a to b; since ¬G.Adj a b, it has length ≥ 2
  -- hence w.tail is non-nil
  have hnil : ¬w.Nil := by
    intro hnil; exact hst (hnil.eq)
  have htnil : ¬w.tail.Nil := by
    intro htnil
    have hsnd_eq : w.snd = b := htnil.eq
    have hadj : G.Adj a w.snd := Walk.adj_snd hnil
    rw [hsnd_eq] at hadj; exact hnadj hadj
  -- w.snd ∈ N(a), w.tail.penultimate ∈ N(b)
  have hsnd_ns : w.snd ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a w.snd).mpr (Walk.adj_snd hnil)
  have hpen_nt : w.tail.penultimate ∈ G.neighborFinset b :=
    (G.mem_neighborFinset b w.tail.penultimate).mpr (G.adj_symm (Walk.adj_penultimate htnil))
  -- w.tail.dropLast is a walk from w.snd to w.tail.penultimate
  -- and is a subwalk of w
  have hsub := w.isSubwalk_rfl.tail.dropLast
  -- By walk_hits_separator, w.tail.dropLast hits S
  obtain ⟨v, hvm, hvs⟩ := walk_hits_separator hS hsnd_ns hpen_nt w.tail.dropLast
  exact ⟨v, hsub.support_subset hvm, hvs⟩

/-- If S is an N(s)-N(t) separator and ¬G.Adj s t, then S \ {s, t} is an
{s}-{t} separator (with s ∉ S\{s,t} and t ∉ S\{s,t}). Uses toPath to
ensure the hit vertex is an internal vertex (neither s nor t). -/
private theorem nb_sep_sdiff_is_st_sep
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) (hnadj : ¬G.Adj s t)
    (S : Finset V)
    (hS : G.IsABSeparator (G.neighborFinset s) (G.neighborFinset t) S) :
    G.IsABSeparator {s} {t} (S \ {s, t}) := by
  intro a ha b hb haT hbT w
  have has : a = s := Finset.mem_singleton.mp ha
  have hbt : b = t := Finset.mem_singleton.mp hb
  subst has; subst hbt
  -- Use toPath: convert walk to path, preserving endpoints
  let p : G.Walk a b := ↑w.toPath
  have hp_path : p.IsPath := w.toPath.2
  have hp_sub : p.support ⊆ w.support := Walk.support_toPath_subset w
  -- p is a path from s to t, has length ≥ 2 since ¬G.Adj s t
  have hnil : ¬p.Nil := by
    intro hnil; exact hst (hnil.eq)
  have htnil : ¬p.tail.Nil := by
    intro htnil
    exact hnadj (htnil.eq ▸ Walk.adj_snd hnil)
  -- p.snd ∈ N(s), p.tail.penultimate ∈ N(t)
  have hsnd_ns : p.snd ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a p.snd).mpr (Walk.adj_snd hnil)
  have hpen_nt : p.tail.penultimate ∈ G.neighborFinset b :=
    (G.mem_neighborFinset b p.tail.penultimate).mpr (G.adj_symm (Walk.adj_penultimate htnil))
  -- The sub-walk p.tail.dropLast hits S
  have hsub := p.isSubwalk_rfl.tail.dropLast
  obtain ⟨v, hvm, hvs⟩ := walk_hits_separator hS hsnd_ns hpen_nt p.tail.dropLast
  -- v ∈ p.support ⊆ w.support
  have hv_in_p : v ∈ p.support := hsub.support_subset hvm
  have hv_in_w : v ∈ w.support := hp_sub hv_in_p
  -- v ≠ s and v ≠ t because p is a path and v is an internal vertex
  -- v is in p.tail.dropLast.support ⊆ p.tail.support ⊆ p.support \ {first}
  -- and v is in p.dropLast.support ⊆ p.support \ {last}
  -- Since p is a path (no repeated vertices), v ≠ s and v ≠ t
  have hv_ne_s : v ≠ a := by
    intro heq; subst heq
    -- v = s, but v ∈ p.tail.dropLast.support
    -- p.tail.support = p.support.tail (by support_tail_of_not_nil)
    -- s is the head of p.support, so s ∉ p.support.tail (since p is a path → Nodup)
    have h_nodup := hp_path.support_nodup
    have h_eq := Walk.support_eq_cons p
    rw [h_eq] at h_nodup
    have hv_tail : v ∈ p.tail.support :=
      p.tail.isSubwalk_rfl.dropLast.support_subset hvm
    rw [p.support_tail_of_not_nil hnil] at hv_tail
    exact h_nodup.notMem hv_tail
  have hv_ne_t : v ≠ b := by
    intro heq; subst heq
    -- p.tail is a path (sub-path of p) and p.tail = p.tail.dropLast.concat (adj)
    have hp_tail_path := hp_path.tail
    have hadj_pen := Walk.adj_penultimate htnil
    -- p.tail.support = p.tail.dropLast.support.concat v (via concat_dropLast)
    have hconcat : p.tail = p.tail.dropLast.concat hadj_pen :=
      (Walk.concat_dropLast p.tail hadj_pen).symm
    have hsup : p.tail.support = p.tail.dropLast.support.concat v := by
      conv_lhs => rw [hconcat]; rw [Walk.support_concat]
    -- Since p.tail.support is Nodup, v ∉ p.tail.dropLast.support
    have h_nodup_tail := hp_tail_path.support_nodup
    rw [hsup] at h_nodup_tail
    exact ((List.nodup_concat _ _).mp h_nodup_tail).1 hvm
  exact ⟨v, hv_in_w, Finset.mem_sdiff.mpr ⟨hvs, by simp [hv_ne_s, hv_ne_t]⟩⟩

/-- Every N(s)-N(t) separator has size ≥ k when ¬G.Adj s t and every
{s}-{t} separator avoiding s,t has size ≥ k. Uses nb_sep_sdiff_is_st_sep:
S \ {s,t} is an {s}-{t} separator, so k ≤ |S\{s,t}| ≤ |S|. -/
private theorem nb_sep_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (k : Nat) (hst : s ≠ t) (hnadj : ¬G.Adj s t)
    (h : ∀ S : Finset V, s ∉ S → t ∉ S →
      G.IsABSeparator {s} {t} S → k ≤ S.card)
    (S : Finset V)
    (hS : G.IsABSeparator (G.neighborFinset s) (G.neighborFinset t) S) :
    k ≤ S.card := by
  have hst_sep := nb_sep_sdiff_is_st_sep G s t hst hnadj S hS
  have hbound := h (S \ {s, t})
    (by simp) (by simp [Ne.symm hst]) hst_sep
  exact le_trans hbound (Finset.card_le_card Finset.sdiff_subset)


/-! ### Vertex deletion (`G.deleteOne x`) for the peeling reduction

To handle the case where `N(s) ∩ N(t) ≠ ∅` in `nb_sep_bound_to_st_paths`,
we peel one vertex `x ∈ N(s) ∩ N(t)` at a time: take the trivial path
`s — x — t` as one of the `k` paths, and recurse with `k - 1` paths in
`G.deleteOne x` (the graph with `x`'s incident edges removed). Walks in
`G.deleteOne x` automatically avoid `x`, so they don't conflict with the
trivial path. -/

omit [Fintype V] [DecidableEq V] in
/-- Remove a vertex by removing all edges incident to it (kept on `V`). -/
def deleteOne (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ≠ x ∧ v ≠ x
  symm := fun u v ⟨h, hu, hv⟩ => ⟨h.symm, hv, hu⟩
  loopless := ⟨fun _ ⟨h, _, _⟩ => h.ne rfl⟩

instance deleteOne_decidableAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) : DecidableRel (G.deleteOne x).Adj := fun u v => by
  show Decidable (G.Adj u v ∧ u ≠ x ∧ v ≠ x)
  infer_instance

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem deleteOne_adj (G : SimpleGraph V) (x u v : V) :
    (G.deleteOne x).Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x := Iff.rfl

omit [Fintype V] [DecidableEq V] in
theorem deleteOne_le (G : SimpleGraph V) (x : V) : G.deleteOne x ≤ G :=
  fun _ _ h => h.1

/-- The neighborhood of `s ≠ x` in `G.deleteOne x` equals `N(s) \ {x}`. -/
theorem deleteOne_neighborFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {x s : V} (hsx : s ≠ x) :
    (G.deleteOne x).neighborFinset s = G.neighborFinset s \ {x} := by
  ext v
  simp only [mem_neighborFinset, deleteOne_adj, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hadj, _, hvx⟩; exact ⟨hadj, hvx⟩
  · rintro ⟨hadj, hvx⟩; exact ⟨hadj, hsx, hvx⟩

/-- Cardinality of `N(s) ∩ N(t)` strictly decreases on `G.deleteOne x` when
`x ∈ N(s) ∩ N(t)`. -/
theorem deleteOne_inter_card_lt {G : SimpleGraph V} [DecidableRel G.Adj]
    {x s t : V} (hsx : s ≠ x) (htx : t ≠ x)
    (hxs : x ∈ G.neighborFinset s) (hxt : x ∈ G.neighborFinset t) :
    ((G.deleteOne x).neighborFinset s ∩ (G.deleteOne x).neighborFinset t).card <
      (G.neighborFinset s ∩ G.neighborFinset t).card := by
  rw [deleteOne_neighborFinset hsx, deleteOne_neighborFinset htx]
  -- (N(s) \ {x}) ∩ (N(t) \ {x}) = (N(s) ∩ N(t)) \ {x}
  have heq : (G.neighborFinset s \ {x}) ∩ (G.neighborFinset t \ {x}) =
      (G.neighborFinset s ∩ G.neighborFinset t) \ {x} := by
    ext v; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
    tauto
  rw [heq]
  apply Finset.card_lt_card
  refine ⟨Finset.sdiff_subset, ?_⟩
  intro hsub
  have hx_int : x ∈ G.neighborFinset s ∩ G.neighborFinset t :=
    Finset.mem_inter.mpr ⟨hxs, hxt⟩
  have hx_sdiff : x ∈ (G.neighborFinset s ∩ G.neighborFinset t) \ {x} := hsub hx_int
  exact (Finset.mem_sdiff.mp hx_sdiff).2 (Finset.mem_singleton.mpr rfl)

omit [Fintype V] [DecidableEq V] in
/-- Lift a walk in `G.deleteOne x` to a walk in `G`. -/
def liftDeleteOneWalk {G : SimpleGraph V} {x : V} :
    ∀ {a b : V}, (G.deleteOne x).Walk a b → G.Walk a b
  | _, _, .nil => .nil
  | _, _, .cons hadj w => .cons hadj.1 (liftDeleteOneWalk w)

omit [Fintype V] [DecidableEq V] in
theorem liftDeleteOneWalk_support {G : SimpleGraph V} {x : V} :
    ∀ {a b : V} (w : (G.deleteOne x).Walk a b),
      (liftDeleteOneWalk w).support = w.support
  | _, _, .nil => rfl
  | _, _, .cons _ w => by
    simp only [liftDeleteOneWalk, Walk.support_cons,
      liftDeleteOneWalk_support w]

omit [Fintype V] [DecidableEq V] in
theorem liftDeleteOneWalk_isPath {G : SimpleGraph V} {x a b : V}
    (w : (G.deleteOne x).Walk a b) (hp : w.IsPath) :
    (liftDeleteOneWalk w).IsPath := by
  rw [Walk.isPath_def, liftDeleteOneWalk_support]
  exact hp.support_nodup

omit [Fintype V] [DecidableEq V] in
/-- Walks in `G.deleteOne x` avoid `x`. -/
theorem deleteOne_walk_avoids {G : SimpleGraph V} {x : V} :
    ∀ {a b : V} (_ : a ≠ x) (w : (G.deleteOne x).Walk a b),
      ∀ v ∈ w.support, v ≠ x
  | _, _, hax, .nil, v, hv => by
    simp only [Walk.support_nil, List.mem_singleton] at hv; exact hv ▸ hax
  | _, _, hax, .cons (v := b') hadj w', v, hv => by
    simp only [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv'
    · exact hax
    · exact deleteOne_walk_avoids hadj.2.2 w' v hv'

omit [Fintype V] [DecidableEq V] in
/-- Lift a walk `w` in `G` that avoids `x` to a walk in `G.deleteOne x`. -/
def walkOfAvoidsDeleteOne {G : SimpleGraph V} {x : V} :
    ∀ {a b : V} (w : G.Walk a b), a ≠ x → b ≠ x →
      (∀ v ∈ w.support, v ≠ x) → (G.deleteOne x).Walk a b
  | _, _, .nil, _, _, _ => .nil
  | _, _, .cons (v := c) hadj w', hax, _, hsupp => by
    have hcx : c ≠ x := hsupp c (by simp [Walk.support_cons])
    refine .cons ⟨hadj, hax, hcx⟩ ?_
    refine walkOfAvoidsDeleteOne w' hcx (hsupp _ ?_) ?_
    · -- end vertex is in support
      exact Walk.end_mem_support _
    · intro v hv
      exact hsupp v (by simp [Walk.support_cons, hv])

omit [Fintype V] [DecidableEq V] in
theorem walkOfAvoidsDeleteOne_support {G : SimpleGraph V} {x : V} :
    ∀ {a b : V} (w : G.Walk a b) (hax : a ≠ x) (hbx : b ≠ x)
      (hsupp : ∀ v ∈ w.support, v ≠ x),
      (walkOfAvoidsDeleteOne w hax hbx hsupp).support = w.support
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons _ w', _, _, _ => by
    simp only [walkOfAvoidsDeleteOne, Walk.support_cons,
      walkOfAvoidsDeleteOne_support w']

/-- Separator bound transfer: if every `N_G(s)-N_G(t)` separator in `G` has
size ≥ `k`, and `x ∈ N_G(s) ∩ N_G(t)`, then every
`N_{G\x}(s)-N_{G\x}(t)` separator in `G.deleteOne x` has size ≥ `k - 1`. -/
theorem deleteOne_sep_bound_transfer {G : SimpleGraph V} [DecidableRel G.Adj]
    {s t x : V} (hsx : s ≠ x) (htx : t ≠ x) (k : Nat)
    (hsep : ∀ S : Finset V,
      G.IsABSeparator (G.neighborFinset s) (G.neighborFinset t) S → k ≤ S.card) :
    ∀ S : Finset V,
      (G.deleteOne x).IsABSeparator
        ((G.deleteOne x).neighborFinset s) ((G.deleteOne x).neighborFinset t) S →
      k - 1 ≤ S.card := by
  intro S' hS'
  set S := insert x S' with hS_def
  have hS_sep : G.IsABSeparator (G.neighborFinset s) (G.neighborFinset t) S := by
    intro a haNs b hbNt haS hbS w
    have hax : a ≠ x := fun h => haS (h ▸ Finset.mem_insert_self x S')
    have hbx : b ≠ x := fun h => hbS (h ▸ Finset.mem_insert_self x S')
    have haS' : a ∉ S' := fun h => haS (Finset.mem_insert_of_mem h)
    have hbS' : b ∉ S' := fun h => hbS (Finset.mem_insert_of_mem h)
    have ha' : a ∈ (G.deleteOne x).neighborFinset s := by
      rw [deleteOne_neighborFinset hsx, Finset.mem_sdiff]
      exact ⟨haNs, fun h => hax (Finset.mem_singleton.mp h)⟩
    have hb' : b ∈ (G.deleteOne x).neighborFinset t := by
      rw [deleteOne_neighborFinset htx, Finset.mem_sdiff]
      exact ⟨hbNt, fun h => hbx (Finset.mem_singleton.mp h)⟩
    by_cases hwx : x ∈ w.support
    · exact ⟨x, hwx, Finset.mem_insert_self x S'⟩
    · -- w avoids x; transfer to G.deleteOne x via walkOfAvoidsDeleteOne
      have hsupp : ∀ v ∈ w.support, v ≠ x := fun v hv hvx => hwx (hvx ▸ hv)
      let w' : (G.deleteOne x).Walk a b := walkOfAvoidsDeleteOne w hax hbx hsupp
      obtain ⟨v, hvw', hvS'⟩ := hS' a ha' b hb' haS' hbS' w'
      refine ⟨v, ?_, Finset.mem_insert_of_mem hvS'⟩
      -- Support of walkOfAvoidsDeleteOne equals support of w
      have : w'.support = w.support := walkOfAvoidsDeleteOne_support w hax hbx hsupp
      rw [this] at hvw'
      exact hvw'
  have hk_le : k ≤ S.card := hsep S hS_sep
  have h_card_le : S.card ≤ S'.card + 1 := by
    rw [hS_def]; exact Finset.card_insert_le x S'
  omega

/-- **s-t Menger reduction from N(s)-N(t) separator bound**: If every
N(s)-N(t) separator has size ≥ k, s ≠ t, and ¬G.Adj s t, then there exist
k internally vertex-disjoint {s}-{t} paths.

The proof first removes common neighbors, using each as the internal vertex
of a length-two path and reducing the required number of paths. Once the
neighbor sets are disjoint, it applies the direct edge-induction argument. -/
private theorem nb_sep_bound_to_st_paths (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (k : Nat) (hst : s ≠ t) (hnadj : ¬G.Adj s t)
    (hsep_bound : ∀ S : Finset V,
      G.IsABSeparator (G.neighborFinset s) (G.neighborFinset t) S → k ≤ S.card) :
    Nonempty (G.STDisjointPaths s t k) := by
  -- Trivial case k = 0
  by_cases hk : k = 0
  · subst hk
    exact ⟨{
      walk := Fin.elim0
      isPath := fun i => Fin.elim0 i
      internal_disjoint := fun i => Fin.elim0 i }⟩
  -- Case split on N(s) ∩ N(t)
  by_cases hint : (G.neighborFinset s ∩ G.neighborFinset t).Nonempty
  · -- Peel: pick x ∈ N(s) ∩ N(t), build trivial s-x-t path + recurse on G.deleteOne x with k-1
    obtain ⟨x, hx⟩ := hint
    have hxs : x ∈ G.neighborFinset s := (Finset.mem_inter.mp hx).1
    have hxt : x ∈ G.neighborFinset t := (Finset.mem_inter.mp hx).2
    have hadj_sx : G.Adj s x := (G.mem_neighborFinset s x).mp hxs
    have hadj_tx : G.Adj t x := (G.mem_neighborFinset t x).mp hxt
    have hsx : s ≠ x := hadj_sx.ne
    have htx : t ≠ x := hadj_tx.ne
    have hnadj' : ¬(G.deleteOne x).Adj s t := fun h => hnadj h.1
    have hsep_bound' : ∀ S : Finset V,
        (G.deleteOne x).IsABSeparator
          ((G.deleteOne x).neighborFinset s) ((G.deleteOne x).neighborFinset t) S →
        (k - 1) ≤ S.card :=
      deleteOne_sep_bound_transfer hsx htx k hsep_bound
    obtain ⟨ih_paths⟩ := nb_sep_bound_to_st_paths (G.deleteOne x) s t (k - 1)
      hst hnadj' hsep_bound'
    -- Build STDisjointPaths in G: index 0 = trivial s-x-t, index j+1 = lifted ih_paths.walk j
    have hk_eq : k = (k - 1) + 1 := by omega
    let trivWalk : G.Walk s t := Walk.cons hadj_sx (Walk.cons hadj_tx.symm Walk.nil)
    let liftedWalks : Fin (k - 1) → G.Walk s t :=
      fun j => liftDeleteOneWalk (ih_paths.walk j)
    let walks : Fin ((k - 1) + 1) → G.Walk s t :=
      Fin.cases trivWalk liftedWalks
    -- Helper: characterize walks i' support for i' : Fin (k-1+1).
    have walks_support_zero : (walks (0 : Fin (k - 1 + 1))) = trivWalk := rfl
    have walks_support_succ : ∀ a : Fin (k - 1),
        (walks a.succ) = liftDeleteOneWalk (ih_paths.walk a) := fun _ => rfl
    refine ⟨{
      walk := fun i => walks (i.cast hk_eq)
      isPath := ?_
      internal_disjoint := ?_ }⟩
    · -- isPath
      intro i
      induction (i.cast hk_eq) using Fin.cases with
      | zero =>
        rw [walks_support_zero]
        refine Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil ?_) ?_
        · simp only [Walk.support_nil, List.mem_singleton]
          exact htx.symm
        · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false, not_or]
          exact ⟨hsx, hst⟩
      | succ a' =>
        rw [walks_support_succ]
        exact liftDeleteOneWalk_isPath _ (ih_paths.isPath a')
    · -- internal_disjoint
      intro i j hij w hwi hws hwt hwj
      have hij' : i.cast hk_eq ≠ j.cast hk_eq := fun h =>
        hij (Fin.cast_injective hk_eq h)
      -- Characterize w in walks i'.support for i' : Fin (k-1+1)
      have walks_internal_char : ∀ (a : Fin (k - 1 + 1)), w ∈ (walks a).support →
          (a = 0 ∧ w = x) ∨
          (∃ a' : Fin (k - 1), a = a'.succ ∧ w ∈ (ih_paths.walk a').support) := by
        intro a ha
        induction a using Fin.cases with
        | zero =>
          left
          refine ⟨rfl, ?_⟩
          rw [walks_support_zero] at ha
          simp only [trivWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · exact absurd rfl hws
          · rfl
          · exact absurd rfl hwt
        | succ a' =>
          right
          refine ⟨a', rfl, ?_⟩
          rw [walks_support_succ] at ha
          rwa [liftDeleteOneWalk_support] at ha
      obtain hwi_case := walks_internal_char (i.cast hk_eq) hwi
      obtain hwj_case := walks_internal_char (j.cast hk_eq) hwj
      rcases hwi_case with ⟨hi_eq, hwx_i⟩ | ⟨i'', hi_succ, hi_in_orig⟩
      · rcases hwj_case with ⟨hj_eq, _⟩ | ⟨j'', hj_succ, hj_in_orig⟩
        · exact hij' (hi_eq.trans hj_eq.symm)
        · exact deleteOne_walk_avoids hsx (ih_paths.walk j'') w hj_in_orig hwx_i
      · rcases hwj_case with ⟨_, hwx_j⟩ | ⟨j'', hj_succ, hj_in_orig⟩
        · exact deleteOne_walk_avoids hsx (ih_paths.walk i'') w hi_in_orig hwx_j
        · have hi''_ne_j'' : i'' ≠ j'' := fun heq =>
            hij' (by rw [hi_succ, hj_succ, heq])
          exact ih_paths.internal_disjoint i'' j'' hi''_ne_j'' w
            hi_in_orig hws hwt hj_in_orig
  · -- Disjoint case: N(s) ∩ N(t) = ∅. Direct s-t Menger via ABConnector.
    -- Proof strategy:
    --   1. Apply menger_hard_direction_AB to get k fully vertex-disjoint
    --      paths conn : ABConnector N(s) N(t) k.
    --   2. Build s-t walks by prepending s—src i and appending dst i—t.
    --   3. isPath / internal_disjoint follow from touchA/touchB/disjoint
    --      plus key lemmas s ∉ walk i and t ∉ walk i.
    have _hdisj : Disjoint (G.neighborFinset s) (G.neighborFinset t) :=
      Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hint)
    obtain ⟨conn⟩ := exists_ABConnector_of_separator_lower_bound G
      (G.neighborFinset s) (G.neighborFinset t) k hk hsep_bound
    have hsrc_adj : ∀ i, G.Adj s (conn.src i) :=
      fun i => (G.mem_neighborFinset s _).mp (conn.src_mem i)
    have hdst_adj : ∀ i, G.Adj t (conn.dst i) :=
      fun i => (G.mem_neighborFinset t _).mp (conn.dst_mem i)
    -- Helper: s ∉ (conn.walk i).support. Proof: if s = src i then
    -- src i ∈ N(s) gives G.Adj s s (loop, false). If s = dst i then
    -- dst i ∈ N(t) gives G.Adj s t, contradicting hnadj. If s is internal,
    -- the successor of s (snd of dropUntil s) is adjacent to s and on the
    -- walk, hence in N(s), so by touchA equals src i. But src i is also at
    -- the start of the walk, contradicting support_nodup.
    have hs_notin : ∀ i, s ∉ (conn.walk i).support := by
      intro i hs_in
      by_cases h1 : s = conn.src i
      · have hadj : G.Adj s (conn.src i) :=
          (G.mem_neighborFinset _ _).mp (conn.src_mem i)
        rw [← h1] at hadj
        exact G.irrefl hadj
      by_cases h2 : s = conn.dst i
      · have hadj : G.Adj t (conn.dst i) :=
          (G.mem_neighborFinset _ _).mp (conn.dst_mem i)
        rw [← h2] at hadj
        exact hnadj (G.adj_symm hadj)
      -- Case 3: s is internal — successor argument
      set walkB := (conn.walk i).dropUntil s hs_in with hwB_def
      have hwB_not_nil : ¬ walkB.Nil := fun h => h2 h.eq
      have hsucc_in_tail : walkB.snd ∈ walkB.support.tail :=
        Walk.snd_mem_tail_support hwB_not_nil
      have hsucc_in_walkB : walkB.snd ∈ walkB.support :=
        List.mem_of_mem_tail hsucc_in_tail
      have hsucc_in_orig : walkB.snd ∈ (conn.walk i).support :=
        Walk.support_dropUntil_subset _ _ hsucc_in_walkB
      have hadj_succ : G.Adj s walkB.snd := Walk.adj_snd hwB_not_nil
      have hsucc_in_Ns : walkB.snd ∈ G.neighborFinset s :=
        (G.mem_neighborFinset _ _).mpr hadj_succ
      have hsucc_eq : walkB.snd = conn.src i :=
        conn.touchA i _ hsucc_in_orig hsucc_in_Ns
      have h_supp_eq : (conn.walk i).support =
          ((conn.walk i).takeUntil s hs_in).support ++ walkB.support.tail := by
        have h := Walk.support_append ((conn.walk i).takeUntil s hs_in) walkB
        rw [Walk.take_spec] at h
        exact h
      have h_nodup := (conn.isPath i).support_nodup
      rw [h_supp_eq] at h_nodup
      have h_src_take : conn.src i ∈ ((conn.walk i).takeUntil s hs_in).support :=
        Walk.start_mem_support _
      have h_src_tail : conn.src i ∈ walkB.support.tail := hsucc_eq ▸ hsucc_in_tail
      exact (List.nodup_append.mp h_nodup).2.2 _ h_src_take _ h_src_tail rfl
    -- Helper: t ∉ (conn.walk i).support. Symmetric argument: predecessor
    -- (penultimate of takeUntil t) is adjacent to t, in N(t), so by touchB
    -- equals dst i. But dst i is also at the end of the walk, in
    -- dropUntil(t).support.tail, contradicting support_nodup.
    have ht_notin : ∀ i, t ∉ (conn.walk i).support := by
      intro i ht_in
      by_cases h1 : t = conn.src i
      · have hadj : G.Adj s (conn.src i) :=
          (G.mem_neighborFinset _ _).mp (conn.src_mem i)
        rw [← h1] at hadj
        exact hnadj hadj
      by_cases h2 : t = conn.dst i
      · have hadj : G.Adj t (conn.dst i) :=
          (G.mem_neighborFinset _ _).mp (conn.dst_mem i)
        rw [← h2] at hadj
        exact G.irrefl hadj
      -- Case 3: t is internal — predecessor argument
      set walkA := (conn.walk i).takeUntil t ht_in with hwA_def
      have hwA_not_nil : ¬ walkA.Nil := fun h => h1 h.eq.symm
      have hadj_pred : G.Adj walkA.penultimate t := Walk.adj_penultimate hwA_not_nil
      have hpred_in_walkA : walkA.penultimate ∈ walkA.support :=
        List.mem_of_mem_dropLast (Walk.penultimate_mem_dropLast_support hwA_not_nil)
      have hpred_in_orig : walkA.penultimate ∈ (conn.walk i).support :=
        Walk.support_takeUntil_subset _ _ hpred_in_walkA
      have hpred_in_Nt : walkA.penultimate ∈ G.neighborFinset t :=
        (G.mem_neighborFinset _ _).mpr hadj_pred.symm
      have hpred_eq : walkA.penultimate = conn.dst i :=
        conn.touchB i _ hpred_in_orig hpred_in_Nt
      have h_supp_eq : (conn.walk i).support =
          walkA.support ++ ((conn.walk i).dropUntil t ht_in).support.tail := by
        have h := Walk.support_append walkA ((conn.walk i).dropUntil t ht_in)
        rw [Walk.take_spec] at h
        exact h
      have h_nodup := (conn.isPath i).support_nodup
      rw [h_supp_eq] at h_nodup
      have h_dst_take : conn.dst i ∈ walkA.support := hpred_eq ▸ hpred_in_walkA
      have h_dst_drop_full : conn.dst i ∈ ((conn.walk i).dropUntil t ht_in).support :=
        Walk.end_mem_support _
      have h_dst_tail : conn.dst i ∈ ((conn.walk i).dropUntil t ht_in).support.tail := by
        have h_drop_supp := Walk.support_eq_cons ((conn.walk i).dropUntil t ht_in)
        rw [h_drop_supp, List.mem_cons] at h_dst_drop_full
        exact h_dst_drop_full.resolve_left fun heq => h2 heq.symm
      exact (List.nodup_append.mp h_nodup).2.2 _ h_dst_take _ h_dst_tail rfl
    -- Construct s-t walks: s → src i → ... → dst i → t.
    let stWalk : Fin k → G.Walk s t := fun i =>
      Walk.cons (hsrc_adj i)
        ((conn.walk i).append (Walk.cons (G.adj_symm (hdst_adj i)) Walk.nil))
    refine ⟨{
      walk := stWalk
      isPath := ?_
      internal_disjoint := ?_ }⟩
    · -- isPath: stWalk i = cons hsrc (walk i ++ cons hdst.symm nil).
      -- Inner is a path via concat_isPath_iff (walk is path, t ∉ walk).
      -- Outer cons is a path via cons_isPath_iff (s ∉ inner.support).
      intro i
      have h_inner_eq : (conn.walk i).append (Walk.cons (G.adj_symm (hdst_adj i)) Walk.nil)
          = (conn.walk i).concat (G.adj_symm (hdst_adj i)) :=
        (Walk.concat_eq_append _ _).symm
      have h_inner_path : ((conn.walk i).append
          (Walk.cons (G.adj_symm (hdst_adj i)) Walk.nil)).IsPath := by
        rw [h_inner_eq]
        exact (Walk.concat_isPath_iff _).mpr ⟨conn.isPath i, ht_notin i⟩
      have h_inner_supp : ((conn.walk i).append
          (Walk.cons (G.adj_symm (hdst_adj i)) Walk.nil)).support
          = (conn.walk i).support ++ [t] := by
        rw [h_inner_eq, Walk.support_concat, List.concat_eq_append]
      apply (Walk.cons_isPath_iff _ _).mpr
      refine ⟨h_inner_path, ?_⟩
      rw [h_inner_supp]
      intro h_in
      rcases List.mem_append.mp h_in with h_in_walk | h_in_t
      · exact hs_notin i h_in_walk
      · simp only [List.mem_singleton] at h_in_t
        exact hst h_in_t
    · -- internal_disjoint: w ∈ stWalk i.support with w ≠ s, w ≠ t
      -- ⇒ w ∈ (conn.walk i).support; same for j; conn.disjoint contradiction.
      intro i j hij w hw_i hw_ne_s hw_ne_t hw_j
      have h_supp : ∀ k : Fin _, (stWalk k).support
          = s :: ((conn.walk k).support ++ [t]) := by
        intro k
        change (Walk.cons (hsrc_adj k)
            ((conn.walk k).append (Walk.cons (G.adj_symm (hdst_adj k)) Walk.nil))).support
            = s :: ((conn.walk k).support ++ [t])
        rw [Walk.support_cons]
        congr 1
        rw [show (conn.walk k).append (Walk.cons (G.adj_symm (hdst_adj k)) Walk.nil)
              = (conn.walk k).concat (G.adj_symm (hdst_adj k))
            from (Walk.concat_eq_append _ _).symm,
            Walk.support_concat, List.concat_eq_append]
      have hw_walk_of : ∀ k, w ∈ (stWalk k).support → w ∈ (conn.walk k).support := by
        intro k hw_k
        rw [h_supp] at hw_k
        rcases List.mem_cons.mp hw_k with h_eq_s | h_in_rest
        · exact absurd h_eq_s hw_ne_s
        · rcases List.mem_append.mp h_in_rest with h_in_walk | h_in_t
          · exact h_in_walk
          · simp only [List.mem_singleton] at h_in_t
            exact absurd h_in_t hw_ne_t
      exact conn.disjoint i j hij w (hw_walk_of i hw_i) (hw_walk_of j hw_j)
termination_by (G.neighborFinset s ∩ G.neighborFinset t).card
decreasing_by
  exact deleteOne_inter_card_lt hsx htx hxs hxt

/-- **Auxiliary construction for s-t Menger** (Diestel Cor 3.3.4):
When s ≠ t and every {s}-{t} separator avoiding s,t has size ≥ k,
there exist k internally vertex-disjoint {s}-{t} paths.

The proof splits into two cases:
- **G.Adj s t**: k copies of the direct edge (support = {s,t}, no internal
  vertices, so internal disjointness is vacuous for any k).
- **¬G.Adj s t**: Every N(s)-N(t) separator has size ≥ k
  (by `nb_sep_lower_bound`, which uses the separator correspondence
  `nb_sep_sdiff_is_st_sep` to reduce to hypothesis h). Then
  `nb_sep_bound_to_st_paths` converts the separator bound into k internally
  vertex-disjoint {s}-{t} paths. Both branches are fully proved. -/
private theorem menger_st_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (k : Nat) (hst : s ≠ t)
    (h : ∀ S : Finset V, s ∉ S → t ∉ S →
      G.IsABSeparator {s} {t} S → k ≤ S.card) :
    Nonempty (G.STDisjointPaths s t k) := by
  by_cases hadj : G.Adj s t
  · -- Case 1: s-t adjacent. k copies of the direct edge.
    -- Support = {s, t}, no internal vertices, disjointness vacuous.
    refine ⟨⟨fun _ => Walk.cons hadj Walk.nil,
      fun _ => Walk.IsPath.cons Walk.IsPath.nil
        (by simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false]; exact hst),
      ?_⟩⟩
    intro i j _hij v hv hns hnt
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> contradiction
  · -- Case 2: ¬G.Adj s t.
    -- Every N(s)-N(t) separator has size ≥ k (proved via separator correspondence).
    have hsep_bound : ∀ S : Finset V,
        G.IsABSeparator (G.neighborFinset s) (G.neighborFinset t) S → k ≤ S.card :=
      fun S hS => nb_sep_lower_bound G s t k hst hadj h S hS
    -- Apply vertex-splitting reduction to get {s}-{t} paths.
    exact nb_sep_bound_to_st_paths G s t k hst hadj hsep_bound

/-- **s-t Menger's theorem** (Diestel Corollary 3.3.4): If every {s}-{t}
separator S with s ∉ S and t ∉ S has size at least k, then there exist k
internally vertex-disjoint s-t paths (represented as vertex-disjoint
{s}-{t} paths). Delegates to `menger_st_aux` which requires auxiliary
graph construction (vertex splitting + walk transfer). -/
theorem menger_st_of_separator_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (k : Nat) (hst : s ≠ t)
    (h : ∀ S : Finset V, s ∉ S → t ∉ S →
      G.IsABSeparator {s} {t} S → k ≤ S.card) :
    Nonempty (G.STDisjointPaths s t k) :=
  menger_st_aux G s t k hst h

/-- **Global form**: k-vertex-connectivity is equivalent to existence of k
internally vertex-disjoint paths between every pair of vertices.

The forward direction (paths ⟹ connectivity) is proved via a pigeonhole
argument: each path must have an internal vertex in S, and by internal
disjointness these are all distinct, so |S| ≥ k.

The backward direction (connectivity ⟹ paths) requires a strengthened
version of Menger's theorem for s-t separators with excluded endpoints.
Not in Mathlib as of 2025. -/
theorem stDisjointPaths_iff_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : Nat) (hk : k < Fintype.card V) :
    (forall (a b : V), Ne a b ->
      Nonempty (G.STDisjointPaths a b k)) <->
    (forall (S : Finset V), S.card < k ->
      (G.induce ((Finset.univ \ S : Finset V) : Set V)).Connected) := by
  constructor
  · -- Forward: k disjoint a-b paths for all a ≠ b ⟹ k-connected.
    -- Proof sketch: If S separates G with |S| < k, pick a ∈ A, b ∈ B
    -- (components of G-S). The k paths from a to b must each cross S,
    -- but by pigeonhole |S| < k paths share a crossing vertex, contradicting
    -- internal disjointness (after careful endpoint analysis).
    intro hpaths S hS
    rw [connected_iff]
    constructor
    · intro ⟨u, hu⟩ ⟨v, hv⟩
      by_cases huv : u = v
      · subst huv; exact Reachable.refl _
      · obtain ⟨dp⟩ := hpaths u v huv
        have huS : u ∉ S := by
          have h := Finset.mem_coe.mp hu; rw [Finset.mem_sdiff] at h; exact h.2
        have hvS : v ∉ S := by
          have h := Finset.mem_coe.mp hv; rw [Finset.mem_sdiff] at h; exact h.2
        suffices ∃ i : Fin k, ∀ w ∈ (dp.walk i).support, w ∉ S by
          obtain ⟨i, hi⟩ := this
          have hsup : ∀ w ∈ (dp.walk i).support, w ∈ (↑(Finset.univ \ S) : Set V) := by
            intro w hw; exact Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hi w hw⟩)
          let w' := Walk.induce (↑(Finset.univ \ S) : Set V) (dp.walk i) hsup
          exact ⟨w'⟩
        -- Pigeonhole: at most |S| paths hit S, but we have k > |S| paths
        by_contra hall
        simp only [not_exists, not_forall, Classical.not_not] at hall
        -- hall : ∀ i, ∃ w, w ∈ support ∧ w ∈ S
        -- Since src = u ∉ S and dst = v ∉ S, hitting vertices are internal
        have internal_hit : ∀ i, ∃ w, w ∈ (dp.walk i).support ∧ w ∈ S ∧ w ≠ u ∧ w ≠ v := by
          intro i
          obtain ⟨w, hw_supp, hw_S⟩ := hall i
          exact ⟨w, hw_supp, hw_S, fun h => huS (h ▸ hw_S), fun h => hvS (h ▸ hw_S)⟩
        -- Choose witness for each path, prove injective, contradict |S| < k
        let f : Fin k → V := fun i => (internal_hit i).choose
        have hf_supp : ∀ i, f i ∈ (dp.walk i).support := fun i => (internal_hit i).choose_spec.1
        have hf_S : ∀ i, f i ∈ S := fun i => (internal_hit i).choose_spec.2.1
        have hf_ne_u : ∀ i, f i ≠ u := fun i => (internal_hit i).choose_spec.2.2.1
        have hf_ne_v : ∀ i, f i ≠ v := fun i => (internal_hit i).choose_spec.2.2.2
        have hf_inj : Function.Injective f := by
          intro i j hij
          by_contra hne
          exact dp.internal_disjoint i j hne (f i) (hf_supp i) (hf_ne_u i) (hf_ne_v i)
            (hij ▸ hf_supp j)
        have h1 : Fintype.card (Fin k) ≤ Fintype.card ↥S :=
          Fintype.card_le_of_injective (fun i => ⟨f i, hf_S i⟩)
            (fun i j h => hf_inj (congrArg Subtype.val h))
        rw [Fintype.card_fin, Fintype.card_coe] at h1
        omega
    · have hcard : S.card < Fintype.card V := lt_trans hS hk
      have hne' : (Finset.univ \ S : Finset V).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        have := Finset.card_le_card hsub
        simp at this
        omega
      exact hne'.to_subtype
  · -- Backward: k-connected ⟹ k disjoint {a}-{b} paths for all a ≠ b.
    -- Proof: For a ≠ b, show every {a}-{b} separator S with a ∉ S, b ∉ S
    -- has size ≥ k (since removing S leaves G connected, so a,b stay connected
    -- in G-S, meaning S doesn't separate them unless |S| ≥ k). Then apply
    -- the s-t version of Menger's theorem (Diestel 3.3.4).
    intro hconn a b hab
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨{ walk := fun i => i.elim0,
               isPath := fun i => i.elim0,
               internal_disjoint := fun i _ _ _ _ _ _ => i.elim0 }⟩
    -- k ≥ 1: Every s-t separator (excluding endpoints) has size ≥ k.
    have hsep_bound : ∀ S : Finset V, a ∉ S → b ∉ S →
        G.IsABSeparator {a} {b} S → k ≤ S.card := by
      intro S haS hbS hS
      by_contra hlt
      push Not at hlt
      have hconn' := hconn S hlt
      rw [connected_iff] at hconn'
      have ha_mem : a ∈ (↑(Finset.univ \ S) : Set V) :=
        Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haS⟩)
      have hb_mem : b ∈ (↑(Finset.univ \ S) : Set V) :=
        Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbS⟩)
      obtain ⟨w⟩ := hconn'.1 ⟨a, ha_mem⟩ ⟨b, hb_mem⟩
      -- Lift the walk from G-S to G and show it avoids S entirely
      have key : ∀ v ∈ (Walk.map (Embedding.induce (↑(Finset.univ \ S) : Set V) (G := G)).toHom w).support, v ∉ S := by
        intro v hv
        rw [Walk.support_map] at hv
        rw [List.mem_map] at hv
        obtain ⟨⟨x, hx⟩, _, rfl⟩ := hv
        exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).2
      -- But hS says every a-b walk hits S — contradiction
      obtain ⟨v, hvm, hvs⟩ := hS a (Finset.mem_singleton.mpr rfl) b (Finset.mem_singleton.mpr rfl) haS hbS
        (Walk.map (Embedding.induce (↑(Finset.univ \ S) : Set V) (G := G)).toHom w)
      exact key v hvm hvs
    -- Step 2: Apply the s-t version of Menger's theorem.
    exact menger_st_of_separator_bound G a b k hab hsep_bound

/-! ## Local vertex Menger: exact min-max form -/

/-- Cardinalities of `{s}`-`{t}` separators that contain neither endpoint.

This is the separator family used in the local form of Menger's theorem
(Diestel, 2nd ed., Corollary 3.3.4(i)).  It differs from
`abSeparatorSizes G {s} {t}` by explicitly excluding `s` and `t`. -/
def stSeparatorSizes (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) : Set Nat :=
  {n | ∃ S : Finset V, s ∉ S ∧ t ∉ S ∧
    G.IsABSeparator {s} {t} S ∧ S.card = n}

/-- For distinct nonadjacent endpoints, `N(s)` is an `s`-`t` separator that
contains neither endpoint. -/
theorem neighborFinset_is_stSeparator (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) (hnadj : ¬G.Adj s t) :
    s ∉ G.neighborFinset s ∧ t ∉ G.neighborFinset s ∧
      G.IsABSeparator {s} {t} (G.neighborFinset s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [G.mem_neighborFinset]
    exact G.irrefl
  · rw [G.mem_neighborFinset]
    exact hnadj
  · intro a ha b hb _ _ w
    rw [Finset.mem_singleton] at ha hb
    subst a
    subst b
    have hnonNil : ¬w.Nil := fun hnil => hst hnil.eq
    have hadj : G.Adj s w.snd := Walk.adj_snd hnonNil
    exact ⟨w.snd, List.mem_of_mem_tail (Walk.snd_mem_tail_support hnonNil),
      (G.mem_neighborFinset s w.snd).mpr hadj⟩

/-- The endpoint-avoiding separator-size set is nonempty for distinct
nonadjacent endpoints. -/
theorem stSeparatorSizes_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) (hnadj : ¬G.Adj s t) :
    (G.stSeparatorSizes s t).Nonempty := by
  obtain ⟨hs, ht, hsep⟩ := neighborFinset_is_stSeparator G s t hst hnadj
  exact ⟨(G.neighborFinset s).card, G.neighborFinset s, hs, ht, hsep, rfl⟩

/-- Minimum size of an `s`-`t` separator avoiding both endpoints. -/
noncomputable def minSTSeparatorSize (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) : Nat :=
  sInf (G.stSeparatorSizes s t)

/-- The local separator minimum is attained for distinct nonadjacent
endpoints. -/
theorem minSTSeparatorSize_spec (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) (hnadj : ¬G.Adj s t) :
    ∃ S : Finset V, s ∉ S ∧ t ∉ S ∧ G.IsABSeparator {s} {t} S ∧
      S.card = G.minSTSeparatorSize s t :=
  Nat.sInf_mem (stSeparatorSizes_nonempty G s t hst hnadj)

/-- Every endpoint-avoiding `s`-`t` separator has cardinality at least the
local separator minimum. -/
theorem minSTSeparatorSize_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (S : Finset V) (hs : s ∉ S) (ht : t ∉ S)
    (hsep : G.IsABSeparator {s} {t} S) :
    G.minSTSeparatorSize s t ≤ S.card :=
  Nat.sInf_le ⟨S, hs, ht, hsep, rfl⟩

/-- The easy direction of local vertex Menger: each internally disjoint
`s`-`t` path needs a distinct vertex of every separator avoiding `s,t`. -/
theorem STDisjointPaths.card_le_separator {G : SimpleGraph V}
    [DecidableRel G.Adj] {s t : V} {k : Nat}
    (P : G.STDisjointPaths s t k) (S : Finset V)
    (hs : s ∉ S) (ht : t ∉ S) (hsep : G.IsABSeparator {s} {t} S) :
    k ≤ S.card := by
  classical
  have hhit : ∀ i : Fin k, ∃ v, v ∈ (P.walk i).support ∧ v ∈ S :=
    fun i => walk_hits_separator hsep (Finset.mem_singleton_self s)
      (Finset.mem_singleton_self t) (P.walk i)
  let f : Fin k → ↥S := fun i => ⟨(hhit i).choose, (hhit i).choose_spec.2⟩
  have hf_supp : ∀ i, (f i : V) ∈ (P.walk i).support :=
    fun i => (hhit i).choose_spec.1
  have hf_ne_s : ∀ i, (f i : V) ≠ s :=
    fun i h => hs (h ▸ (f i).property)
  have hf_ne_t : ∀ i, (f i : V) ≠ t :=
    fun i h => ht (h ▸ (f i).property)
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hval : (f i : V) = (f j : V) := congrArg Subtype.val hij
    exact (P.internal_disjoint i j hne (f i) (hf_supp i) (hf_ne_s i) (hf_ne_t i))
      (hval ▸ hf_supp j)
  simpa using Fintype.card_le_of_injective f hf_inj

/-- The maximum number of internally vertex-disjoint `s`-`t` paths, for the
local Menger setting of distinct nonadjacent endpoints.  Its combinatorial
maximum specification is provided by `maxSTDisjointPaths_spec` and
`le_maxSTDisjointPaths`. -/
noncomputable def maxSTDisjointPaths (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) : Nat :=
  G.minSTSeparatorSize s t

/-- The local path maximum is attained for distinct nonadjacent endpoints. -/
theorem maxSTDisjointPaths_spec (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) :
    Nonempty (G.STDisjointPaths s t (G.maxSTDisjointPaths s t)) := by
  apply menger_st_of_separator_bound G s t (G.maxSTDisjointPaths s t) hst
  intro S hs ht hsep
  exact minSTSeparatorSize_le G s t S hs ht hsep

/-- Every internally vertex-disjoint `s`-`t` path family has cardinality at
most `maxSTDisjointPaths` when the endpoints are distinct and nonadjacent. -/
theorem le_maxSTDisjointPaths (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) (hnadj : ¬G.Adj s t) {k : Nat}
    (P : G.STDisjointPaths s t k) :
    k ≤ G.maxSTDisjointPaths s t := by
  obtain ⟨S, hs, ht, hsep, hcard⟩ :=
    minSTSeparatorSize_spec G s t hst hnadj
  rw [maxSTDisjointPaths, ← hcard]
  exact P.card_le_separator S hs ht hsep

/-- **Local vertex Menger theorem** (Diestel, 2nd ed., Corollary 3.3.4(i)).
For distinct nonadjacent vertices, the maximum number of internally
vertex-disjoint `s`-`t` paths equals the minimum cardinality of an `s`-`t`
separator containing neither endpoint. -/
theorem local_vertex_menger (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (_hst : s ≠ t) (_hnadj : ¬G.Adj s t) :
    G.maxSTDisjointPaths s t = G.minSTSeparatorSize s t := by
  rfl

/-! ## Fan form of Menger's theorem -/

/-- An `a`-`B` **fan** of order `k`: `k` paths with common initial vertex
`a`, distinct final vertices in `B`, and no common vertices other than `a`.
Each path meets `B` only in its final vertex. -/
structure ABFan (G : SimpleGraph V) (a : V) (B : Finset V) (k : Nat) where
  /-- The distinct final vertices of the fan paths. -/
  dst : Fin k → V
  /-- The paths from the common centre to their final vertices. -/
  walk : (i : Fin k) → G.Walk a (dst i)
  /-- Every fan walk is a path. -/
  isPath : ∀ i, (walk i).IsPath
  /-- Every final vertex belongs to `B`. -/
  dst_mem : ∀ i, dst i ∈ B
  /-- Different fan paths have different final vertices. -/
  dst_inj : Function.Injective dst
  /-- A fan path meets `B` only at its final vertex. -/
  touchB : ∀ i v, v ∈ (walk i).support → v ∈ B → v = dst i
  /-- Different fan paths can meet only at their common initial vertex. -/
  common_eq_start : ∀ i j, i ≠ j → ∀ v,
    v ∈ (walk i).support → v ∈ (walk j).support → v = a

/-- There is always an `a`-`B` fan with no paths. -/
theorem abFan_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) : Nonempty (G.ABFan a B 0) :=
  ⟨{ dst := Fin.elim0
     walk := fun i => Fin.elim0 i
     isPath := fun i => Fin.elim0 i
     dst_mem := fun i => Fin.elim0 i
     dst_inj := fun i => Fin.elim0 i
     touchB := fun i => Fin.elim0 i
     common_eq_start := fun i => Fin.elim0 i }⟩

/-- Cardinalities of sets of vertices different from `a` that separate `a`
from `B`. This is the separator family in Diestel's fan form of Menger. -/
def aBSeparatorSizes (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) : Set Nat :=
  {n | ∃ S : Finset V, a ∉ S ∧ G.IsABSeparator {a} B S ∧ S.card = n}

/-- If `a ∉ B`, the family of `a`-`B` separator sizes avoiding `a` is
nonempty. The set `univ.erase a` is a witness. -/
theorem aBSeparatorSizes_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (haB : a ∉ B) :
    (G.aBSeparatorSizes a B).Nonempty := by
  refine ⟨(Finset.univ.erase a).card, Finset.univ.erase a, by simp, ?_, rfl⟩
  intro x hx y hy _ hyS _
  rw [Finset.mem_singleton] at hx
  subst x
  have hya : y = a := by simpa using hyS
  subst y
  exact (haB hy).elim

/-- The minimum number of vertices different from `a` separating `a` from
`B`. -/
noncomputable def minABFanSeparatorSize (G : SimpleGraph V)
    [DecidableRel G.Adj] (a : V) (B : Finset V) : Nat :=
  sInf (G.aBSeparatorSizes a B)

/-- The minimum `a`-`B` separator size avoiding `a` is attained. -/
theorem minABFanSeparatorSize_spec (G : SimpleGraph V)
    [DecidableRel G.Adj] (a : V) (B : Finset V) (haB : a ∉ B) :
    ∃ S : Finset V, a ∉ S ∧ G.IsABSeparator {a} B S ∧
      S.card = G.minABFanSeparatorSize a B :=
  Nat.sInf_mem (aBSeparatorSizes_nonempty G a B haB)

/-- Every `a`-`B` separator avoiding `a` has at least the minimum cardinality. -/
theorem minABFanSeparatorSize_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (a : V) (B S : Finset V)
    (haS : a ∉ S) (hsep : G.IsABSeparator {a} B S) :
    G.minABFanSeparatorSize a B ≤ S.card :=
  Nat.sInf_le ⟨S, haS, hsep, rfl⟩

/-- An `N_G(a)`-`B` separator in `G.deleteOne a` yields an `a`-`B`
separator in `G` after erasing `a` from it.

The key point is that an arbitrary `a`-`B` walk can first be replaced by a
path. The tail of that path avoids `a`, hence is a walk in `G.deleteOne a`. -/
theorem deleteOne_neighbor_separator_to_aBSeparator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B S : Finset V) (haB : a ∉ B)
    (hS : (G.deleteOne a).IsABSeparator (G.neighborFinset a) B S) :
    G.IsABSeparator {a} B (S.erase a) := by
  intro x hx y hy _ _ w
  rw [Finset.mem_singleton] at hx
  subst x
  have hay : a ≠ y := by
    intro h
    apply haB
    simpa [h] using hy
  let p : G.Walk a y := w.toPath
  have hp : p.IsPath := w.toPath.property
  have hp_ne : ¬p.Nil := Walk.not_nil_of_ne hay
  have hadj : G.Adj a p.snd := p.adj_snd hp_ne
  have hsnd_mem : p.snd ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a p.snd).mpr hadj
  have ha_tail : a ∉ p.support.tail := by
    have hnodup := hp.support_nodup
    rw [p.support_eq_cons] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have ha_tail_walk : ∀ v ∈ p.tail.support, v ≠ a := by
    intro v hv hva
    subst v
    apply ha_tail
    rwa [p.support_tail_of_not_nil hp_ne] at hv
  let q : (G.deleteOne a).Walk p.snd y :=
    walkOfAvoidsDeleteOne p.tail hadj.ne' hay.symm ha_tail_walk
  obtain ⟨v, hvq, hvS⟩ :=
    walk_hits_separator hS hsnd_mem hy q
  have hq_support : q.support = p.tail.support :=
    walkOfAvoidsDeleteOne_support p.tail hadj.ne' hay.symm ha_tail_walk
  have hv_tail_walk : v ∈ p.tail.support := by
    rw [← hq_support]
    exact hvq
  have hv_tail : v ∈ p.support.tail := by
    rwa [p.support_tail_of_not_nil hp_ne] at hv_tail_walk
  refine ⟨v, Walk.support_toPath_subset w (List.mem_of_mem_tail hv_tail), ?_⟩
  exact Finset.mem_erase.mpr ⟨fun hva => ha_tail (hva ▸ hv_tail), hvS⟩

/-- Prepending the centre `a` to an `N_G(a)`-`B` connector in
`G.deleteOne a` produces an `a`-`B` fan in `G`. -/
noncomputable def ABConnector.toABFan
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a : V} {B : Finset V} {k : Nat} (haB : a ∉ B)
    (conn : (G.deleteOne a).ABConnector (G.neighborFinset a) B k) :
    G.ABFan a B k where
  dst := conn.dst
  walk := fun i =>
    Walk.cons ((G.mem_neighborFinset a (conn.src i)).mp (conn.src_mem i))
      (liftDeleteOneWalk (conn.walk i))
  isPath := fun i => by
    let hadj : G.Adj a (conn.src i) :=
      (G.mem_neighborFinset a (conn.src i)).mp (conn.src_mem i)
    rw [Walk.cons_isPath_iff]
    refine ⟨liftDeleteOneWalk_isPath (conn.walk i) (conn.isPath i), ?_⟩
    intro ha
    rw [liftDeleteOneWalk_support] at ha
    exact (deleteOne_walk_avoids hadj.ne' (conn.walk i) a ha) rfl
  dst_mem := conn.dst_mem
  dst_inj := by
    intro i j hij
    by_contra hne
    exact conn.disjoint i j hne (conn.dst i) (Walk.end_mem_support _)
      (by simpa [hij] using Walk.end_mem_support (conn.walk j))
  touchB := by
    intro i v hv hvB
    simp only [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (haB hvB).elim
    · apply conn.touchB i v _ hvB
      rwa [liftDeleteOneWalk_support] at hv
  common_eq_start := by
    intro i j hij v hvi hvj
    simp only [Walk.support_cons, List.mem_cons] at hvi hvj
    rcases hvi with rfl | hvi
    · rfl
    rcases hvj with rfl | hvj
    · rfl
    exfalso
    apply conn.disjoint i j hij v
    · rwa [liftDeleteOneWalk_support] at hvi
    · rwa [liftDeleteOneWalk_support] at hvj

/-- The hard direction of the fan form of Menger: there is an `a`-`B` fan
whose order is the minimum cardinality of an `a`-`B` separator avoiding `a`. -/
theorem abFan_hard_direction (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (haB : a ∉ B) :
    Nonempty (G.ABFan a B (G.minABFanSeparatorSize a B)) := by
  by_cases hm : G.minABFanSeparatorSize a B = 0
  · rw [hm]
    exact abFan_zero G a B
  · have hbound : ∀ S : Finset V,
        (G.deleteOne a).IsABSeparator (G.neighborFinset a) B S →
          G.minABFanSeparatorSize a B ≤ S.card := by
      intro S hS
      calc
        G.minABFanSeparatorSize a B ≤ (S.erase a).card :=
          minABFanSeparatorSize_le G a B (S.erase a) (by simp)
            (deleteOne_neighbor_separator_to_aBSeparator G a B S haB hS)
        _ ≤ S.card := Finset.card_erase_le
    obtain ⟨conn⟩ := exists_ABConnector_of_separator_lower_bound
      (G.deleteOne a) (G.neighborFinset a) B
      (G.minABFanSeparatorSize a B) hm hbound
    exact ⟨conn.toABFan haB⟩

/-- The easy direction of fan Menger: every `a`-`B` fan has order at most
the cardinality of every `a`-`B` separator avoiding `a`. -/
theorem ABFan.card_le_separator {G : SimpleGraph V} [DecidableRel G.Adj]
    {a : V} {B : Finset V} {k : Nat} (P : G.ABFan a B k)
    (S : Finset V) (haS : a ∉ S) (hsep : G.IsABSeparator {a} B S) :
    k ≤ S.card := by
  classical
  have hhit : ∀ i : Fin k, ∃ v, v ∈ (P.walk i).support ∧ v ∈ S :=
    fun i => walk_hits_separator hsep (Finset.mem_singleton_self a)
      (P.dst_mem i) (P.walk i)
  let f : Fin k → ↥S := fun i => ⟨(hhit i).choose, (hhit i).choose_spec.2⟩
  have hf_supp : ∀ i, (f i : V) ∈ (P.walk i).support :=
    fun i => (hhit i).choose_spec.1
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hval : (f i : V) = (f j : V) := congrArg Subtype.val hij
    have hstart : (f i : V) = a :=
      P.common_eq_start i j hne (f i) (hf_supp i) (hval ▸ hf_supp j)
    exact haS (hstart ▸ (f i).property)
  simpa using Fintype.card_le_of_injective f hf_inj

/-- The maximum order of an `a`-`B` fan. Its attained and universal
specifications are `maxABFanSize_spec` and `le_maxABFanSize`. -/
noncomputable def maxABFanSize (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) : Nat :=
  G.minABFanSeparatorSize a B

/-- The maximum fan order is attained. -/
theorem maxABFanSize_spec (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (haB : a ∉ B) :
    Nonempty (G.ABFan a B (G.maxABFanSize a B)) := by
  exact abFan_hard_direction G a B haB

/-- Every `a`-`B` fan has order at most `maxABFanSize`. -/
theorem le_maxABFanSize (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (haB : a ∉ B) {k : Nat}
    (P : G.ABFan a B k) : k ≤ G.maxABFanSize a B := by
  obtain ⟨S, haS, hsep, hcard⟩ := minABFanSeparatorSize_spec G a B haB
  rw [maxABFanSize, ← hcard]
  exact P.card_le_separator S haS hsep

/-- **Fan form of Menger's theorem** (Diestel, 2nd ed., Corollary 3.3.3):
for `a ∉ B`, the maximum order of an `a`-`B` fan equals the minimum number
of vertices different from `a` that separate `a` from `B`.

The two extrema are independently certified by `maxABFanSize_spec`,
`le_maxABFanSize`, `minABFanSeparatorSize_spec`, and
`minABFanSeparatorSize_le`. -/
theorem fan_menger (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (_haB : a ∉ B) :
    G.maxABFanSize a B = G.minABFanSeparatorSize a B := by
  rfl

end SimpleGraph
