import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import GraphTheory.SimpleGraph.Connectivity.Menger

/-!
# Mader's theorem on H-paths (Diestel §3.4, Theorem 3.4.1)

Diestel, *Graph Theory*, 5th ed., §3.4, pp. 56–58. Mader's 1978 theorem
extends Menger's theorem to paths through a specified subgraph `H ⊆ G`.

This file defines H-paths, families of disjoint H-paths, and H-covers. It proves
the loose upper bound from a packing of H-paths to any H-cover. The full
min-max equality is not asserted here.

## Definitions

* `IsHPath G H p` — a walk `p : G.Walk u v` is an **H-path** when its
  endpoints `u, v` lie in `H.verts`, its internal vertices lie outside
  `H.verts`, and none of its edges belongs to `H.edgeSet`.
* `HPaths G H k` — a family of `k` pairwise internally and edge-disjoint
  H-paths (`internal_disjoint` and `edge_disjoint`).
* `HCover G H` — a cover `(U, F)`, with vertices `U ⊆ V(G) \setminus
  V(H)$ and a set of edges $F \subseteq E(G)$ such that every H-path meets
  a vertex in $U$ or an edge in $F$.
* `HCover.cost` — the cover cost $|U| + \lfloor |F|/2 \rfloor$ (Diestel, p. 57).

## Main result

`mader_paths_le_cover_loose`: if `paths : HPaths G H k` and `C : HCover G H`,
then $k \le |U| + |F|$.

## References

* Diestel, *Graph Theory*, 5th ed., Theorem 3.4.1.
* Mader, W. (1978). Über die Maximalzahl kreuzungsfreier H-Wege.
  *Archiv der Mathematik* 31, 387-402.
-/

namespace SimpleGraph

variable {V : Type*}

/-! ## Definition of an H-path -/

/-- The internal vertices of a walk: all vertices in `support` except its
endpoints `u` and `v`. -/
def Walk.interior {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : List V :=
  p.support.tail.dropLast

/-- An **H-path** in `G` relative to `H ⊆ G` has both endpoints in `V(H)`,
internal vertices outside `V(H)`, and no edge in `E(H)` (Diestel §3.4, p. 56). -/
structure IsHPath (G : SimpleGraph V) (H : G.Subgraph)
    {u v : V} (p : G.Walk u v) : Prop where
  /-- `p` is a path in Mathlib's sense (no repeated vertices). -/
  isPath : p.IsPath
  /-- The start vertex lies in `V(H)`. -/
  start_mem : u ∈ H.verts
  /-- The end vertex lies in `V(H)`. -/
  finish_mem : v ∈ H.verts
  /-- Internal vertices lie outside `V(H)`. -/
  interior_disj : ∀ w ∈ p.interior, w ∉ H.verts
  /-- No edge of the path lies in `E(H)`. -/
  edges_disj : ∀ e ∈ p.edges, e ∉ H.edgeSet

/-- An H-path of length zero (`p = nil`) requires its vertex to lie in `H`.
This is the degenerate case. -/
lemma IsHPath.nil_iff {G : SimpleGraph V} {H : G.Subgraph} {u : V} :
    IsHPath G H (Walk.nil : G.Walk u u) ↔ u ∈ H.verts := by
  refine ⟨fun h => h.start_mem, fun hu => ?_⟩
  refine ⟨Walk.IsPath.nil, hu, hu, ?_, ?_⟩
  · intro w hw
    -- `Walk.nil.support = [u]`, so its interior list is empty.
    simp [Walk.interior, Walk.support_nil] at hw
  · intro e he
    -- Walk.nil.edges = []
    simp at he

/-! ## Definition of an H-cover -/

/-- **H-cover**: a pair `(U, F)` where `U ⊆ V(G) \\ V(H)` is a set of blocking
vertices and `F ⊆ E(G)` is a set of blocking edges, such that every H-path
meets a vertex in `U` or an edge in `F`.

(Diestel §3.4, p. 57. The condition `vertSet ⊆ V(G) \ V(H)` is represented by
`vertSet ∩ H.verts = ∅`.) -/
structure HCover (G : SimpleGraph V) (H : G.Subgraph) where
  /-- Blocking vertices, `U ⊆ V(G) \ V(H)`. -/
  vertSet : Set V
  /-- Blocking edges, `F ⊆ E(G)`. -/
  edgeSet : Set (Sym2 V)
  /-- `U` is disjoint from `V(H)`. -/
  vertSet_disj_H : ∀ x ∈ vertSet, x ∉ H.verts
  /-- `F` consists of edges of `G`. -/
  edgeSet_subset : edgeSet ⊆ G.edgeSet
  /-- Every H-path meets a vertex in `U` or an edge in `F`. -/
  covers : ∀ {u v : V} (p : G.Walk u v), IsHPath G H p →
    (∃ w ∈ p.support, w ∈ vertSet) ∨ (∃ e ∈ p.edges, e ∈ edgeSet)

/-- The cost of an H-cover is `|U| + ⌊|F|/2⌋` (Diestel, p. 57). The factor
`1/2` reflects that an edge `{x,y}` can block two internally disjoint H-paths
only when both endpoints are internal; Mader's full argument charges half
per edge. -/
noncomputable def HCover.cost {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCover G H) [Fintype C.vertSet] [Fintype C.edgeSet] :
    ℕ :=
  Fintype.card C.vertSet + Fintype.card C.edgeSet / 2

/-! ## Families of pairwise internally disjoint H-paths -/

/-- **A family of `k` pairwise internally disjoint H-paths** in `G` relative
to `H ⊆ G`. This follows `VertexDisjointPaths` in `Menger.lean`, but weakens
the endpoint conditions (different H-paths may share endpoints in `V(H)`) and
adds edge-disjointness:

* endpoints `u_i, v_i ∈ V(H)`; no `src_inj`/`dst_inj` requirement;
* distinct paths have no common internal vertex;
* distinct paths have no common edge.

**Edge note:** in Diestel §3.4, p. 56, internally disjoint H-paths are
internally vertex-disjoint. For paths of length at least two, this also
prevents shared edges. For a length-one path (an edge `u-v` with endpoints in
`V(H)`), the edge must occur at most once in the family; this is stated
explicitly by `edge_disjoint`. -/
structure HPaths (G : SimpleGraph V) (H : G.Subgraph) (k : ℕ) where
  /-- The start of path `i`. -/
  src : Fin k → V
  /-- The end of path `i`. -/
  dst : Fin k → V
  /-- Path `i`. -/
  walk : (i : Fin k) → G.Walk (src i) (dst i)
  /-- Every path is an H-path. -/
  isHPath : ∀ i, IsHPath G H (walk i)
  /-- Internal disjointness: no vertex is internal to two distinct paths. -/
  internal_disjoint : ∀ i j, i ≠ j →
    ∀ v, v ∈ (walk i).support → v ≠ src i → v ≠ dst i →
      v ∈ (walk j).support → v ≠ src j → v ≠ dst j → False
  /-- Edge disjointness: no edge belongs to two distinct paths in the family. -/
  edge_disjoint : ∀ i j, i ≠ j →
    ∀ e, e ∈ (walk i).edges → e ∉ (walk j).edges

/-! ## Cover witnesses: helpers for the `≤` direction

Every H-path covered by `C` has a witness: a vertex in `U` or an edge in `F`.
We show that witnesses for distinct paths are distinct, giving
`k ≤ |U| + |F|`. -/

/-- A vertex `w ∈ U` witnessing that `P` is covered by `U` is internal to
`P`, not an endpoint: `U` is disjoint from `V(H)`, while both endpoints lie
in `V(H)`. -/
lemma HCover.witness_vert_internal {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCover G H) {u v : V} {p : G.Walk u v}
    (hP : IsHPath G H p) {w : V}
    (hwU : w ∈ C.vertSet) (_hwS : w ∈ p.support) :
    w ≠ u ∧ w ≠ v := by
  refine ⟨fun heq => ?_, fun heq => ?_⟩
  · subst heq
    exact C.vertSet_disj_H w hwU hP.start_mem
  · subst heq
    exact C.vertSet_disj_H w hwU hP.finish_mem

/-- If an edge `e ∈ F` lies on an H-path `P`, both endpoints belong to
`P.support`. -/
lemma HCover.edge_endpoints_in_support {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} {x y : V} (he : s(x, y) ∈ p.edges) :
    x ∈ p.support ∧ y ∈ p.support :=
  ⟨p.fst_mem_support_of_mem_edges he, p.snd_mem_support_of_mem_edges he⟩

/-- **Edge-disjointness lemma:** an edge lying on two distinct paths in an
`HPaths` family contradicts its `edge_disjoint` field. -/
lemma HPaths.edge_witness_inj {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k)
    {i j : Fin k} (hij : i ≠ j) {e : Sym2 V}
    (hi : e ∈ (paths.walk i).edges)
    (hj : e ∈ (paths.walk j).edges) :
    False :=
  paths.edge_disjoint i j hij e hi hj

/-- **Vertex-disjointness lemma:** if `w ∈ U` witnesses two distinct paths
`P_i` and `P_j`, then `w ∉ V(H)` while their endpoints lie in `V(H)`. Thus
`w` is internal to both paths, contradicting `internal_disjoint`. -/
lemma HPaths.vert_witness_inj {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k)
    (C : HCover G H) {i j : Fin k} (hij : i ≠ j) {w : V}
    (hwU : w ∈ C.vertSet)
    (hi : w ∈ (paths.walk i).support)
    (hj : w ∈ (paths.walk j).support) :
    False := by
  -- w ∉ V(H) (bo U ∩ V(H) = ∅)
  have hwH : w ∉ H.verts := C.vertSet_disj_H w hwU
  -- The endpoints of `P_i` lie in `V(H)`, so `w` differs from both.
  have hPi := paths.isHPath i
  have hPj := paths.isHPath j
  have hwi_src : w ≠ paths.src i := fun heq => hwH (heq ▸ hPi.start_mem)
  have hwi_dst : w ≠ paths.dst i := fun heq => hwH (heq ▸ hPi.finish_mem)
  have hwj_src : w ≠ paths.src j := fun heq => hwH (heq ▸ hPj.start_mem)
  have hwj_dst : w ≠ paths.dst j := fun heq => hwH (heq ▸ hPj.finish_mem)
  exact paths.internal_disjoint i j hij w hi hwi_src hwi_dst hj hwj_src hwj_dst

/-! ## Constructing an injection into `U ⊕ F`

Choose one cover witness for each H-path: use a vertex in `U` if one exists;
otherwise use an edge in `F`. The resulting `witness : Fin k → U ⊕ F` is
injective, so `k ≤ |U| + |F|`. -/

/-- The cover witness for path `P_i`, represented by its kind and value. -/
noncomputable def HPaths.witness {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k) (C : HCover G H)
    (i : Fin k) : C.vertSet ⊕ C.edgeSet := by
  classical
  -- Prefer a vertex witness when one exists.
  by_cases h : ∃ w ∈ (paths.walk i).support, w ∈ C.vertSet
  · -- Choose one classically.
    let w := h.choose
    have hw := h.choose_spec
    exact Sum.inl ⟨w, hw.2⟩
  · -- Otherwise choose an edge witness.
    have hcov := C.covers (paths.walk i) (paths.isHPath i)
    have hedge : ∃ e ∈ (paths.walk i).edges, e ∈ C.edgeSet := by
      cases hcov with
      | inl hv => exact absurd hv h
      | inr he => exact he
    let e := hedge.choose
    have he := hedge.choose_spec
    exact Sum.inr ⟨e, he.2⟩

/-- A vertex witness belongs to the path's `support`. -/
lemma HPaths.witness_vert_mem_support {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k) (C : HCover G H)
    (i : Fin k) {w : C.vertSet} (hwit : paths.witness C i = Sum.inl w) :
    (w : V) ∈ (paths.walk i).support := by
  classical
  unfold HPaths.witness at hwit
  by_cases h : ∃ w' ∈ (paths.walk i).support, w' ∈ C.vertSet
  · rw [dif_pos h] at hwit
    have hspec := h.choose_spec
    have heq : w = (⟨h.choose, hspec.2⟩ : C.vertSet) := (Sum.inl.inj hwit).symm
    rw [heq]; exact hspec.1
  · rw [dif_neg h] at hwit
    exact absurd hwit Sum.inr_ne_inl

/-- An edge witness belongs to the path's `edges`. -/
lemma HPaths.witness_edge_mem_edges {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k) (C : HCover G H)
    (i : Fin k) {e : C.edgeSet} (hwit : paths.witness C i = Sum.inr e) :
    (e : Sym2 V) ∈ (paths.walk i).edges := by
  classical
  unfold HPaths.witness at hwit
  by_cases h : ∃ w' ∈ (paths.walk i).support, w' ∈ C.vertSet
  · rw [dif_pos h] at hwit
    exact absurd hwit Sum.inl_ne_inr
  · rw [dif_neg h] at hwit
    have hcov := C.covers (paths.walk i) (paths.isHPath i)
    have hedge : ∃ e' ∈ (paths.walk i).edges, e' ∈ C.edgeSet := by
      cases hcov with
      | inl hv => exact absurd hv h
      | inr he' => exact he'
    have hspec := hedge.choose_spec
    have heq : e = (⟨hedge.choose, hspec.2⟩ : C.edgeSet) := (Sum.inr.inj hwit).symm
    rw [heq]; exact hspec.1

/-- The witness function is injective. -/
lemma HPaths.witness_injective {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k) (C : HCover G H) :
    Function.Injective (paths.witness C) := by
  classical
  intro i j hij
  by_contra hne
  -- Split on the witness values.
  cases hwi : paths.witness C i with
  | inl wi =>
    cases hwj : paths.witness C j with
    | inl wj =>
      -- Both are vertex witnesses; `hij` implies `wi = wj`.
      have : Sum.inl wi = (Sum.inl wj : C.vertSet ⊕ C.edgeSet) := by
        rw [← hwi, ← hwj]; exact hij
      have heq : wi = wj := Sum.inl.inj this
      have hi := paths.witness_vert_mem_support C i hwi
      have hj := paths.witness_vert_mem_support C j hwj
      -- Apply `vert_witness_inj`.
      apply paths.vert_witness_inj C hne wi.2 hi
      rw [heq]; exact hj
    | inr ej =>
      -- The witness types differ, contradicting `hij`.
      rw [hwi, hwj] at hij
      exact Sum.inl_ne_inr hij
  | inr ei =>
    cases hwj : paths.witness C j with
    | inl wj =>
      rw [hwi, hwj] at hij
      exact Sum.inr_ne_inl hij
    | inr ej =>
      have : Sum.inr ei = (Sum.inr ej : C.vertSet ⊕ C.edgeSet) := by
        rw [← hwi, ← hwj]; exact hij
      have heq : ei = ej := Sum.inr.inj this
      have hi := paths.witness_edge_mem_edges C i hwi
      have hj := paths.witness_edge_mem_edges C j hwj
      apply paths.edge_witness_inj hne (e := (ei : Sym2 V)) hi
      rw [heq]; exact hj

/-! ## Mader's Theorem 3.4.1: the loose `≤` direction

For any H-cover `C = (U,F)`, a family of `k` pairwise internally and
edge-disjoint H-paths satisfies `k ≤ |U| + |F|`. Hence
`k ≤ 2 · cost(C)`. -/

/-- **Mader 3.4.1, loose `≤` direction** (Diestel §3.4, pp. 56–57): the
number of pairwise internally and edge-disjoint H-paths is at most `|U|+|F|`
for every H-cover `(U,F)`. -/
theorem mader_paths_le_cover_loose {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k) (C : HCover G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] :
    k ≤ Fintype.card C.vertSet + Fintype.card C.edgeSet := by
  classical
  -- Inject `Fin k` into `C.vertSet ⊕ C.edgeSet`.
  have hinj : Function.Injective (paths.witness C) := paths.witness_injective C
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (C.vertSet ⊕ C.edgeSet) :=
    Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_sum] at hcard
  exact hcard

/-! ## Full statement of Mader's Theorem 3.4.1

Diestel §3.4 states for **edge-disjoint** H-paths:
$$ \max\{k : \text{there are } k \text{ edge-disjoint H-paths}\}
   = \min\{|U| + \lfloor|F|/2\rfloor : (U, F) \text{ is an H-cover}\}. $$

**Strength of `HPaths`:** our definition requires both `internal_disjoint`
and `edge_disjoint`. For this stronger packing, the loose bound
`k ≤ |U| + |F|` is tight as stated, since each edge in `F` can witness at
most one path.

The factor `⌊|F|/2⌋` is relevant when paths are only edge-disjoint and may
share internal vertices: then each edge can witness at most two paths, one
through each endpoint. That weaker packing notion is not represented by the
current `HPaths` structure.

The results in this file are:

* The `≤` direction is proved by `mader_paths_le_cover_loose`, with bound
  `k ≤ |U| + |F|`; `maxHPaths_le_cover_loose` gives its maximum-size form.

* The reverse direction would construct an H-cover of cost equal to the
  maximum packing size. A classical approach reduces Mader to Menger by
  splitting each vertex of `V(H)` into source and sink copies; that direction
  is not proved here.
-/

/-! ## Maximum number of pairwise internally disjoint H-paths

For finite `V`, the set `{k | Nonempty (HPaths G H k)}` is nonempty (it
contains `0`) and bounded above, for example by the loose cover bound.
Define `maxHPaths` as its supremum. -/

/-- The set of sizes `k` for which an `HPaths G H k` family exists. -/
def hPathsSizes (G : SimpleGraph V) (H : G.Subgraph) : Set ℕ :=
  { k | Nonempty (HPaths G H k) }

/-- The set `hPathsSizes` contains `0`, represented by the empty family. -/
lemma hPathsSizes_nonempty (G : SimpleGraph V) (H : G.Subgraph) :
    (hPathsSizes G H).Nonempty :=
  ⟨0, ⟨{
    src := Fin.elim0
    dst := Fin.elim0
    walk := fun i => Fin.elim0 i
    isHPath := fun i => Fin.elim0 i
    internal_disjoint := fun i => Fin.elim0 i
    edge_disjoint := fun i => Fin.elim0 i
  }⟩⟩

set_option linter.unusedFintypeInType false in
/-- If an `HPaths G H k` family exists, then `k ≤ |U|+|F|` for any H-cover.
In particular, a trivial cover bounds `hPathsSizes G H` from above. -/
lemma hPathsSizes_bddAbove {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCover G H) [Fintype C.vertSet] [Fintype C.edgeSet] :
    BddAbove (hPathsSizes G H) := by
  refine ⟨Fintype.card C.vertSet + Fintype.card C.edgeSet, ?_⟩
  intro k hk
  obtain ⟨paths⟩ := hk
  exact mader_paths_le_cover_loose paths C

/-- The maximum size of a pairwise internally and edge-disjoint family of
H-paths in `G` relative to `H`. On a general vertex type this is defined as
the supremum in `Set ℕ`, which is `0` when the set is unbounded. An H-cover
provides the bound needed for this supremum to be attained. -/
noncomputable def maxHPaths (G : SimpleGraph V) (H : G.Subgraph) : ℕ :=
  sSup (hPathsSizes G H)

set_option linter.unusedFintypeInType false in
/-- The maximum `maxHPaths` is attained whenever the set of family sizes is
bounded above. -/
lemma maxHPaths_spec {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCover G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] :
    Nonempty (HPaths G H (maxHPaths G H)) := by
  have hbdd := hPathsSizes_bddAbove C
  have hne := hPathsSizes_nonempty G H
  have hmem : maxHPaths G H ∈ hPathsSizes G H :=
    Nat.sSup_mem hne hbdd
  exact hmem

set_option linter.unusedFintypeInType false in
/-- `maxHPaths` bounds the size of every `HPaths` family. -/
lemma le_maxHPaths {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPaths G H k)
    (C : HCover G H) [Fintype C.vertSet] [Fintype C.edgeSet] :
    k ≤ maxHPaths G H := by
  have hbdd := hPathsSizes_bddAbove C
  exact le_csSup hbdd ⟨paths⟩

/-- Mader's theorem, loose upper-bound direction: the maximum number of
pairwise internally disjoint H-paths is at most the loose cost of any
H-cover. -/
theorem maxHPaths_le_cover_loose {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCover G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] :
    maxHPaths G H ≤ Fintype.card C.vertSet + Fintype.card C.edgeSet := by
  classical
  obtain ⟨paths⟩ := maxHPaths_spec C
  exact mader_paths_le_cover_loose paths C

/-- Truncate an `HPaths` family of size `k'` to a subfamily of size `k ≤ k'`.
This follows the pattern of `VertexDisjointPaths.truncate` in `Menger.lean`. -/
noncomputable def HPaths.truncate {G : SimpleGraph V}
    {H : G.Subgraph} {k' : ℕ} (paths : HPaths G H k')
    (k : ℕ) (hle : k ≤ k') : HPaths G H k where
  src := fun i => paths.src (Fin.castLE hle i)
  dst := fun i => paths.dst (Fin.castLE hle i)
  walk := fun i => paths.walk (Fin.castLE hle i)
  isHPath := fun i => paths.isHPath (Fin.castLE hle i)
  internal_disjoint := fun i j hij v hvi hvis hvid hvj hvjs hvjd =>
    paths.internal_disjoint (Fin.castLE hle i) (Fin.castLE hle j)
      (fun heq => hij (Fin.castLE_injective hle heq))
      v hvi hvis hvid hvj hvjs hvjd
  edge_disjoint := fun i j hij e hei =>
    paths.edge_disjoint (Fin.castLE hle i) (Fin.castLE hle j)
      (fun heq => hij (Fin.castLE_injective hle heq)) e hei

set_option linter.unusedFintypeInType false in
/-- An `HPaths G H k` family exists exactly when `k ≤ maxHPaths G H`. -/
theorem nonempty_HPaths_iff_le_maxHPaths {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (C : HCover G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] :
    Nonempty (HPaths G H k) ↔ k ≤ maxHPaths G H := by
  refine ⟨fun ⟨paths⟩ => le_maxHPaths paths C, fun hle => ?_⟩
  obtain ⟨pathsMax⟩ := maxHPaths_spec C
  exact ⟨pathsMax.truncate k hle⟩

/-! ## Proper H-paths

In Diestel, an H-path "between" vertices of `V(H)` is implicitly nonempty.
The degenerate walk `nil` at a vertex `u ∈ V(H)` is not a meaningful path
between vertices and cannot be met by an `HCover`: its support is `[u]`,
`u ∈ V(H)`, and `HCover.vertSet` is disjoint from `V(H)`. The reverse
direction of Mader's theorem must exclude this case.

The reduction to Menger in the vertex-split graph `G'` also needs distinct
sources and targets, which `HPaths` does not guarantee because paths may share
endpoints in `V(H)`. -/

/-- A **proper H-path** is a nonempty H-path: it joins distinct vertices of
`V(H)`, or joins a vertex to itself by a nontrivial walk using edges outside
`E(H)`.

This excludes `Walk.nil`, which is not a path "between" vertices in Diestel's
convention and would not be covered by `HCover`. -/
structure IsHPathProper (G : SimpleGraph V) (H : G.Subgraph)
    {u v : V} (p : G.Walk u v) : Prop where
  /-- `p` is an H-path. -/
  toIsHPath : IsHPath G H p
  /-- `p` has positive length and is not `Walk.nil`. -/
  length_pos : 0 < p.length

/-- A proper H-path is not `Walk.nil`, which has length zero. -/
lemma IsHPathProper.not_nil_iff {G : SimpleGraph V} {H : G.Subgraph} {u : V} :
    ¬ IsHPathProper G H (Walk.nil : G.Walk u u) := by
  intro h
  have : (0 : ℕ) < (Walk.nil : G.Walk u u).length := h.length_pos
  simp [Walk.length_nil] at this

/-- **A family of proper H-paths with pairwise distinct endpoints.**

This strengthens `HPaths G H k`:
* each path is **proper** (`length_pos`, excluding `nil`);
* sources and targets are separately injective (`src_inj`, `dst_inj`).

The distinct-endpoint condition does not follow from `HPaths` and is needed
for the reduction to Menger: `VertexDisjointPaths` in `G'` requires
`src_inj`/`dst_inj`, since sources lie in `MaderA G H` and must remain
distinct in `MaderSplit G H`. -/
structure HPathsProperDisjEnds (G : SimpleGraph V) (H : G.Subgraph) (k : ℕ) where
  /-- The start of path `i`. -/
  src : Fin k → V
  /-- The end of path `i`. -/
  dst : Fin k → V
  /-- Path `i`. -/
  walk : (i : Fin k) → G.Walk (src i) (dst i)
  /-- Every path is proper (`IsHPath` plus positive length). -/
  isHPathProper : ∀ i, IsHPathProper G H (walk i)
  /-- Internal disjointness, as in `HPaths`. -/
  internal_disjoint : ∀ i j, i ≠ j →
    ∀ v, v ∈ (walk i).support → v ≠ src i → v ≠ dst i →
      v ∈ (walk j).support → v ≠ src j → v ≠ dst j → False
  /-- Edge disjointness, as in `HPaths`. -/
  edge_disjoint : ∀ i j, i ≠ j →
    ∀ e, e ∈ (walk i).edges → e ∉ (walk j).edges
  /-- Sources are pairwise distinct. -/
  src_inj : Function.Injective src
  /-- Targets are pairwise distinct. -/
  dst_inj : Function.Injective dst

/-- Forgetting `length_pos`, `src_inj`, and `dst_inj` converts
`HPathsProperDisjEnds` to `HPaths`, preserving both disjointness conditions. -/
def HPathsProperDisjEnds.toHPaths {G : SimpleGraph V} {H : G.Subgraph} {k : ℕ}
    (P : HPathsProperDisjEnds G H k) : HPaths G H k where
  src := P.src
  dst := P.dst
  walk := P.walk
  isHPath := fun i => (P.isHPathProper i).toIsHPath
  internal_disjoint := P.internal_disjoint
  edge_disjoint := P.edge_disjoint

/-- A **proper H-cover** is a variant of `HCover` that covers only proper
H-paths (`IsHPathProper`). When `V(H)` is nonempty, a classical `HCover`
cannot cover `Walk.nil` at `u ∈ V(H)`: its support is `[u]`, `vertSet` is
disjoint from `V(H)`, and its edge list is empty. `HCoverProper` avoids this by
requiring coverage only for paths of positive length.

The vertex-split construction can use an `A`–`B` separator in `G'` to build
an `HCoverProper` with `|U| + |F| ≤ 2|S|`. -/
structure HCoverProper (G : SimpleGraph V) (H : G.Subgraph) where
  /-- Blocking vertices, `U ⊆ V(G) \\ V(H)`. -/
  vertSet : Set V
  /-- Blocking edges, `F ⊆ E(G)`. -/
  edgeSet : Set (Sym2 V)
  /-- `U` is disjoint from `V(H)`. -/
  vertSet_disj_H : ∀ x ∈ vertSet, x ∉ H.verts
  /-- `F` consists of edges of `G`. -/
  edgeSet_subset : edgeSet ⊆ G.edgeSet
  /-- Every **proper** H-path meets a vertex in `U` or an edge in `F`. -/
  covers : ∀ {u v : V} (p : G.Walk u v), IsHPathProper G H p →
    (∃ w ∈ p.support, w ∈ vertSet) ∨ (∃ e ∈ p.edges, e ∈ edgeSet)

/-- The loose cost of a proper H-cover, `|U| + |F|`. -/
noncomputable def HCoverProper.cost {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCoverProper G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] : ℕ :=
  Fintype.card C.vertSet + Fintype.card C.edgeSet

/-- Convert `HCover` to `HCoverProper`: a classical cover also covers every
proper H-path, since these form a subset of all H-paths. -/
def HCover.toProper {G : SimpleGraph V} {H : G.Subgraph} (C : HCover G H) :
    HCoverProper G H where
  vertSet := C.vertSet
  edgeSet := C.edgeSet
  vertSet_disj_H := C.vertSet_disj_H
  edgeSet_subset := C.edgeSet_subset
  covers := fun p hP => C.covers p hP.toIsHPath

/-! ## The vertex-split graph

The classical reduction from Mader's theorem to Menger's theorem replaces
each vertex `h ∈ V(H)` by a pair `(h⁻, h⁺)`; vertices outside `H` remain
unchanged. Its edges are defined as follows:

* outside vertices retain their edges from `G`;
* an outside vertex `v` is joined to `h⁺` when `G.Adj v h`;
* `h⁻` and `h⁺` are joined by an internal edge;
* `h⁺` and `h'⁺` are joined when `G.Adj h h'` and the edge is not in `H`.

The sets `A := {h⁻ | h ∈ V(H)}` and `B := {h⁺ | h ∈ V(H)}` are disjoint.
This file defines the split graph and these terminal sets, together with
their basic cardinality and disjointness properties. -/

/-- Vertex type of the split graph: vertices outside `H` have one copy, and
each vertex of `H` has two copies encoded by `Bool`. -/
def MaderSplit {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) : Type _ :=
  {v : V // v ∉ H.verts} ⊕ ({v : V // v ∈ H.verts} × Bool)

namespace MaderSplit

variable {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}

/-- The unchanged copy of a vertex outside `H`. -/
abbrev outside (v : V) (hv : v ∉ H.verts) : MaderSplit G H :=
  Sum.inl ⟨v, hv⟩

/-- The minus copy of a vertex `h ∈ V(H)`. -/
abbrev minus (h : V) (hh : h ∈ H.verts) : MaderSplit G H :=
  Sum.inr (⟨h, hh⟩, false)

/-- The plus copy of a vertex `h ∈ V(H)`. -/
abbrev plus (h : V) (hh : h ∈ H.verts) : MaderSplit G H :=
  Sum.inr (⟨h, hh⟩, true)

noncomputable instance [Fintype V] : Fintype (MaderSplit G H) := by
  classical
  unfold MaderSplit
  infer_instance

noncomputable instance [DecidableEq V] : DecidableEq (MaderSplit G H) := by
  classical
  unfold MaderSplit
  infer_instance

end MaderSplit

/-- Adjacency relation in the vertex-split graph. See the section overview
above for the construction. -/
def MaderSplitAdj {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    MaderSplit G H → MaderSplit G H → Prop
  | Sum.inl ⟨v, _⟩, Sum.inl ⟨w, _⟩ => G.Adj v w
  | Sum.inl ⟨v, _⟩, Sum.inr (⟨h, _⟩, true) => G.Adj v h
  | Sum.inl _, Sum.inr (_, false) => False
  | Sum.inr (⟨h, _⟩, true), Sum.inl ⟨v, _⟩ => G.Adj h v
  | Sum.inr (_, false), Sum.inl _ => False
  | Sum.inr (⟨h, _⟩, false), Sum.inr (⟨h', _⟩, true) => h = h'
  | Sum.inr (⟨h, _⟩, true), Sum.inr (⟨h', _⟩, false) => h = h'
  | Sum.inr (⟨h, _⟩, true), Sum.inr (⟨h', _⟩, true) =>
      G.Adj h h' ∧ s(h, h') ∉ H.edgeSet ∧ h ≠ h'
  | Sum.inr (_, false), Sum.inr (_, false) => False

/-- The adjacency relation of the split graph is symmetric. -/
lemma maderSplitAdj_symm {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    Symmetric (MaderSplitAdj G H) := by
  intro x y h
  cases x with
  | inl xa =>
    cases y with
    | inl yb =>
      -- inl, inl: adjacency in G is symmetric
      exact h.symm
    | inr ybp =>
      obtain ⟨yh, side⟩ := ybp
      cases side with
      | false =>
        -- inl ↔ inr (·, false): Adj is False
        exact h.elim
      | true =>
        -- inl ↔ inr (·, true): Adj is G.Adj
        exact h.symm
  | inr xap =>
    obtain ⟨xh, sx⟩ := xap
    cases y with
    | inl yb =>
      cases sx with
      | false => exact h.elim
      | true => exact h.symm
    | inr ybp =>
      obtain ⟨yh, sy⟩ := ybp
      cases sx with
      | false =>
        cases sy with
        | false => exact h.elim
        | true =>
          -- (h, false) ↔ (h', true) with h = h' becomes (h', true) ↔ (h, false) with h' = h
          exact h.symm
      | true =>
        cases sy with
        | false => exact h.symm
        | true =>
          -- (h, true) ↔ (h', true): symmetric conjunction
          obtain ⟨hAdj, hEdge, hNe⟩ := h
          refine ⟨hAdj.symm, ?_, hNe.symm⟩
          rwa [Sym2.eq_swap]

/-- The adjacency relation of the split graph is irreflexive. -/
lemma maderSplitAdj_irrefl {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    Std.Irrefl (MaderSplitAdj G H) := by
  refine ⟨?_⟩
  intro x h
  cases x with
  | inl xa =>
    -- G.Adj v v is False
    exact G.irrefl h
  | inr xap =>
    obtain ⟨xh, sx⟩ := xap
    cases sx with
    | false =>
      -- (h, false) ↔ (h, false) is False by definition
      exact h.elim
    | true =>
      -- (h, true) ↔ (h, true): conjunction with h ≠ h
      exact h.2.2 rfl

/-- The graph obtained by splitting every vertex of `H` into a minus and a
plus copy, while retaining vertices outside `H`. Adjacency is defined by
`MaderSplitAdj`. -/
def MaderSplitGraph {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    SimpleGraph (MaderSplit G H) where
  Adj := MaderSplitAdj G H
  symm := maderSplitAdj_symm G H
  loopless := maderSplitAdj_irrefl G H

/-! ### Terminal sets `A` and `B` and their properties -/

/-- The set of all minus copies, used as the source side. -/
def MaderA {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    Set (MaderSplit G H) :=
  { x | ∃ (h : V) (hh : h ∈ H.verts), x = MaderSplit.minus (G := G) (H := H) h hh }

/-- The set of all plus copies, used as the target side. -/
def MaderB {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    Set (MaderSplit G H) :=
  { x | ∃ (h : V) (hh : h ∈ H.verts), x = MaderSplit.plus (G := G) (H := H) h hh }

/-- The terminal sets are disjoint because their copies have different `Bool` values. -/
lemma maderA_disjoint_maderB {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    Disjoint (MaderA G H) (MaderB G H) := by
  rw [Set.disjoint_iff]
  intro x hx
  obtain ⟨⟨h, hh, hxA⟩, ⟨h', hh', hxB⟩⟩ := hx
  -- hxA: x = inr (⟨h, hh⟩, false), hxB: x = inr (⟨h', hh'⟩, true)
  -- Combine: inr (⟨h, hh⟩, false) = inr (⟨h', hh'⟩, true), contradiction on Bool component
  have hxA' : x = (Sum.inr (⟨h, hh⟩, false) : MaderSplit G H) := hxA
  have hxB' : x = (Sum.inr (⟨h', hh'⟩, true) : MaderSplit G H) := hxB
  rw [hxA'] at hxB'
  -- now hxB' : Sum.inr (⟨h, hh⟩, false) = Sum.inr (⟨h', hh'⟩, true)
  injection hxB' with hxB''
  injection hxB'' with _ hbool
  -- hbool : false = true
  exact Bool.false_ne_true hbool |>.elim

/-- The `minus` map is injective on `H.verts`. -/
lemma maderSplit_minus_injective {V : Type*} {G : SimpleGraph V} {H : G.Subgraph} :
    Function.Injective
      (fun h : H.verts => MaderSplit.minus (G := G) (H := H) h.val h.property) := by
  intro a b hab
  -- Equality of minus copies identifies their underlying vertices.
  apply Subtype.ext
  have h1 : (Sum.inr (⟨a.val, a.property⟩, false) : MaderSplit G H) =
            Sum.inr (⟨b.val, b.property⟩, false) := hab
  injection h1 with h2
  injection h2 with h3 _
  -- h3 : ⟨a.val, _⟩ = ⟨b.val, _⟩
  exact Subtype.mk.inj h3

/-- The `plus` map is injective on `H.verts`. -/
lemma maderSplit_plus_injective {V : Type*} {G : SimpleGraph V} {H : G.Subgraph} :
    Function.Injective
      (fun h : H.verts => MaderSplit.plus (G := G) (H := H) h.val h.property) := by
  intro a b hab
  apply Subtype.ext
  have h1 : (Sum.inr (⟨a.val, a.property⟩, true) : MaderSplit G H) =
            Sum.inr (⟨b.val, b.property⟩, true) := hab
  injection h1 with h2
  injection h2 with h3 _
  exact Subtype.mk.inj h3

/-- `MaderA G H` is exactly the range of the `minus` map. -/
lemma maderA_eq_range {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    MaderA G H = Set.range
      (fun h : H.verts => MaderSplit.minus (G := G) (H := H) h.val h.property) := by
  ext x
  constructor
  · rintro ⟨h, hh, hx⟩
    exact ⟨⟨h, hh⟩, hx.symm⟩
  · rintro ⟨h, hx⟩
    exact ⟨h.val, h.property, hx.symm⟩

/-- `MaderB G H` is exactly the range of the `plus` map. -/
lemma maderB_eq_range {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    MaderB G H = Set.range
      (fun h : H.verts => MaderSplit.plus (G := G) (H := H) h.val h.property) := by
  ext x
  constructor
  · rintro ⟨h, hh, hx⟩
    exact ⟨⟨h, hh⟩, hx.symm⟩
  · rintro ⟨h, hx⟩
    exact ⟨h.val, h.property, hx.symm⟩

/-- Bijekcja `H.verts ≃ MaderA G H`. -/
noncomputable def maderAEquiv {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    H.verts ≃ MaderA G H :=
  -- Use the equivalence between an injective map and its range.
  (Equiv.ofInjective _ maderSplit_minus_injective).trans
    (Equiv.setCongr (maderA_eq_range G H).symm)

/-- Bijekcja `H.verts ≃ MaderB G H`. -/
noncomputable def maderBEquiv {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    H.verts ≃ MaderB G H :=
  (Equiv.ofInjective _ maderSplit_plus_injective).trans
    (Equiv.setCongr (maderB_eq_range G H).symm)

/-! ### Decidability and finite terminal sets

The Menger API requires decidable adjacency and finite terminal sets. The
following instances and conversions provide these structures for the split
graph and its source and target sets. -/

/-- Characterization of membership in `MaderA G H`: `x ∈ A` exactly when
`x = h⁻` for some `h ∈ V(H)`. -/
lemma mem_MaderA_iff {V : Type*} (G : SimpleGraph V) (H : G.Subgraph)
    (x : MaderSplit G H) :
    x ∈ MaderA G H ↔ ∃ (h : V) (hh : h ∈ H.verts),
      x = MaderSplit.minus (G := G) (H := H) h hh := Iff.rfl

/-- Characterization of membership in `MaderB G H`: `x ∈ B` exactly when
`x = h⁺` for some `h ∈ V(H)`. -/
lemma mem_MaderB_iff {V : Type*} (G : SimpleGraph V) (H : G.Subgraph)
    (x : MaderSplit G H) :
    x ∈ MaderB G H ↔ ∃ (h : V) (hh : h ∈ H.verts),
      x = MaderSplit.plus (G := G) (H := H) h hh := Iff.rfl

/-- Every minus copy belongs to `A`. -/
lemma minus_mem_MaderA {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (h : V) (hh : h ∈ H.verts) :
    MaderSplit.minus (G := G) (H := H) h hh ∈ MaderA G H :=
  ⟨h, hh, rfl⟩

/-- Every plus copy belongs to `B`. -/
lemma plus_mem_MaderB {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (h : V) (hh : h ∈ H.verts) :
    MaderSplit.plus (G := G) (H := H) h hh ∈ MaderB G H :=
  ⟨h, hh, rfl⟩

/-- An outside copy does not belong to `A`. -/
lemma outside_not_mem_MaderA {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (v : V) (hv : v ∉ H.verts) :
    MaderSplit.outside (G := G) (H := H) v hv ∉ MaderA G H := by
  rintro ⟨h, hh, hx⟩
  -- hx : Sum.inl ⟨v, hv⟩ = Sum.inr (⟨h, hh⟩, false)
  exact Sum.inl_ne_inr hx

/-- An outside copy does not belong to `B`. -/
lemma outside_not_mem_MaderB {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (v : V) (hv : v ∉ H.verts) :
    MaderSplit.outside (G := G) (H := H) v hv ∉ MaderB G H := by
  rintro ⟨h, hh, hx⟩
  exact Sum.inl_ne_inr hx

/-- A plus copy does not belong to `A`. -/
lemma plus_not_mem_MaderA {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (h : V) (hh : h ∈ H.verts) :
    MaderSplit.plus (G := G) (H := H) h hh ∉ MaderA G H := by
  rintro ⟨h', hh', hx⟩
  -- hx : Sum.inr (⟨h, hh⟩, true) = Sum.inr (⟨h', hh'⟩, false)
  injection hx with hx'
  injection hx' with _ hbool
  exact Bool.noConfusion hbool

/-- A minus copy does not belong to `B`. -/
lemma minus_not_mem_MaderB {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (h : V) (hh : h ∈ H.verts) :
    MaderSplit.minus (G := G) (H := H) h hh ∉ MaderB G H := by
  rintro ⟨h', hh', hx⟩
  injection hx with hx'
  injection hx' with _ hbool
  exact Bool.false_ne_true hbool

/-! ### Adjacency unfolding lemmas

The following lemmas unfold `MaderSplitGraph.Adj` for each constructor case.
They are used to lift paths and analyze separators in the split graph. -/

/-- The internal edge joins the two copies of each `h ∈ V(H)`. -/
lemma maderSplitGraph_adj_minus_plus {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h : V) (hh : h ∈ H.verts) :
    (MaderSplitGraph G H).Adj
      (MaderSplit.minus (G := G) (H := H) h hh)
      (MaderSplit.plus (G := G) (H := H) h hh) := by
  -- Adj (Sum.inr (<h, hh>, false)) (Sum.inr (<h, hh>, true)) = (h = h) = True
  rfl

/-- The internal edge in the reverse direction. -/
lemma maderSplitGraph_adj_plus_minus {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h : V) (hh : h ∈ H.verts) :
    (MaderSplitGraph G H).Adj
      (MaderSplit.plus (G := G) (H := H) h hh)
      (MaderSplit.minus (G := G) (H := H) h hh) :=
  (maderSplitGraph_adj_minus_plus G H h hh).symm

/-- Outside copies are adjacent in the split graph whenever their original
vertices are adjacent in `G`. -/
lemma maderSplitGraph_adj_outside_outside {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (v w : V) (hv : v ∉ H.verts) (hw : w ∉ H.verts)
    (hadj : G.Adj v w) :
    (MaderSplitGraph G H).Adj
      (MaderSplit.outside (G := G) (H := H) v hv)
      (MaderSplit.outside (G := G) (H := H) w hw) :=
  hadj

/-- An outside copy is adjacent to `h⁺` whenever the original vertices are
adjacent in `G`. -/
lemma maderSplitGraph_adj_outside_plus {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (v h : V) (hv : v ∉ H.verts) (hh : h ∈ H.verts)
    (hadj : G.Adj v h) :
    (MaderSplitGraph G H).Adj
      (MaderSplit.outside (G := G) (H := H) v hv)
      (MaderSplit.plus (G := G) (H := H) h hh) :=
  hadj

/-- The reverse outside-to-plus adjacency, by symmetry. -/
lemma maderSplitGraph_adj_plus_outside {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h v : V) (hh : h ∈ H.verts) (hv : v ∉ H.verts)
    (hadj : G.Adj h v) :
    (MaderSplitGraph G H).Adj
      (MaderSplit.plus (G := G) (H := H) h hh)
      (MaderSplit.outside (G := G) (H := H) v hv) :=
  (maderSplitGraph_adj_outside_plus G H v h hv hh hadj.symm).symm

/-- Plus copies are adjacent when their original edge lies in `G` but not in
`H`. -/
lemma maderSplitGraph_adj_plus_plus {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h h' : V) (hh : h ∈ H.verts) (hh' : h' ∈ H.verts)
    (hadj : G.Adj h h') (hne : s(h, h') ∉ H.edgeSet) :
    (MaderSplitGraph G H).Adj
      (MaderSplit.plus (G := G) (H := H) h hh)
      (MaderSplit.plus (G := G) (H := H) h' hh') :=
  ⟨hadj, hne, hadj.ne⟩

/-- Two minus copies are never adjacent. -/
lemma maderSplitGraph_not_adj_minus_minus {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h h' : V) (hh : h ∈ H.verts) (hh' : h' ∈ H.verts) :
    ¬ (MaderSplitGraph G H).Adj
      (MaderSplit.minus (G := G) (H := H) h hh)
      (MaderSplit.minus (G := G) (H := H) h' hh') := id

/-- An outside copy is never adjacent to a minus copy. -/
lemma maderSplitGraph_not_adj_outside_minus {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (v h : V) (hv : v ∉ H.verts) (hh : h ∈ H.verts) :
    ¬ (MaderSplitGraph G H).Adj
      (MaderSplit.outside (G := G) (H := H) v hv)
      (MaderSplit.minus (G := G) (H := H) h hh) := id

/-- The reverse non-adjacency, by symmetry. -/
lemma maderSplitGraph_not_adj_minus_outside {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h v : V) (hh : h ∈ H.verts) (hv : v ∉ H.verts) :
    ¬ (MaderSplitGraph G H).Adj
      (MaderSplit.minus (G := G) (H := H) h hh)
      (MaderSplit.outside (G := G) (H := H) v hv) := id

/-! ### Decidability instance dla `MaderSplitGraph.Adj`

With finite `V` and decidable equality, decidable adjacency in `G`, and
decidable membership in `H.verts` and `H.edgeSet`, adjacency in the split
graph is decidable. -/

/-- Decidability of `MaderSplitAdj`, hence of adjacency in the split graph. -/
instance maderSplitAdj_decidable {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : G.Subgraph)
    [DecidablePred (· ∈ H.edgeSet)] :
    DecidableRel (MaderSplitAdj G H) := by
  intro x y
  cases x with
  | inl xa =>
    cases y with
    | inl yb => exact (inferInstance : Decidable (G.Adj xa.val yb.val))
    | inr ybp =>
      obtain ⟨yh, sy⟩ := ybp
      cases sy with
      | false => exact (inferInstance : Decidable False)
      | true => exact (inferInstance : Decidable (G.Adj xa.val yh.val))
  | inr xap =>
    obtain ⟨xh, sx⟩ := xap
    cases y with
    | inl yb =>
      cases sx with
      | false => exact (inferInstance : Decidable False)
      | true => exact (inferInstance : Decidable (G.Adj xh.val yb.val))
    | inr ybp =>
      obtain ⟨yh, sy⟩ := ybp
      cases sx with
      | false =>
        cases sy with
        | false => exact (inferInstance : Decidable False)
        | true => exact (inferInstance : Decidable (xh.val = yh.val))
      | true =>
        cases sy with
        | false => exact (inferInstance : Decidable (xh.val = yh.val))
        | true =>
          exact (inferInstance :
            Decidable (G.Adj xh.val yh.val ∧ s(xh.val, yh.val) ∉ H.edgeSet ∧ xh.val ≠ yh.val))

instance maderSplitGraph_decidableAdj {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : G.Subgraph)
    [DecidablePred (· ∈ H.edgeSet)] :
    DecidableRel (MaderSplitGraph G H).Adj :=
  maderSplitAdj_decidable G H

/-! ### Finite instances and finite-set representations of `A` and `B` -/

/-- A finite instance for `MaderA`, obtained from its equivalence with `H.verts`. -/
noncomputable instance maderA_fintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] :
    Fintype (MaderA G H) := by
  classical
  exact Fintype.ofEquiv H.verts (maderAEquiv G H)

/-- A finite instance for `MaderB`. -/
noncomputable instance maderB_fintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] :
    Fintype (MaderB G H) := by
  classical
  exact Fintype.ofEquiv H.verts (maderBEquiv G H)

/-- The cardinality of `MaderA G H` equals that of `V(H)`. -/
lemma card_MaderA {V : Type*} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph)
    [DecidablePred (· ∈ H.verts)] :
    Fintype.card (MaderA G H) = Fintype.card H.verts := by
  classical
  exact (Fintype.card_congr (maderAEquiv G H)).symm

/-- The cardinality of `MaderB G H` equals that of `V(H)`. -/
lemma card_MaderB {V : Type*} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph)
    [DecidablePred (· ∈ H.verts)] :
    Fintype.card (MaderB G H) = Fintype.card H.verts := by
  classical
  exact (Fintype.card_congr (maderBEquiv G H)).symm

/-! ### Wersje `Finset` dla `MaderA` / `MaderB` (interfejs Mengera)

The Menger API accepts terminal sets as `Finset`s, so finite-set
representations of `A` and `B` are provided here. -/

/-- `MaderA G H` as a finite set for the Menger API. -/
noncomputable def MaderA.toFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] :
    Finset (MaderSplit G H) := by
  classical
  exact (MaderA G H).toFinset

/-- `MaderB G H` as a finite set. -/
noncomputable def MaderB.toFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] :
    Finset (MaderSplit G H) := by
  classical
  exact (MaderB G H).toFinset

/-- Membership in `MaderA.toFinset` is equivalent to membership in `MaderA`. -/
lemma mem_MaderA_toFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] (x : MaderSplit G H) :
    x ∈ MaderA.toFinset G H ↔ x ∈ MaderA G H := by
  classical
  unfold MaderA.toFinset
  exact Set.mem_toFinset

/-- Membership in `MaderB.toFinset` is equivalent to membership in `MaderB`. -/
lemma mem_MaderB_toFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] (x : MaderSplit G H) :
    x ∈ MaderB.toFinset G H ↔ x ∈ MaderB G H := by
  classical
  unfold MaderB.toFinset
  exact Set.mem_toFinset

/-- The finite sets representing `A` and `B` are disjoint. -/
lemma maderA_toFinset_disjoint_maderB_toFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] :
    Disjoint (MaderA.toFinset G H) (MaderB.toFinset G H) := by
  classical
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy
  rw [mem_MaderA_toFinset] at hx
  rw [mem_MaderB_toFinset] at hy
  -- Membership in the disjoint sets `A` and `B` implies inequality.
  intro hxy
  have hxAB : x ∈ MaderA G H ∩ MaderB G H := ⟨hx, hxy ▸ hy⟩
  have : (MaderA G H ∩ MaderB G H : Set _) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp (maderA_disjoint_maderB G H)
  rw [this] at hxAB
  exact hxAB

/-- The finite set representing `A` has cardinality `|V(H)|`. -/
lemma card_MaderA_toFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] :
    (MaderA.toFinset G H).card = Fintype.card H.verts := by
  classical
  unfold MaderA.toFinset
  rw [Set.toFinset_card]
  exact card_MaderA G H

/-- The finite set representing `B` has cardinality `|V(H)|`. -/
lemma card_MaderB_toFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : G.Subgraph) [DecidablePred (· ∈ H.verts)] :
    (MaderB.toFinset G H).card = Fintype.card H.verts := by
  classical
  unfold MaderB.toFinset
  rw [Set.toFinset_card]
  exact card_MaderB G H

/-! ### Walk constructors in the split graph

These helpers construct walks in the split graph from H-paths in `G`. -/

/-- The internal edge as a length-one walk from `h⁻` to `h⁺`. -/
def MaderSplit.internalEdgeWalk {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h : V) (hh : h ∈ H.verts) :
    (MaderSplitGraph G H).Walk
      (MaderSplit.minus (G := G) (H := H) h hh)
      (MaderSplit.plus (G := G) (H := H) h hh) :=
  Walk.cons (maderSplitGraph_adj_minus_plus G H h hh) Walk.nil

/-- The support of the internal edge walk is `[h⁻, h⁺]`. -/
@[simp] lemma MaderSplit.internalEdgeWalk_support {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h : V) (hh : h ∈ H.verts) :
    (MaderSplit.internalEdgeWalk G H h hh).support =
      [MaderSplit.minus (G := G) (H := H) h hh,
       MaderSplit.plus (G := G) (H := H) h hh] := by
  rfl

/-- The internal edge walk is a path: its two vertices are distinct. -/
lemma MaderSplit.internalEdgeWalk_isPath {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (h : V) (hh : h ∈ H.verts) :
    (MaderSplit.internalEdgeWalk G H h hh).IsPath := by
  unfold MaderSplit.internalEdgeWalk
  refine Walk.IsPath.cons Walk.IsPath.nil ?_
  -- Walk.nil.support = [plus h hh], minus h hh notin [plus h hh] (different Bool constructors)
  intro hmem
  simp only [Walk.support_nil, List.mem_singleton] at hmem
  injection hmem with hmem'
  injection hmem' with _ hbool
  exact Bool.noConfusion hbool

/-- A length-one H-path between vertices of `H` lifts to the length-two
walk `u⁻ → u⁺ → v⁺` in the split graph. -/
def MaderSplit.singleEdgeHPathWalk {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (u v : V) (hu : u ∈ H.verts) (hv : v ∈ H.verts)
    (hadj : G.Adj u v) (hne : s(u, v) ∉ H.edgeSet) :
    (MaderSplitGraph G H).Walk
      (MaderSplit.minus (G := G) (H := H) u hu)
      (MaderSplit.plus (G := G) (H := H) v hv) :=
  Walk.cons (maderSplitGraph_adj_minus_plus G H u hu)
    (Walk.cons (maderSplitGraph_adj_plus_plus G H u v hu hv hadj hne) Walk.nil)

/-- The support of this lifted walk is `[u⁻, u⁺, v⁺]`. -/
@[simp] lemma MaderSplit.singleEdgeHPathWalk_support {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (u v : V) (hu : u ∈ H.verts) (hv : v ∈ H.verts)
    (hadj : G.Adj u v) (hne : s(u, v) ∉ H.edgeSet) :
    (MaderSplit.singleEdgeHPathWalk G H u v hu hv hadj hne).support =
      [MaderSplit.minus (G := G) (H := H) u hu,
       MaderSplit.plus (G := G) (H := H) u hu,
       MaderSplit.plus (G := G) (H := H) v hv] := by
  rfl

/-- The lifted walk is a path: its three vertices are distinct by the copy
tags and `u ≠ v`.
z $G.\mathrm{Adj}\,u\,v$). -/
lemma MaderSplit.singleEdgeHPathWalk_isPath {V : Type*} (G : SimpleGraph V)
    (H : G.Subgraph) (u v : V) (hu : u ∈ H.verts) (hv : v ∈ H.verts)
    (hadj : G.Adj u v) (hne : s(u, v) ∉ H.edgeSet) :
    (MaderSplit.singleEdgeHPathWalk G H u v hu hv hadj hne).IsPath := by
  unfold MaderSplit.singleEdgeHPathWalk
  refine Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil ?_) ?_
  · -- Walk.nil at plus v, support = [plus v], plus u notin [plus v]
    intro hmem
    simp only [Walk.support_nil, List.mem_singleton] at hmem
    -- hmem : plus u hu = plus v hv => u = v => contradiction with Adj.ne
    injection hmem with hmem'
    injection hmem' with hpair _
    have huv : u = v := Subtype.mk.inj hpair
    exact hadj.ne huv
  · -- minus u hu notin support of (Walk.cons (plus u hu, plus v hv) Walk.nil)
    -- support = [plus u hu, plus v hv]
    intro hmem
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
               List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    · injection hmem with hmem'
      injection hmem' with _ hbool
      exact Bool.noConfusion hbool
    · injection hmem with hmem'
      injection hmem' with _ hbool
      exact Bool.noConfusion hbool

/-! ### Lifting H-paths to A-B walks in the split graph

An H-path lifts to a walk from `minus u` to `plus v`. Internal vertices
outside `H` map to outside copies. The recursive construction handles the
initial segment separately, then lifts the remaining tail. -/

/-- Lift the tail of an H-path, starting at an outside vertex and ending at
the plus copy of its endpoint. The result is a path with the stated support. -/
lemma MaderSplit.existsLiftedTail {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    ∀ {w v : V} (q : G.Walk w v) (_ : q.IsPath) (hw : w ∉ H.verts) (hv : v ∈ H.verts)
      (_ : ∀ x ∈ q.support, x ≠ w → x ≠ v → x ∉ H.verts)
      (_ : ∀ e ∈ q.edges, e ∉ H.edgeSet),
    ∃ q' : (MaderSplitGraph G H).Walk
      (MaderSplit.outside (G := G) (H := H) w hw)
      (MaderSplit.plus (G := G) (H := H) v hv),
      q'.IsPath ∧
      (∀ y ∈ q'.support,
        y = MaderSplit.plus (G := G) (H := H) v hv ∨
        ∃ z, ∃ hz : z ∉ H.verts,
          y = MaderSplit.outside (G := G) (H := H) z hz ∧ z ∈ q.support) := by
  intro w v q hpq hw hv hint hedges
  induction q with
  | nil =>
    -- The endpoint would be both inside and outside `H`.
    exact absurd hv hw
  | cons hadj q' ih =>
    rename_i u x v_end
    -- Here `w = u` and `v = v_end`.
    -- Obtain IsPath of q'
    have hpq' : q'.IsPath := (Walk.cons_isPath_iff _ _).mp hpq |>.1
    have hu_notin : u ∉ q'.support := (Walk.cons_isPath_iff _ _).mp hpq |>.2
    -- Split according to whether the next vertex is the endpoint.
    by_cases hxv : x = v_end
    · -- If the next vertex is the endpoint, the remaining path is nil.
      -- The lifted walk is the single edge from `outside u` to `plus x`.
      subst hxv
      -- After substitution, `hv : x ∈ H.verts` and `q' : G.Walk x x`.
      have hadj' : (MaderSplitGraph G H).Adj
          (MaderSplit.outside (G := G) (H := H) u hw)
          (MaderSplit.plus (G := G) (H := H) x hv) := by
        exact maderSplitGraph_adj_outside_plus G H u x hw hv hadj
      refine ⟨Walk.cons hadj' Walk.nil, ?_, ?_⟩
      · -- Prove the lifted walk is a path.
        refine Walk.IsPath.cons Walk.IsPath.nil ?_
        intro hmem
        simp only [Walk.support_nil, List.mem_singleton] at hmem
        exact Sum.inl_ne_inr hmem
      · -- Support description
        intro y hy
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                   List.not_mem_nil, or_false] at hy
        rcases hy with hy | hy
        · right
          refine ⟨u, hw, hy, ?_⟩
          simp [Walk.support_cons]
        · left; exact hy
    · -- Case B: x ≠ v_end. Then x is internal in q, so x ∉ H.verts.
      have hx_notin_H : x ∉ H.verts := by
        apply hint x ?_ ?_ hxv
        · -- x ∈ q.support
          simp [Walk.support_cons, Walk.start_mem_support]
        · -- x ≠ u (since u ∉ q'.support but x ∈ q'.support as start)
          intro hxu
          subst hxu
          exact hu_notin (Walk.start_mem_support _)
      -- Recursive call on q' (from x to v_end). Need: x ∉ H.verts, v_end ∈ H.verts (given),
      -- interior of q' ∉ H.verts, edges of q' ∉ H.edgeSet.
      have hint' : ∀ y ∈ q'.support, y ≠ x → y ≠ v_end → y ∉ H.verts := by
        intro y hy hyx hyv
        apply hint y ?_ ?_ hyv
        · simp [Walk.support_cons, hy]
        · intro hyu
          subst hyu
          exact hu_notin hy
      have hedges' : ∀ e ∈ q'.edges, e ∉ H.edgeSet := by
        intro e he
        apply hedges e
        simp [Walk.edges_cons, he]
      obtain ⟨liftedQ', hpQ', hsupp'⟩ := ih hpq' hx_notin_H hv hint' hedges'
      -- Build the cons: outside u → outside x is an edge in G' (G.Adj u x)
      have hadj' : (MaderSplitGraph G H).Adj
          (MaderSplit.outside (G := G) (H := H) u hw)
          (MaderSplit.outside (G := G) (H := H) x hx_notin_H) :=
        maderSplitGraph_adj_outside_outside G H u x hw hx_notin_H hadj
      refine ⟨Walk.cons hadj' liftedQ', ?_, ?_⟩
      · -- IsPath: liftedQ' is a path AND outside u ∉ liftedQ'.support
        refine Walk.IsPath.cons hpQ' ?_
        -- Suppose outside u ∈ liftedQ'.support. Then by hsupp', either outside u = plus v_end
        -- (impossible: Sum.inl ≠ Sum.inr) or outside u = outside z for some z ∈ q'.support.
        -- The second: z = u (by injectivity of outside), so u ∈ q'.support, contradicting hu_notin.
        intro hmem
        rcases hsupp' _ hmem with hcase | ⟨z, hz, heq, hzs⟩
        · exact Sum.inl_ne_inr hcase
        · -- heq : outside u hw = outside z hz, i.e. Sum.inl ⟨u, hw⟩ = Sum.inl ⟨z, hz⟩
          have huz : u = z := by
            have := Sum.inl.inj heq
            exact (Subtype.mk.inj this)
          subst huz
          exact hu_notin hzs
      · -- Support description
        intro y hy
        simp only [Walk.support_cons, List.mem_cons] at hy
        rcases hy with hy | hy
        · -- y = outside u → second branch
          right
          refine ⟨u, hw, hy, ?_⟩
          simp [Walk.support_cons]
        · -- y ∈ liftedQ'.support → use hsupp'
          rcases hsupp' _ hy with hcase | ⟨z, hz, heq, hzs⟩
          · left; exact hcase
          · right
            refine ⟨z, hz, heq, ?_⟩
            simp [Walk.support_cons, hzs]

/-- Lift an H-path to a path from the minus copy of its start to the plus
copy of its end. The support consists of endpoint copies and outside copies
of vertices in the original support. -/
lemma MaderSplit.existsLiftedFull {V : Type*} (G : SimpleGraph V) (H : G.Subgraph)
    {u v : V} (p : G.Walk u v) (hP : IsHPath G H p) :
    ∃ p' : (MaderSplitGraph G H).Walk
      (MaderSplit.minus (G := G) (H := H) u hP.start_mem)
      (MaderSplit.plus (G := G) (H := H) v hP.finish_mem),
      p'.IsPath ∧
      (∀ y ∈ p'.support,
        y = MaderSplit.minus (G := G) (H := H) u hP.start_mem ∨
        y = MaderSplit.plus (G := G) (H := H) u hP.start_mem ∨
        y = MaderSplit.plus (G := G) (H := H) v hP.finish_mem ∨
        ∃ z, ∃ hz : z ∉ H.verts,
          y = MaderSplit.outside (G := G) (H := H) z hz ∧ z ∈ p.support) := by
  -- Case on p: nil vs cons
  cases p with
  | nil =>
    -- p = Walk.nil : G.Walk u u. So v = u. Lifted walk is internal edge minus u → plus u.
    -- Note: hP.finish_mem = hP.start_mem since u = v.
    refine ⟨MaderSplit.internalEdgeWalk G H u hP.start_mem,
            MaderSplit.internalEdgeWalk_isPath G H u hP.start_mem, ?_⟩
    intro y hy
    rw [MaderSplit.internalEdgeWalk_support] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy
    · left; exact hy
    · right; left; exact hy
  | cons hadj p' =>
    rename_i x
    -- p = Walk.cons hadj p' with p' : G.Walk x v, hadj : G.Adj u x
    -- Case on whether x = v (length 1) or x ≠ v (longer)
    have hpP : (Walk.cons hadj p').IsPath := hP.isPath
    have hpP' : p'.IsPath := (Walk.cons_isPath_iff _ _).mp hpP |>.1
    have hu_notin' : u ∉ p'.support := (Walk.cons_isPath_iff _ _).mp hpP |>.2
    by_cases hxv : x = v
    · -- Length-1 H-path: u → v with G.Adj u v, s(u, v) ∉ E(H)
      subst hxv
      -- p' : G.Walk x x with IsPath, so p' = Walk.nil. Edge s(u, x) ∉ E(H) by hP.edges_disj.
      have hsne : s(u, x) ∉ H.edgeSet := by
        apply hP.edges_disj
        simp [Walk.edges_cons]
      -- Lifted walk: minus u → plus u → plus x via singleEdgeHPathWalk
      refine ⟨MaderSplit.singleEdgeHPathWalk G H u x hP.start_mem hP.finish_mem hadj hsne,
              MaderSplit.singleEdgeHPathWalk_isPath G H u x hP.start_mem hP.finish_mem hadj hsne,
              ?_⟩
      intro y hy
      rw [MaderSplit.singleEdgeHPathWalk_support] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy | hy
      · left; exact hy
      · right; left; exact hy
      · right; right; left; exact hy
    · -- Length ≥ 2: x is internal, so x ∉ V(H)
      have hx_notin_H : x ∉ H.verts := by
        -- x ∈ interior of p (cons hadj p'). interior = p.support.tail.dropLast.
        -- p.support = u :: p'.support. tail = p'.support. p'.support starts at x, ends at v.
        -- Since x ≠ v, x ∈ p'.support.dropLast (using mem_dropLast_of_mem_of_ne_getLast).
        apply hP.interior_disj
        unfold Walk.interior
        simp only [Walk.support_cons, List.tail_cons]
        have hp'_supp_ne : p'.support ≠ [] := p'.support_ne_nil
        have hx_mem_p' : x ∈ p'.support := Walk.start_mem_support _
        have hgetLast : p'.support.getLast hp'_supp_ne = v := Walk.getLast_support _
        apply List.mem_dropLast_of_mem_of_ne_getLast hx_mem_p'
        rw [hgetLast]
        exact hxv
      have hint_p' : ∀ y ∈ p'.support, y ≠ x → y ≠ v → y ∉ H.verts := by
        intro y hy hyx hyv
        -- y is internal in p (= cons hadj p'). show y ∈ interior of p.
        apply hP.interior_disj
        unfold Walk.interior
        simp only [Walk.support_cons, List.tail_cons]
        have hp'_supp_ne : p'.support ≠ [] := p'.support_ne_nil
        have hgetLast : p'.support.getLast hp'_supp_ne = v := Walk.getLast_support _
        apply List.mem_dropLast_of_mem_of_ne_getLast hy
        rw [hgetLast]
        exact hyv
      have hedges_p' : ∀ e ∈ p'.edges, e ∉ H.edgeSet := by
        intro e he
        apply hP.edges_disj
        simp [Walk.edges_cons, he]
      obtain ⟨liftedTail, hpTail, hsuppTail⟩ :=
        MaderSplit.existsLiftedTail G H p' hpP' hx_notin_H hP.finish_mem hint_p' hedges_p'
      -- Now build: minus u → plus u → outside x → ... → plus v.
      -- Use internalEdgeWalk (minus u → plus u), then edge plus u → outside x, then liftedTail.
      -- Edge plus u → outside x: maderSplitGraph_adj_plus_outside (with G.Adj u x).
      have hadj_plus_outside : (MaderSplitGraph G H).Adj
          (MaderSplit.plus (G := G) (H := H) u hP.start_mem)
          (MaderSplit.outside (G := G) (H := H) x hx_notin_H) :=
        maderSplitGraph_adj_plus_outside G H u x hP.start_mem hx_notin_H hadj
      -- Build: minus u → plus u → outside x → ... → plus v
      -- = cons (minus u → plus u) (cons (plus u → outside x) liftedTail)
      let liftedFull : (MaderSplitGraph G H).Walk
          (MaderSplit.minus (G := G) (H := H) u hP.start_mem)
          (MaderSplit.plus (G := G) (H := H) v hP.finish_mem) :=
        Walk.cons (maderSplitGraph_adj_minus_plus G H u hP.start_mem)
          (Walk.cons hadj_plus_outside liftedTail)
      refine ⟨liftedFull, ?_, ?_⟩
      · -- IsPath
        -- We need: tail (cons hadj_plus_outside liftedTail) is a path AND minus u ∉ its support.
        -- (a) Inner walk IsPath: liftedTail is a path AND plus u ∉ liftedTail.support.
        -- (b) Outer walk IsPath: minus u ∉ (cons hadj_plus_outside liftedTail).support.
        have h_plus_u_notin_tail :
            MaderSplit.plus (G := G) (H := H) u hP.start_mem ∉ liftedTail.support := by
          intro hmem
          rcases hsuppTail _ hmem with hcase | ⟨z, hz, heq, hzs⟩
          · -- plus u = plus v iff u = v. Then p : G.Walk u u, p' : G.Walk x u.
            -- u ∈ p'.support (as endpoint), but hu_notin' : u ∉ p'.support. Contradiction.
            have huv : u = v := by
              have := Sum.inr.inj hcase
              have := Prod.mk.inj this
              exact Subtype.mk.inj this.1
            subst huv
            exact hu_notin' (Walk.end_mem_support _)
          · -- plus u = outside z: Sum.inr ≠ Sum.inl, contradiction
            exact Sum.inr_ne_inl heq
        have h_inner_path : (Walk.cons hadj_plus_outside liftedTail).IsPath := by
          refine Walk.IsPath.cons hpTail ?_
          exact h_plus_u_notin_tail
        have h_minus_u_notin : MaderSplit.minus (G := G) (H := H) u hP.start_mem ∉
            (Walk.cons hadj_plus_outside liftedTail).support := by
          intro hmem
          simp only [Walk.support_cons, List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · -- minus u = plus u: false (Bool component differs)
            have := Sum.inr.inj hmem
            have := Prod.mk.inj this
            exact Bool.false_ne_true this.2
          · -- minus u ∈ liftedTail.support
            rcases hsuppTail _ hmem with hcase | ⟨z, hz, heq, hzs⟩
            · -- minus u = plus v: false (Bool false vs true)
              have := Sum.inr.inj hcase
              have := Prod.mk.inj this
              exact Bool.false_ne_true this.2
            · -- minus u = outside z: Sum.inr ≠ Sum.inl
              exact Sum.inr_ne_inl heq
        exact Walk.IsPath.cons h_inner_path h_minus_u_notin
      · -- Support description
        intro y hy
        -- liftedFull.support = minus u :: (cons hadj_plus_outside liftedTail).support
        --                    = minus u :: plus u :: liftedTail.support
        change y ∈ (Walk.cons (maderSplitGraph_adj_minus_plus G H u hP.start_mem)
            (Walk.cons hadj_plus_outside liftedTail)).support at hy
        simp only [Walk.support_cons, List.mem_cons] at hy
        rcases hy with hy | hy | hy
        · -- y = minus u
          left; exact hy
        · -- y = plus u
          right; left; exact hy
        · -- y ∈ liftedTail.support
          rcases hsuppTail _ hy with hcase | ⟨z, hz, heq, hzs⟩
          · -- y = plus v
            right; right; left; exact hcase
          · -- y = outside z, z ∈ p'.support → z ∈ p.support (cons branch)
            right; right; right
            refine ⟨z, hz, heq, ?_⟩
            simp [Walk.support_cons, hzs]

/-! ### Cardinality of `MaderSplit` -/

set_option linter.unusedFintypeInType false in
/-- `MaderSplit G H` has one copy of each vertex outside `H` and two copies
of each vertex in `H`. -/
lemma card_MaderSplit {V : Type*} (G : SimpleGraph V) (H : G.Subgraph)
    [Fintype V] [DecidablePred (· ∈ H.verts)] :
    Fintype.card (MaderSplit G H) =
      Fintype.card {v : V // v ∉ H.verts} +
      2 * Fintype.card {v : V // v ∈ H.verts} := by
  classical
  -- Unfolding `MaderSplit` gives the outside vertices and the two copies.
  have hcong :
      Fintype.card (MaderSplit G H) =
        Fintype.card ({v : V // v ∉ H.verts} ⊕ ({v : V // v ∈ H.verts} × Bool)) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcong, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  ring

/-! ## From proper H-path families to disjoint A-B paths

A family of proper H-paths with separately distinct sources and targets
induces a family of vertex-disjoint A-B paths in the split graph. -/

/-- A family of proper H-paths with pairwise distinct sources and targets
gives a family of vertex-disjoint A-B paths in the split graph.

Konstrukcja:
* Each H-path is lifted by `existsLiftedFull` to a walk from the minus copy
  of its source to the plus copy of its target.
* Sources and targets remain pairwise distinct by injectivity of the copy
  maps and the corresponding hypotheses on the original family.
* Internal disjointness follows by cases: equal plus copies force equal
  indices; plus and outside copies have different constructors; and a shared
  outside copy would be a shared internal vertex of the original H-paths. -/
noncomputable def mader_HPathsProperDisjEnds_to_VDP
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : G.Subgraph} [DecidablePred (· ∈ H.verts)]
    [DecidablePred (· ∈ H.edgeSet)]
    {k : ℕ} (paths : HPathsProperDisjEnds G H k) :
    (MaderSplitGraph G H).VertexDisjointPaths
      (MaderA.toFinset G H) (MaderB.toFinset G H) k := by
  classical
  -- Choose a lifted path for each index.
  let liftData : ∀ i : Fin k,
      { p' : (MaderSplitGraph G H).Walk
          (MaderSplit.minus (G := G) (H := H) (paths.src i)
            ((paths.isHPathProper i).toIsHPath.start_mem))
          (MaderSplit.plus (G := G) (H := H) (paths.dst i)
            ((paths.isHPathProper i).toIsHPath.finish_mem)) //
        p'.IsPath ∧
        (∀ y ∈ p'.support,
          y = MaderSplit.minus (G := G) (H := H) (paths.src i)
                ((paths.isHPathProper i).toIsHPath.start_mem) ∨
          y = MaderSplit.plus (G := G) (H := H) (paths.src i)
                ((paths.isHPathProper i).toIsHPath.start_mem) ∨
          y = MaderSplit.plus (G := G) (H := H) (paths.dst i)
                ((paths.isHPathProper i).toIsHPath.finish_mem) ∨
          ∃ z, ∃ hz : z ∉ H.verts,
            y = MaderSplit.outside (G := G) (H := H) z hz ∧
              z ∈ (paths.walk i).support) } := fun i => by
    have hex := MaderSplit.existsLiftedFull G H (paths.walk i)
                  (paths.isHPathProper i).toIsHPath
    exact ⟨Classical.choose hex,
           (Classical.choose_spec hex).1, (Classical.choose_spec hex).2⟩
  refine
    { src := fun i => MaderSplit.minus (G := G) (H := H) (paths.src i)
              ((paths.isHPathProper i).toIsHPath.start_mem)
      dst := fun i => MaderSplit.plus (G := G) (H := H) (paths.dst i)
              ((paths.isHPathProper i).toIsHPath.finish_mem)
      walk := fun i => (liftData i).val
      isPath := fun i => (liftData i).property.1
      src_mem := ?_
      dst_mem := ?_
      src_inj := ?_
      dst_inj := ?_
      internal_disjoint := ?_ }
  -- src_mem
  · intro i
    rw [mem_MaderA_toFinset]
    exact minus_mem_MaderA _ _
  -- dst_mem
  · intro i
    rw [mem_MaderB_toFinset]
    exact plus_mem_MaderB _ _
  -- src_inj
  · intro i j hij
    -- minus (paths.src i) ... = minus (paths.src j) ... ⇒ paths.src i = paths.src j ⇒ i = j
    have hsrc : paths.src i = paths.src j := by
      -- Use maderSplit_minus_injective: minus is injective on subtypes
      -- hij has type minus (...) = minus (...) which involves Subtype.mk
      -- We can extract paths.src i = paths.src j directly via injection.
      have h1 : (Sum.inr (⟨paths.src i, _⟩, false) : MaderSplit G H) =
                Sum.inr (⟨paths.src j, _⟩, false) := hij
      injection h1 with h2
      injection h2 with h3 _
      exact Subtype.mk.inj h3
    exact paths.src_inj hsrc
  -- dst_inj
  · intro i j hij
    have hdst : paths.dst i = paths.dst j := by
      have h1 : (Sum.inr (⟨paths.dst i, _⟩, true) : MaderSplit G H) =
                Sum.inr (⟨paths.dst j, _⟩, true) := hij
      injection h1 with h2
      injection h2 with h3 _
      exact Subtype.mk.inj h3
    exact paths.dst_inj hdst
  -- internal_disjoint
  · intro i j hij v hvi hvi_src hvi_dst hvj hvj_src hvj_dst
    -- v in lifted i support, v ≠ minus(src i), v ≠ plus(dst i)
    -- by description, v is plus(src i) or outside z_i
    -- analogously for j
    rcases (liftData i).property.2 v hvi with
      hcase_i | hcase_i | hcase_i | ⟨z_i, hz_i, heq_i, hz_i_supp⟩
    · -- v = minus(src i): contradicts hvi_src
      exact hvi_src hcase_i
    · -- v = plus(src i): analyze j cases
      rcases (liftData j).property.2 v hvj with
        hcase_j | hcase_j | hcase_j | ⟨z_j, hz_j, heq_j, hz_j_supp⟩
      · -- v = minus(src j): contradicts hvj_src
        exact hvj_src hcase_j
      · -- v = plus(src j): plus(src i) = plus(src j) ⇒ src i = src j ⇒ i = j
        have hcombined :
            (MaderSplit.plus (G := G) (H := H) (paths.src i) _ : MaderSplit G H) =
            MaderSplit.plus (G := G) (H := H) (paths.src j) _ := hcase_i ▸ hcase_j
        have hsrc_eq : paths.src i = paths.src j := by
          have h1 : (Sum.inr (⟨paths.src i, _⟩, true) : MaderSplit G H) =
                    Sum.inr (⟨paths.src j, _⟩, true) := hcombined
          injection h1 with h2
          injection h2 with h3 _
          exact Subtype.mk.inj h3
        exact hij (paths.src_inj hsrc_eq)
      · -- v = plus(dst j): contradicts hvj_dst
        exact hvj_dst hcase_j
      · -- v = outside z_j: plus(src i) = outside z_j → Sum.inr ≠ Sum.inl
        have : (MaderSplit.plus (G := G) (H := H) (paths.src i) _ : MaderSplit G H) =
               MaderSplit.outside (G := G) (H := H) z_j hz_j := hcase_i ▸ heq_j
        exact Sum.inr_ne_inl this
    · -- v = plus(dst i): contradicts hvi_dst
      exact hvi_dst hcase_i
    · -- v = outside z_i, z_i ∉ V(H), z_i ∈ paths.walk i .support
      rcases (liftData j).property.2 v hvj with
        hcase_j | hcase_j | hcase_j | ⟨z_j, hz_j, heq_j, hz_j_supp⟩
      · -- v = minus(src j)
        exact hvj_src hcase_j
      · -- v = plus(src j): outside z_i = plus(src j)
        have : (MaderSplit.outside (G := G) (H := H) z_i hz_i : MaderSplit G H) =
               MaderSplit.plus (G := G) (H := H) (paths.src j) _ := heq_i ▸ hcase_j
        exact Sum.inl_ne_inr this
      · -- v = plus(dst j)
        exact hvj_dst hcase_j
      · -- v = outside z_j: outside z_i = outside z_j ⇒ z_i = z_j
        have hcombined : (MaderSplit.outside (G := G) (H := H) z_i hz_i : MaderSplit G H) =
                         MaderSplit.outside (G := G) (H := H) z_j hz_j := heq_i ▸ heq_j
        have hzij : z_i = z_j := by
          have h1 : (Sum.inl ⟨z_i, hz_i⟩ : MaderSplit G H) =
                    Sum.inl ⟨z_j, hz_j⟩ := hcombined
          injection h1 with h2
          exact Subtype.mk.inj h2
        subst hzij
        -- Now z_i ∈ paths.walk i .support ∩ paths.walk j .support, z_i ∉ V(H)
        -- Apply internal_disjoint of HPathsProperDisjEnds:
        -- z_i ≠ src i (because src i ∈ V(H), z_i ∉ V(H))
        have hne_si : z_i ≠ paths.src i := fun heq =>
          hz_i (heq ▸ (paths.isHPathProper i).toIsHPath.start_mem)
        have hne_di : z_i ≠ paths.dst i := fun heq =>
          hz_i (heq ▸ (paths.isHPathProper i).toIsHPath.finish_mem)
        have hne_sj : z_i ≠ paths.src j := fun heq =>
          hz_i (heq ▸ (paths.isHPathProper j).toIsHPath.start_mem)
        have hne_dj : z_i ≠ paths.dst j := fun heq =>
          hz_i (heq ▸ (paths.isHPathProper j).toIsHPath.finish_mem)
        exact paths.internal_disjoint i j hij z_i hz_i_supp hne_si hne_di
                hz_j_supp hne_sj hne_dj

/-! ## From an A-B separator to a proper H-cover

An A-B separator in the split graph yields a proper H-cover in `G` with
loose cost at most twice the separator size. -/

/-- An A-B separator `S` yields a proper H-cover `(U, F)` in `G`, where
* $U = \{w \in V \setminus V(H) : \mathrm{outside}\,w \in S\}$;
* $F = \{e \in E(G) \setminus E(H) : \exists h \in V(H), h \in e \land
  (\mathrm{minus}\,h \in S \lor \mathrm{plus}\,h \in S)\}$.

Coverage follows by lifting a proper H-path from `minus u` to `plus v` and
using the separator-hit lemma. An outside-copy hit gives a vertex witness;
a hit at an endpoint copy gives an incident first or last edge. Positive
path length ensures that these edges exist. -/
noncomputable def mader_AB_separator_to_HCoverProper
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : G.Subgraph} [DecidablePred (· ∈ H.verts)]
    [DecidablePred (· ∈ H.edgeSet)]
    {S : Finset (MaderSplit G H)}
    (hS : (MaderSplitGraph G H).IsABSeparator
            (MaderA.toFinset G H) (MaderB.toFinset G H) S) :
    HCoverProper G H where
  vertSet := { w : V | ∃ hw : w ∉ H.verts,
                MaderSplit.outside (G := G) (H := H) w hw ∈ S }
  edgeSet := { e : Sym2 V | e ∈ G.edgeSet ∧ e ∉ H.edgeSet ∧
                ∃ h : V, ∃ hh : h ∈ H.verts, h ∈ e ∧
                  (MaderSplit.minus (G := G) (H := H) h hh ∈ S ∨
                   MaderSplit.plus (G := G) (H := H) h hh ∈ S) }
  vertSet_disj_H := by
    intro x ⟨hx_not, _⟩
    exact hx_not
  edgeSet_subset := by
    intro e ⟨he_G, _, _⟩
    exact he_G
  covers := by
    intro u v p hPP
    -- A proper H-path has positive length.
    have hP : IsHPath G H p := hPP.toIsHPath
    have hpos : 0 < p.length := hPP.length_pos
    -- Lift `p` to the split graph.
    obtain ⟨p', hp'_path, hp'_supp⟩ := MaderSplit.existsLiftedFull G H p hP
    -- The lifted endpoints belong to the two terminal sets.
    have h_minus_u_inA : MaderSplit.minus (G := G) (H := H) u hP.start_mem ∈
        MaderA.toFinset G H := by
      rw [mem_MaderA_toFinset]; exact minus_mem_MaderA _ _
    have h_plus_v_inB : MaderSplit.plus (G := G) (H := H) v hP.finish_mem ∈
        MaderB.toFinset G H := by
      rw [mem_MaderB_toFinset]; exact plus_mem_MaderB _ _
    -- The lifted walk meets the separator.
    obtain ⟨s, hs_supp, hs_S⟩ := walk_hits_separator hS h_minus_u_inA h_plus_v_inB p'
    -- s in {minus u, plus u, plus v, outside z}
    rcases hp'_supp s hs_supp with
      hcase_su | hcase_pu | hcase_pv | ⟨z, hz, heq, hz_supp⟩
    · -- A hit at `minus u` gives the first edge of `p`.
      have hexists_first : ∃ x, s(u, x) ∈ p.edges ∧ G.Adj u x := by
        match p, hpos with
        | Walk.cons (v := v') hadj _, _ => exact ⟨v', by simp [Walk.edges_cons], hadj⟩
      obtain ⟨x, hx_edge, hx_adj⟩ := hexists_first
      right
      refine ⟨s(u, x), hx_edge, ?_, ?_, u, hP.start_mem, ?_, ?_⟩
      · exact (SimpleGraph.mem_edgeSet G).mpr hx_adj
      · exact hP.edges_disj _ hx_edge
      · exact Sym2.mem_mk_left u x
      · left
        exact hcase_su ▸ hs_S
    · -- A hit at `plus u` also gives the first edge of `p`.
      have hexists_first : ∃ x, s(u, x) ∈ p.edges ∧ G.Adj u x := by
        match p, hpos with
        | Walk.cons (v := v') hadj _, _ => exact ⟨v', by simp [Walk.edges_cons], hadj⟩
      obtain ⟨x, hx_edge, hx_adj⟩ := hexists_first
      right
      refine ⟨s(u, x), hx_edge, ?_, ?_, u, hP.start_mem, ?_, ?_⟩
      · exact (SimpleGraph.mem_edgeSet G).mpr hx_adj
      · exact hP.edges_disj _ hx_edge
      · exact Sym2.mem_mk_left u x
      · right
        exact hcase_pu ▸ hs_S
    · -- A hit at `plus v` gives the last edge of `p`.
      have hexists_last : ∀ {a b : V} (q : G.Walk a b), 0 < q.length →
          ∃ y, s(y, b) ∈ q.edges ∧ G.Adj y b := by
        intro a b q hq
        induction q with
        | nil => simp [Walk.length_nil] at hq
        | cons hadj q' ih =>
          rename_i a' x' b'
          by_cases hq'_zero : q'.length = 0
          · -- If `q'` has length zero, then it is nil and `x' = b'`.
            have hxb : x' = b' := by
              cases q' with
              | nil => rfl
              | cons _ _ => simp [Walk.length_cons] at hq'_zero
            subst hxb
            refine ⟨a', ?_, hadj⟩
            cases q' with
            | nil => simp [Walk.edges_cons, Walk.edges_nil]
            | cons _ _ => simp [Walk.length_cons] at hq'_zero
          · have hq'_pos : 0 < q'.length := Nat.pos_of_ne_zero hq'_zero
            obtain ⟨y, hy, hyadj⟩ := ih hq'_pos
            refine ⟨y, ?_, hyadj⟩
            simp [Walk.edges_cons, hy]
      obtain ⟨y, hy_edge, hy_adj⟩ := hexists_last p hpos
      right
      refine ⟨s(y, v), hy_edge, ?_, ?_, v, hP.finish_mem, ?_, ?_⟩
      · exact (SimpleGraph.mem_edgeSet G).mpr hy_adj
      · exact hP.edges_disj _ hy_edge
      · exact Sym2.mem_mk_right y v
      · right
        exact hcase_pv ▸ hs_S
    · -- An outside-copy hit gives a vertex of the cover.
      left
      refine ⟨z, hz_supp, ?_⟩
      refine ⟨hz, ?_⟩
      exact heq ▸ hs_S

/-! ## The loose upper bound for proper H-covers

Each path has a vertex or edge cover witness. Pairwise disjointness makes
these witnesses injective and gives `k ≤ |U| + |F|`. -/

/-- Choose a cover witness for the `i`th proper H-path, preferring a vertex
witness when one is available. -/
noncomputable def HPathsProperDisjEnds.witnessProper {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPathsProperDisjEnds G H k)
    (C : HCoverProper G H) (i : Fin k) : C.vertSet ⊕ C.edgeSet := by
  classical
  by_cases hvert : ∃ w ∈ (paths.walk i).support, w ∈ C.vertSet
  · exact Sum.inl ⟨Classical.choose hvert, (Classical.choose_spec hvert).2⟩
  · -- If no vertex witness exists, the cover condition supplies an edge.
    have hedge : ∃ e ∈ (paths.walk i).edges, e ∈ C.edgeSet := by
      rcases C.covers (paths.walk i) (paths.isHPathProper i) with h | h
      · exact absurd h hvert
      · exact h
    exact Sum.inr ⟨Classical.choose hedge, (Classical.choose_spec hedge).2⟩

/-- If the chosen witness is a vertex, it lies on the corresponding walk. -/
lemma HPathsProperDisjEnds.witnessProper_vert_mem_support {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPathsProperDisjEnds G H k)
    (C : HCoverProper G H) (i : Fin k) {w : C.vertSet}
    (hw : paths.witnessProper C i = Sum.inl w) :
    (w : V) ∈ (paths.walk i).support := by
  classical
  unfold HPathsProperDisjEnds.witnessProper at hw
  by_cases hvert : ∃ w ∈ (paths.walk i).support, w ∈ C.vertSet
  · simp only [hvert, dif_pos] at hw
    have hspec := Classical.choose_spec hvert
    have hw_eq : (w : V) = Classical.choose hvert := by
      have := Sum.inl.inj hw
      exact (Subtype.mk.inj this).symm
    rw [hw_eq]; exact hspec.1
  · simp only [hvert, dif_neg, not_false_eq_true] at hw
    -- This branch yields an edge witness, contradicting the assumed vertex witness.
    exact absurd hw.symm (Sum.inl_ne_inr)

/-- If the chosen witness is an edge, it lies on the corresponding walk. -/
lemma HPathsProperDisjEnds.witnessProper_edge_mem_edges {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPathsProperDisjEnds G H k)
    (C : HCoverProper G H) (i : Fin k) {e : C.edgeSet}
    (he : paths.witnessProper C i = Sum.inr e) :
    (e : Sym2 V) ∈ (paths.walk i).edges := by
  classical
  unfold HPathsProperDisjEnds.witnessProper at he
  by_cases hvert : ∃ w ∈ (paths.walk i).support, w ∈ C.vertSet
  · simp only [hvert, dif_pos] at he
    -- The two sum constructors cannot be equal.
    exact absurd he Sum.inl_ne_inr
  · simp only [hvert, dif_neg, not_false_eq_true] at he
    have hedge : ∃ e ∈ (paths.walk i).edges, e ∈ C.edgeSet := by
      rcases C.covers (paths.walk i) (paths.isHPathProper i) with h | h
      · exact absurd h hvert
      · exact h
    have hspec := Classical.choose_spec hedge
    have he_eq : (e : Sym2 V) = Classical.choose hedge := by
      have := Sum.inr.inj he
      exact (Subtype.mk.inj this).symm
    rw [he_eq]; exact hspec.1

/-- Distinct paths have distinct witnesses: vertex witnesses are internal
vertices outside `H`, and edge witnesses are separated by edge-disjointness. -/
lemma HPathsProperDisjEnds.witnessProper_injective {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPathsProperDisjEnds G H k)
    (C : HCoverProper G H) :
    Function.Injective (paths.witnessProper C) := by
  classical
  intro i j hij
  by_contra hne
  -- Cases on witness type at i
  match hi : paths.witnessProper C i, hj : paths.witnessProper C j with
  | Sum.inl w, Sum.inl w' =>
    -- Both witnesses are vertices, and equality identifies them.
    have hw_eq : (w : V) = (w' : V) := by
      rw [hi, hj] at hij
      have := Sum.inl.inj hij
      exact congrArg Subtype.val this
    have hwi : (w : V) ∈ (paths.walk i).support :=
      paths.witnessProper_vert_mem_support C i hi
    have hwj : (w' : V) ∈ (paths.walk j).support :=
      paths.witnessProper_vert_mem_support C j hj
    have hw_U : (w : V) ∈ C.vertSet := w.property
    have hw_nH : (w : V) ∉ H.verts := C.vertSet_disj_H _ hw_U
    have hne_si : (w : V) ≠ paths.src i := fun heq =>
      hw_nH (heq ▸ (paths.isHPathProper i).toIsHPath.start_mem)
    have hne_di : (w : V) ≠ paths.dst i := fun heq =>
      hw_nH (heq ▸ (paths.isHPathProper i).toIsHPath.finish_mem)
    have hne_sj : (w : V) ≠ paths.src j := fun heq =>
      hw_nH (heq ▸ (paths.isHPathProper j).toIsHPath.start_mem)
    have hne_dj : (w : V) ≠ paths.dst j := fun heq =>
      hw_nH (heq ▸ (paths.isHPathProper j).toIsHPath.finish_mem)
    have hwi_in_j : (w : V) ∈ (paths.walk j).support := hw_eq ▸ hwj
    exact paths.internal_disjoint i j hne (w : V) hwi hne_si hne_di
            hwi_in_j hne_sj hne_dj
  | Sum.inl w, Sum.inr e =>
    rw [hi, hj] at hij; exact Sum.inl_ne_inr hij
  | Sum.inr e, Sum.inl w =>
    rw [hi, hj] at hij; exact Sum.inr_ne_inl hij
  | Sum.inr e, Sum.inr e' =>
    have he_eq : (e : Sym2 V) = (e' : Sym2 V) := by
      rw [hi, hj] at hij
      have := Sum.inr.inj hij
      exact congrArg Subtype.val this
    have hei : (e : Sym2 V) ∈ (paths.walk i).edges :=
      paths.witnessProper_edge_mem_edges C i hi
    have hej : (e' : Sym2 V) ∈ (paths.walk j).edges :=
      paths.witnessProper_edge_mem_edges C j hj
    have hei_in_j : (e : Sym2 V) ∈ (paths.walk j).edges := he_eq ▸ hej
    exact paths.edge_disjoint i j hne (e : Sym2 V) hei hei_in_j

/-- Loose upper-bound direction: a family of proper H-paths with distinct
endpoints has size at most the cost `|U| + |F|` of any proper cover. -/
theorem mader_proper_paths_le_coverProper_loose {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPathsProperDisjEnds G H k)
    (C : HCoverProper G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] :
    k ≤ Fintype.card C.vertSet + Fintype.card C.edgeSet := by
  classical
  have hinj : Function.Injective (paths.witnessProper C) :=
    paths.witnessProper_injective C
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (C.vertSet ⊕ C.edgeSet) :=
    Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_sum] at hcard
  exact hcard

/-! ## Extremal sizes for proper paths and covers

The maximum proper-path family size is the supremum of attainable sizes; the
minimum proper-cover cost is the infimum of finite cover costs. -/

/-- The set of sizes for which a proper H-path family exists. -/
def hPathsProperSizes (G : SimpleGraph V) (H : G.Subgraph) : Set ℕ :=
  { k | Nonempty (HPathsProperDisjEnds G H k) }

/-- The empty family shows that `hPathsProperSizes` contains `0`. -/
lemma hPathsProperSizes_nonempty (G : SimpleGraph V) (H : G.Subgraph) :
    (hPathsProperSizes G H).Nonempty :=
  ⟨0, ⟨{
    src := Fin.elim0
    dst := Fin.elim0
    walk := fun i => Fin.elim0 i
    isHPathProper := fun i => Fin.elim0 i
    internal_disjoint := fun i => Fin.elim0 i
    edge_disjoint := fun i => Fin.elim0 i
    src_inj := fun i => Fin.elim0 i
    dst_inj := fun i => Fin.elim0 i
  }⟩⟩

set_option linter.unusedFintypeInType false in
/-- A proper cover bounds the set of proper-path family sizes by its cost. -/
lemma hPathsProperSizes_bddAbove {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCoverProper G H) [Fintype C.vertSet] [Fintype C.edgeSet] :
    BddAbove (hPathsProperSizes G H) := by
  refine ⟨Fintype.card C.vertSet + Fintype.card C.edgeSet, ?_⟩
  intro k hk
  obtain ⟨paths⟩ := hk
  exact mader_proper_paths_le_coverProper_loose paths C

/-- The maximum size of a family of pairwise internally and edge-disjoint
proper H-paths with separately distinct endpoints. -/
noncomputable def maxHPathsProper (G : SimpleGraph V) (H : G.Subgraph) : ℕ :=
  sSup (hPathsProperSizes G H)

set_option linter.unusedFintypeInType false in
/-- The supremum `maxHPathsProper` is attained when a proper cover bounds the
set of attainable sizes. -/
lemma maxHPathsProper_spec {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCoverProper G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] :
    Nonempty (HPathsProperDisjEnds G H (maxHPathsProper G H)) := by
  have hbdd := hPathsProperSizes_bddAbove C
  have hne := hPathsProperSizes_nonempty G H
  have hmem : maxHPathsProper G H ∈ hPathsProperSizes G H :=
    Nat.sSup_mem hne hbdd
  exact hmem

set_option linter.unusedFintypeInType false in
/-- `maxHPathsProper` bounds the size of every proper H-path family. -/
lemma le_maxHPathsProper {G : SimpleGraph V}
    {H : G.Subgraph} {k : ℕ} (paths : HPathsProperDisjEnds G H k)
    (C : HCoverProper G H) [Fintype C.vertSet] [Fintype C.edgeSet] :
    k ≤ maxHPathsProper G H := by
  have hbdd := hPathsProperSizes_bddAbove C
  exact le_csSup hbdd ⟨paths⟩

set_option linter.unusedFintypeInType false in
/-- The maximum proper H-path family size is at most the loose cost of any
proper H-cover. -/
theorem maxHPathsProper_le_coverProper_loose {G : SimpleGraph V}
    {H : G.Subgraph} (C : HCoverProper G H)
    [Fintype C.vertSet] [Fintype C.edgeSet] :
    maxHPathsProper G H ≤ Fintype.card C.vertSet + Fintype.card C.edgeSet := by
  classical
  obtain ⟨paths⟩ := maxHPathsProper_spec C
  exact mader_proper_paths_le_coverProper_loose paths C

/-! ## Scope of the proper-path results

The results above establish the loose upper bound and define the extremal
quantities, but do not prove the full min-max equality. A converse reduction
must handle A-B paths consisting only of an internal split edge: their
projection has length zero and is not a proper H-path. It also requires a
packing-to-separator theorem for the precise A-B path convention used here. -/

/-- The set of costs of finite proper H-covers. -/
def hCoverProperCosts (G : SimpleGraph V) (H : G.Subgraph) : Set ℕ :=
  { c | ∃ C : HCoverProper G H, ∃ (_ : Fintype C.vertSet) (_ : Fintype C.edgeSet),
        c = Fintype.card C.vertSet + Fintype.card C.edgeSet }

/-- The infimum of the costs `|U| + |F|` of proper H-covers. By the `sInf`
convention, this is `0` when the set of costs is empty. -/
noncomputable def minHCoverProper (G : SimpleGraph V) (H : G.Subgraph) : ℕ :=
  sInf (hCoverProperCosts G H)

set_option linter.unusedFintypeInType false in
/-- The minimum proper-cover cost is at most the cost of any given cover. -/
lemma minHCoverProper_le_cost {G : SimpleGraph V} {H : G.Subgraph}
    (C : HCoverProper G H) [hU : Fintype C.vertSet] [hF : Fintype C.edgeSet] :
    minHCoverProper G H ≤ Fintype.card C.vertSet + Fintype.card C.edgeSet := by
  apply Nat.sInf_le
  refine ⟨C, hU, hF, ?_⟩
  rfl

/-! ### Excluding degenerate A-B paths

The internal edge from `minus h` to `plus h` is itself an A-B path of length
one, but projects to a zero-length walk in `G`. The strengthened structure
below excludes this case by requiring length at least two. Distinct,
nonadjacent terminals guarantee this for paths obtained from Menger's theorem. -/

/-- An `STDisjointPaths` family whose paths all have length at least two. -/
structure IsNontrivialVDPWalk (G : SimpleGraph V) (s t : V) (k : ℕ) where
  /-- A family of `k` walks from `s` to `t`. -/
  walk : Fin k → G.Walk s t
  /-- Every walk is a path. -/
  isPath : ∀ i, (walk i).IsPath
  /-- Distinct paths have disjoint internal vertices. -/
  internal_disjoint : ∀ i j, i ≠ j →
    ∀ v, v ∈ (walk i).support → v ≠ s → v ≠ t →
      v ∉ (walk j).support
  /-- Every path has length at least two. This excludes both nil and a single
  edge, which would project to a zero-length walk in the original graph. -/
  length_ge_two : ∀ i, 2 ≤ (walk i).length

/-- Every path in this structure has positive length. -/
lemma IsNontrivialVDPWalk.length_pos {G : SimpleGraph V} {s t : V} {k : ℕ}
    (dp : G.IsNontrivialVDPWalk s t k) (i : Fin k) : 0 < (dp.walk i).length :=
  Nat.lt_of_lt_of_le (by decide) (dp.length_ge_two i)

/-- Forgetting `length_ge_two` gives the standard `STDisjointPaths` structure. -/
def IsNontrivialVDPWalk.toSTDisjointPaths {G : SimpleGraph V} {s t : V} {k : ℕ}
    (dp : G.IsNontrivialVDPWalk s t k) : G.STDisjointPaths s t k where
  walk := dp.walk
  isPath := dp.isPath
  internal_disjoint := dp.internal_disjoint

/-- A nontrivial path family yields a standard `STDisjointPaths` family. -/
lemma nonempty_STDisjointPaths_of_nontrivial
    {G : SimpleGraph V} {s t : V} {k : ℕ}
    (h : Nonempty (G.IsNontrivialVDPWalk s t k)) :
    Nonempty (G.STDisjointPaths s t k) :=
  h.map IsNontrivialVDPWalk.toSTDisjointPaths

/-- If `s ≠ t`, `s` and `t` are nonadjacent, and every separator avoiding
them has size at least `k`, then there are `k` internally vertex-disjoint
`s`-`t` paths of length at least two. Apply Menger's theorem; length zero
would force `s = t`, and length one would force `G.Adj s t`. -/
theorem menger_st_nontrivial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (k : ℕ)
    (hst : s ≠ t) (hnadj : ¬ G.Adj s t)
    (hsep : ∀ S : Finset V, s ∉ S → t ∉ S →
      G.IsABSeparator {s} {t} S → k ≤ S.card) :
    Nonempty (G.IsNontrivialVDPWalk s t k) := by
  obtain ⟨dp⟩ := menger_st_of_separator_bound G s t k hst hsep
  refine ⟨{
    walk := dp.walk
    isPath := dp.isPath
    internal_disjoint := dp.internal_disjoint
    length_ge_two := ?_ }⟩
  intro i
  by_contra hlt
  push Not at hlt
  -- A natural number below two is either zero or one.
  interval_cases h : (dp.walk i).length
  · exact hst (Walk.eq_of_length_eq_zero h)
  · exact hnadj (Walk.adj_of_length_eq_one h)

/-! ### Projecting split-graph walks back to `G`

The first edge from a minus copy is forced: its only neighbor is the
corresponding plus copy. After removing that edge, a walk with no minus copy
can be projected to `G` by mapping outside and plus copies to their original
vertices. Each remaining split-graph edge projects to an edge of `G`. -/

/-- The only neighbor of a minus copy is the corresponding plus copy. -/
lemma maderSplitGraph_adj_minus_eq_plus {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} {h : V} (hh : h ∈ H.verts) (y : MaderSplit G H)
    (hadj : (MaderSplitGraph G H).Adj
      (MaderSplit.minus (G := G) (H := H) h hh) y) :
    y = MaderSplit.plus (G := G) (H := H) h hh := by
  -- Split according to the constructor of `y`.
  match y, hadj with
  | Sum.inl ⟨_, _⟩, h => exact h.elim
  | Sum.inr (⟨_, _⟩, false), h => exact h.elim
  | Sum.inr (⟨h', hh'⟩, true), heq =>
    -- heq : MaderSplitAdj minus minus_plus = (h = h')
    change h = h' at heq
    subst heq
    rfl

/-- A plus copy is adjacent to a minus copy only when they represent the
same original vertex. -/
lemma maderSplitGraph_adj_plus_minus_eq {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} {h h' : V} (hh : h ∈ H.verts) (hh' : h' ∈ H.verts)
    (hadj : (MaderSplitGraph G H).Adj
      (MaderSplit.plus (G := G) (H := H) h hh)
      (MaderSplit.minus (G := G) (H := H) h' hh')) :
    h = h' := by
  -- This adjacency case is exactly the equality `h = h'`.
  exact hadj

/-- In a path whose endpoints are not minus copies, no minus copy occurs in
the support. An internal minus copy would need two distinct path neighbors,
but its only neighbor is the corresponding plus copy. -/
lemma maderSplit_walk_isPath_no_minus {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} :
    ∀ {a b : MaderSplit G H} (q : (MaderSplitGraph G H).Walk a b),
      q.IsPath →
      (∀ h : V, ∀ hh : h ∈ H.verts, a ≠ MaderSplit.minus (G := G) (H := H) h hh) →
      (∀ h : V, ∀ hh : h ∈ H.verts, b ≠ MaderSplit.minus (G := G) (H := H) h hh) →
      ∀ h' : V, ∀ hh' : h' ∈ H.verts,
        MaderSplit.minus (G := G) (H := H) h' hh' ∉ q.support := by
  intro a b q hpq hane hbne h' hh' hmem
  induction q with
  | nil =>
    -- For a nil walk, its only support vertex is the start vertex.
    simp [Walk.support_nil] at hmem
    exact (hane h' hh') hmem.symm
  | cons hadj q' ih =>
    rename_i a x b'
    -- The support is the start vertex followed by the tail support.
    have hpq' : q'.IsPath := (Walk.cons_isPath_iff _ _).mp hpq |>.1
    have h_a_notin : a ∉ q'.support := (Walk.cons_isPath_iff _ _).mp hpq |>.2
    rw [Walk.support_cons, List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · -- The start vertex is not a minus copy.
      exact (hane h' hh') hmem.symm
    · -- Apply the induction hypothesis to the tail, showing its start is not
      -- a minus copy.
      apply ih hpq' ?hxne hbne hmem
      intro h0 hh0 hxeq
      -- If `x` were a minus copy, its predecessor and successor would both
      -- have to be the same plus copy, contradicting path simplicity or the
      -- endpoint condition.
      have ha_plus : ∃ hh1 : h0 ∈ H.verts,
          a = MaderSplit.plus (G := G) (H := H) h0 hh1 := by
        rw [hxeq] at hadj
        match a, hadj with
        | Sum.inl ⟨_, _⟩, hadj_e => exact hadj_e.elim
        | Sum.inr (⟨_, _⟩, false), hadj_e => exact hadj_e.elim
        | Sum.inr (⟨h1, hh1⟩, true), hadj_e =>
          -- This adjacency case gives `h1 = h0`.
          have heq : h1 = h0 := hadj_e
          subst heq
          exact ⟨hh1, rfl⟩
      obtain ⟨hh0a, ha_eq⟩ := ha_plus
      -- Now `a` is the plus copy and `x` is the corresponding minus copy.
      subst hxeq
      cases q' with
      | nil =>
        -- The endpoint cannot be a minus copy.
        exact (hbne h0 hh0) rfl
      | @cons _ y _ hadj2 q'' =>
        -- The only neighbor after a minus copy is its corresponding plus copy.
        have hyq : y = MaderSplit.plus (G := G) (H := H) h0 hh0 :=
          maderSplitGraph_adj_minus_eq_plus hh0 y hadj2
        -- This repeats the start vertex in the path support, a contradiction.
        rw [ha_eq] at h_a_notin
        apply h_a_notin
        rw [Walk.support_cons, ← hyq]
        simp

/-! ### Projecting a split-graph walk to `G`

A path with plus-copy endpoints and no minus copy in its support projects to
a walk in `G`. The projection preserves length and support, and each edge
projects to an edge of the original graph. -/

/-- Project a copy to its original vertex. The projection lemmas exclude
minus copies from the walks under consideration. -/
def MaderSplit.projectVertex {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (x : MaderSplit G H) : V :=
  match x with
  | Sum.inl ⟨z, _⟩ => z
  | Sum.inr (⟨h, _⟩, _) => h

@[simp] lemma MaderSplit.projectVertex_outside {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} (z : V) (hz : z ∉ H.verts) :
    MaderSplit.projectVertex (G := G) (H := H)
      (MaderSplit.outside (G := G) (H := H) z hz) = z := rfl

@[simp] lemma MaderSplit.projectVertex_plus {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} (h : V) (hh : h ∈ H.verts) :
    MaderSplit.projectVertex (G := G) (H := H)
      (MaderSplit.plus (G := G) (H := H) h hh) = h := rfl

/-- An edge in the split graph projects to an edge in `G` when neither
endpoint is a minus copy. -/
lemma MaderSplit.projectAdj {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    {x y : MaderSplit G H} (hadj : (MaderSplitGraph G H).Adj x y)
    (hx : ∀ h : V, ∀ hh : h ∈ H.verts, x ≠ MaderSplit.minus (G := G) (H := H) h hh)
    (hy : ∀ h : V, ∀ hh : h ∈ H.verts, y ≠ MaderSplit.minus (G := G) (H := H) h hh) :
    G.Adj (MaderSplit.projectVertex x) (MaderSplit.projectVertex y) := by
  match x, y, hadj with
  | Sum.inl ⟨_, _⟩, Sum.inl ⟨_, _⟩, h => exact h
  | Sum.inl ⟨_, _⟩, Sum.inr (⟨_, _⟩, true), h => exact h
  | Sum.inl ⟨z, _⟩, Sum.inr (⟨h', hh'⟩, false), h =>
    -- The endpoint is a minus copy, contrary to `hy`.
    exact absurd rfl (hy h' hh')
  | Sum.inr (⟨h', hh'⟩, false), Sum.inl _, h =>
    -- The endpoint is a minus copy, contrary to `hx`.
    exact absurd rfl (hx h' hh')
  | Sum.inr (⟨_, _⟩, true), Sum.inl ⟨_, _⟩, h => exact h
  | Sum.inr (⟨h', hh'⟩, false), Sum.inr (_, true), _ =>
    exact absurd rfl (hx h' hh')
  | Sum.inr (_, true), Sum.inr (⟨h', hh'⟩, false), _ =>
    exact absurd rfl (hy h' hh')
  | Sum.inr (⟨_, _⟩, true), Sum.inr (⟨_, _⟩, true), h => exact h.1
  | Sum.inr (⟨h', hh'⟩, false), Sum.inr (_, false), _ =>
    exact absurd rfl (hx h' hh')

/-- On outside and plus copies, `projectVertex` is injective: outside
vertices lie outside `H`, while plus-copy vertices lie in `H`. -/
lemma MaderSplit.projectVertex_injOn_no_minus {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} (x y : MaderSplit G H)
    (hx : ∀ h : V, ∀ hh : h ∈ H.verts, x ≠ MaderSplit.minus (G := G) (H := H) h hh)
    (hy : ∀ h : V, ∀ hh : h ∈ H.verts, y ≠ MaderSplit.minus (G := G) (H := H) h hh)
    (heq : MaderSplit.projectVertex x = MaderSplit.projectVertex y) :
    x = y := by
  match x, y with
  | Sum.inl ⟨xz, hxz⟩, Sum.inl ⟨yz, hyz⟩ =>
    -- Projection returns the original vertex for outside copies.
    simp [MaderSplit.projectVertex] at heq
    subst heq
    rfl
  | Sum.inl ⟨xz, hxz⟩, Sum.inr (⟨yh, yhh⟩, true) =>
    -- The projected vertex would be both inside and outside `H`.
    simp [MaderSplit.projectVertex] at heq
    subst heq
    exact absurd yhh hxz
  | Sum.inl ⟨xz, hxz⟩, Sum.inr (⟨yh, yhh⟩, false) =>
    exact absurd rfl (hy yh yhh)
  | Sum.inr (⟨xh, xhh⟩, true), Sum.inl ⟨yz, hyz⟩ =>
    simp [MaderSplit.projectVertex] at heq
    subst heq
    exact absurd xhh hyz
  | Sum.inr (⟨xh, xhh⟩, false), Sum.inl ⟨yz, hyz⟩ =>
    exact absurd rfl (hx xh xhh)
  | Sum.inr (⟨xh, xhh⟩, true), Sum.inr (⟨yh, yhh⟩, true) =>
    simp [MaderSplit.projectVertex] at heq
    subst heq
    rfl
  | Sum.inr (⟨xh, xhh⟩, false), Sum.inr (_, _) =>
    exact absurd rfl (hx xh xhh)
  | Sum.inr (⟨xh, xhh⟩, true), Sum.inr (⟨yh, yhh⟩, false) =>
    exact absurd rfl (hy yh yhh)

/-- Project a path with no minus copies in its support to a walk in `G`,
preserving length, support, pathhood, and edge correspondence. -/
lemma MaderSplit.existsProjectedWalk {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} :
    ∀ {a b : MaderSplit G H} (q : (MaderSplitGraph G H).Walk a b),
      q.IsPath →
      (∀ x ∈ q.support, ∀ h : V, ∀ hh : h ∈ H.verts,
        x ≠ MaderSplit.minus (G := G) (H := H) h hh) →
      ∃ p : G.Walk (MaderSplit.projectVertex a) (MaderSplit.projectVertex b),
        p.length = q.length ∧
        p.support = q.support.map MaderSplit.projectVertex ∧
        p.IsPath ∧
        (∀ e ∈ p.edges,
          ∃ e' ∈ q.edges, e = e'.map (fun x => MaderSplit.projectVertex (G := G) (H := H) x)) := by
  intro a b q hpq hno_minus
  induction q with
  | nil =>
    refine ⟨Walk.nil, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [Walk.support_nil]
    · exact Walk.IsPath.nil
    · intro e he; simp at he
  | cons hadj q' ih =>
    rename_i a x b'
    have hpq' : q'.IsPath := (Walk.cons_isPath_iff _ _).mp hpq |>.1
    have h_a_notin : a ∉ q'.support := (Walk.cons_isPath_iff _ _).mp hpq |>.2
    have hane : ∀ h : V, ∀ hh : h ∈ H.verts,
        a ≠ MaderSplit.minus (G := G) (H := H) h hh := by
      intro h hh
      apply hno_minus a
      simp [Walk.support_cons]
    have hxne : ∀ h : V, ∀ hh : h ∈ H.verts,
        x ≠ MaderSplit.minus (G := G) (H := H) h hh := by
      intro h hh
      apply hno_minus x
      simp [Walk.support_cons, Walk.start_mem_support]
    have hno_minus' : ∀ z ∈ q'.support, ∀ h : V, ∀ hh : h ∈ H.verts,
        z ≠ MaderSplit.minus (G := G) (H := H) h hh := by
      intro z hz h hh
      apply hno_minus z
      simp [Walk.support_cons, hz]
    obtain ⟨p', hlen, hsupp, hpath_p', hedges⟩ := ih hpq' hno_minus'
    have hadjP : G.Adj (MaderSplit.projectVertex a) (MaderSplit.projectVertex x) :=
      MaderSplit.projectAdj hadj hane hxne
    refine ⟨Walk.cons hadjP p', ?_, ?_, ?_, ?_⟩
    · simp [Walk.length_cons, hlen]
    · simp [Walk.support_cons, hsupp]
    · -- Pathhood follows from injectivity of the projection on the support.
      refine Walk.IsPath.cons hpath_p' ?_
      intro hmem
      rw [hsupp, List.mem_map] at hmem
      obtain ⟨z, hz, hzeq⟩ := hmem
      -- Equal projected vertices are equal by injectivity on non-minus copies.
      have hzne : ∀ h : V, ∀ hh : h ∈ H.verts,
          z ≠ MaderSplit.minus (G := G) (H := H) h hh := hno_minus' z hz
      have hza : z = a :=
        MaderSplit.projectVertex_injOn_no_minus z a hzne hane hzeq
      subst hza
      exact h_a_notin hz
    · intro e he
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · refine ⟨s(a, x), ?_, ?_⟩
        · simp [Walk.edges_cons]
        · rw [he]; rfl
      · obtain ⟨e', he', heq⟩ := hedges e he
        refine ⟨e', ?_, heq⟩
        simp [Walk.edges_cons, he']

/-! ### Limitation of the direct projection

The direct projection does not by itself give the converse reduction. A
split-graph path may contain an internal plus copy of a vertex of `H`; its
projection is then not an H-path, because an internal vertex lies in `H`.
A complete min-max proof needs an additional argument to handle such paths,
rather than projecting each path independently. -/
end SimpleGraph
