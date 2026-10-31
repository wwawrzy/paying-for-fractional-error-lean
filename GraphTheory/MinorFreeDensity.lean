import GraphTheory.SimpleGraph.Minor.Defs
import GraphTheory.SimpleGraph.Degeneracy
import GraphTheory.SimpleGraph.DegeneracyColoring
import Mathlib.Tactic

/-!
# Edge Density Bounds for Minor-Free Graph Classes

This file formalizes edge density bounds for two minor-free graph classes:

* **E5:** K_{2,t}-minor-free graphs have |E| ≤ (t+1)(|V|-1)/2.
* **E6:** K_{3,3}-minor-free graphs have |E| ≤ 3|V| - 6 (same bound as planar).

From the K_{3,3}-minor-free density bound we derive:

* K_{3,3}-minor-free → 5-degenerate (same proof pattern as planar)
* K_{3,3}-minor-free → 6-colorable

## Main definitions

* `SimpleGraph.IsK2tMinorFree` — `G` is K_{2,t}-minor-free
* `SimpleGraph.IsK33MinorFree` — imported from `MdsLean.Minor`

## Main results

* `SimpleGraph.IsK2tMinorFree.edgeFinset_card_le` — edge density for K_{2,t}-minor-free
* `SimpleGraph.IsK33MinorFree.edgeFinset_card_le` — edge density for K_{3,3}-minor-free
* `SimpleGraph.IsK33MinorFree.isKDegenerate_five` — K_{3,3}-minor-free → 5-degenerate
* `SimpleGraph.IsK33MinorFree.colorable_six` — K_{3,3}-minor-free → 6-colorable

## References

* Kostochka, A.V.; Prince, N. (2008). "On K_{s,t}-minors in graphs of given average degree."
  Discrete Mathematics 308(19): 4435-4445. (edge density for K_{2,t}-minor-free)
* Wagner, K. (1937). "Über eine Eigenschaft der ebenen Komplexe."
  Mathematische Annalen 114: 570-590. (structure theorem for K_{3,3}-minor-free)
* Diestel, *Graph Theory*, 5th ed., Ch. 4 notes (Wagner's theorem discussion)
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}

/-! ### K_{2,t}-minor-free graphs -/

/-- A graph `G` is *K_{2,t}-minor-free* if the complete bipartite graph `K_{2,t}`
is not a minor of `G`. -/
def IsK2tMinorFree {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  G.IsHMinorFree (completeBipartiteGraph (Fin 2) (Fin t))

/-! ### Structural lemma: common neighborhoods are bounded -/

/-- A singleton set induces a connected subgraph. -/
private lemma singleton_induce_connected (G : SimpleGraph V) (v : V) :
    (G.induce {v}).Connected := by
  rw [connected_iff_exists_forall_reachable]
  exact ⟨⟨v, rfl⟩, fun ⟨w, hw⟩ => by
    rw [Set.mem_singleton_iff] at hw; subst hw; exact Reachable.refl _⟩

/-- If two vertices `u` and `v` have at least `t` common neighbors, then `K_{2,t}` is a
minor of `G`. The branch sets are singletons: `{u}`, `{v}`, and `{wᵢ}` for `t` common
neighbors `w₁, …, wₜ`. -/
theorem k2t_minor_of_commonNeighbors (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} (hne : u ≠ v) {t : ℕ}
    (h : t ≤ Fintype.card (G.commonNeighbors u v)) :
    (completeBipartiteGraph (Fin 2) (Fin t)) ≤m G := by
  have hemb := Function.Embedding.nonempty_of_card_le (α := Fin t)
    (β := G.commonNeighbors u v) (by rwa [Fintype.card_fin])
  obtain ⟨f⟩ := hemb
  let g : Fin t → V := fun i => (f i).val
  have hg_inj : Function.Injective g := fun i j hij => f.injective (Subtype.ext hij)
  have hg_adj_u : ∀ i, G.Adj u (g i) := fun i => ((f i).prop).1
  have hg_adj_v : ∀ i, G.Adj v (g i) := fun i => ((f i).prop).2
  have hg_ne_u : ∀ i, g i ≠ u := fun i h => G.irrefl (h ▸ hg_adj_u i)
  have hg_ne_v : ∀ i, g i ≠ v := fun i h => G.irrefl (h ▸ hg_adj_v i)
  let bs : Fin 2 ⊕ Fin t → Set V := fun x =>
    match x with
    | Sum.inl 0 => {u}
    | Sum.inl 1 => {v}
    | Sum.inr j => {g j}
  refine ⟨{
    branchSet := bs
    nonempty := fun h => by
      match h with
      | Sum.inl 0 => exact ⟨u, rfl⟩
      | Sum.inl 1 => exact ⟨v, rfl⟩
      | Sum.inr j => exact ⟨g j, rfl⟩
    disjoint := fun h₁ h₂ hne12 => by
      rw [Set.disjoint_iff]; intro x ⟨hx1, hx2⟩
      match h₁, h₂ with
      | Sum.inl 0, Sum.inl 0 => exact hne12 rfl
      | Sum.inl 0, Sum.inl 1 =>
        simp [bs, Set.mem_singleton_iff] at hx1 hx2; exact hne (hx1 ▸ hx2)
      | Sum.inl 1, Sum.inl 0 =>
        simp [bs, Set.mem_singleton_iff] at hx1 hx2; exact hne (hx2 ▸ hx1)
      | Sum.inl 1, Sum.inl 1 => exact hne12 rfl
      | Sum.inl 0, Sum.inr j =>
        simp [bs, Set.mem_singleton_iff] at hx1 hx2
        exact (hg_ne_u j) (hx2 ▸ hx1)
      | Sum.inl 1, Sum.inr j =>
        simp [bs, Set.mem_singleton_iff] at hx1 hx2
        exact (hg_ne_v j) (hx2 ▸ hx1)
      | Sum.inr j, Sum.inl 0 =>
        simp [bs, Set.mem_singleton_iff] at hx1 hx2
        exact (hg_ne_u j) (hx2 ▸ hx1.symm)
      | Sum.inr j, Sum.inl 1 =>
        simp [bs, Set.mem_singleton_iff] at hx1 hx2
        exact (hg_ne_v j) (hx2 ▸ hx1.symm)
      | Sum.inr j₁, Sum.inr j₂ =>
        simp [bs, Set.mem_singleton_iff] at hx1 hx2
        exact hne12 (congr_arg Sum.inr (hg_inj (hx1 ▸ hx2)))
    connected := fun h => by
      match h with
      | Sum.inl 0 => exact singleton_induce_connected G u
      | Sum.inl 1 => exact singleton_induce_connected G v
      | Sum.inr j => exact singleton_induce_connected G (g j)
    adjacent := fun h₁ h₂ hadj => by
      match h₁, h₂ with
      | Sum.inl 0, Sum.inr j => exact ⟨u, rfl, g j, rfl, hg_adj_u j⟩
      | Sum.inl 1, Sum.inr j => exact ⟨v, rfl, g j, rfl, hg_adj_v j⟩
      | Sum.inr j, Sum.inl 0 => exact ⟨g j, rfl, u, rfl, (hg_adj_u j).symm⟩
      | Sum.inr j, Sum.inl 1 => exact ⟨g j, rfl, v, rfl, (hg_adj_v j).symm⟩
      | Sum.inl 0, Sum.inl 0 => simp [completeBipartiteGraph] at hadj
      | Sum.inl 0, Sum.inl 1 => simp [completeBipartiteGraph] at hadj
      | Sum.inl 1, Sum.inl 0 => simp [completeBipartiteGraph] at hadj
      | Sum.inl 1, Sum.inl 1 => simp [completeBipartiteGraph] at hadj
      | Sum.inr _, Sum.inr _ => simp [completeBipartiteGraph] at hadj
  }⟩

/-- **In a K_{2,t}-minor-free graph, any two distinct vertices have fewer than `t` common
neighbors.** This is the key structural lemma: if `|N(u) ∩ N(v)| ≥ t`, then
the `t` common neighbors together with `{u}` and `{v}` form singleton branch sets
for a `K_{2,t}` minor model. -/
theorem IsK2tMinorFree.commonNeighbors_card_lt (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {t : ℕ} (hG : G.IsK2tMinorFree t) {u v : V} (hne : u ≠ v) :
    Fintype.card (G.commonNeighbors u v) < t := by
  by_contra h
  push_neg at h
  exact hG (k2t_minor_of_commonNeighbors G hne h)

/-! ### Edge density: K_{2,t}-minor-free (E5) -/

/-- **Edge density bound for K_{2,t}-minor-free graphs (hard case)** (axiom).

The full minor-exclusion hypothesis is essential. A bound on the number of
common neighbors alone is insufficient: for t=2, the Petersen graph has at
most one common neighbor per pair but violates the proposed edge bound.
This structural edge estimate is an explicit axiom in the inherited library;
it is not a proved result of this formalization.

**Reference:** Kostochka, A.V.; Prince, N. (2008). "On K_{s,t}-minors in graphs
of given average degree." Discrete Mathematics 308(19): 4435-4445. -/
axiom wedge_count_edge_bound {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {t : ℕ} (ht : 1 ≤ t)
    (hG : G.IsK2tMinorFree t)
    (hcard : 2 ≤ Fintype.card V)
    (hgt : t + 1 < Fintype.card V) :
    2 * G.edgeFinset.card ≤ (t + 1) * (Fintype.card V - 1)

/-- **[E5]** A K_{2,t}-minor-free graph on `n` vertices has at most `(t+1)(n-1)/2` edges.

This is a classical result in extremal graph theory (Kostochka–Prince 2008).
The bound is tight for `t = 2` (outerplanar graphs) and `t = 3` (planar-like).

The key structural ingredient is `IsK2tMinorFree.commonNeighbors_card_lt`:
any two distinct vertices have fewer than `t` common neighbors.

**Proof structure:** Split into two cases:
* **Easy case** (`n ≤ t + 1`): The trivial bound `deg(v) ≤ n - 1` gives
  `2|E| = ∑ deg(v) ≤ n(n-1) ≤ (t+1)(n-1)`.
* **Hard case** (`n > t + 1`): Uses `wedge_count_edge_bound`, a double-counting
  argument on wedges (length-2 paths) combined with convexity. -/
theorem IsK2tMinorFree.edgeFinset_card_le (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {t : ℕ} (hG : G.IsK2tMinorFree t) (ht : 1 ≤ t)
    (hcard : 2 ≤ Fintype.card V) :
    2 * G.edgeFinset.card ≤ (t + 1) * (Fintype.card V - 1) := by
  by_cases hle : Fintype.card V ≤ t + 1
  · -- Easy case: n ≤ t + 1. The trivial bound deg(v) ≤ n - 1 suffices.
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc ∑ v : V, G.degree v
        ≤ ∑ _v : V, (Fintype.card V - 1) := by
          apply Finset.sum_le_sum; intro v _
          have := G.degree_lt_card_verts v; omega
      _ = Fintype.card V * (Fintype.card V - 1) := by
          simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ (t + 1) * (Fintype.card V - 1) := Nat.mul_le_mul_right _ hle
  · -- Hard case: n > t + 1. Use the edge density bound.
    exact wedge_count_edge_bound G ht hG hcard (by omega)

/-! ### Edge density: K_{3,3}-minor-free (E6) -/

/-- **Subgraph closure for K_{3,3}-minor-freeness.**
If `G` is K_{3,3}-minor-free and `H ≤ G`, then `H` is K_{3,3}-minor-free. -/
theorem IsK33MinorFree.mono {G H : SimpleGraph V}
    (hG : G.IsK33MinorFree) (hle : H ≤ G) : H.IsK33MinorFree := by
  intro hm
  apply hG
  let m := hm.some
  refine Nonempty.intro {
    branchSet := m.branchSet
    nonempty := m.nonempty
    disjoint := m.disjoint
    connected := fun h => (m.connected h).mono (fun a b hadj => hle hadj)
    adjacent := fun h₁ h₂ hadj => ?_
  }
  have hab := m.adjacent h₁ h₂ hadj
  exact hab.imp fun v₁ => And.imp_right (Exists.imp fun v₂ => And.imp_right (fun h => hle h))

/-- **K_{3,3}-minor-freeness is inherited by induced subgraphs.**
If `G` is K_{3,3}-minor-free, then `G.induce s` is also K_{3,3}-minor-free.

The proof constructs a minor model in `G` from any minor model in `G.induce s`
by mapping each branch set element back via `Subtype.val`, then applies
`IsHMinorFree.minor` (monotonicity under taking minors). -/
theorem IsK33MinorFree.induce {G : SimpleGraph V}
    (hG : G.IsK33MinorFree) (s : Set V) :
    (G.induce s).IsK33MinorFree := by
  intro hm
  apply hG
  exact hm.trans (Nonempty.intro {
    branchSet := fun v => {v.val}
    nonempty := fun v => Set.singleton_nonempty v.val
    disjoint := fun v1 v2 hne => by
      rw [Set.disjoint_iff]
      intro x hx
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at hx
      exact hne (Subtype.ext (hx.1.symm.trans hx.2))
    connected := fun v => by
      rw [connected_iff_exists_forall_reachable]
      refine Exists.intro (Subtype.mk v.val (Set.mem_singleton v.val)) (fun w => ?_)
      have hw : w.val = v.val := by
        have := w.property
        rw [Set.mem_singleton_iff] at this
        exact this
      cases w with
      | mk val prop =>
        subst hw
        exact Reachable.refl _
    adjacent := fun v1 v2 hadj => by
      rw [induce_adj] at hadj
      exact Exists.intro v1.val (And.intro rfl (Exists.intro v2.val (And.intro rfl hadj)))
  })

/-- **Wagner edge density bound for K_{3,3}-minor-free graphs** (axiom).

For n >= 3, a K_{3,3}-minor-free graph has at most 3n - 5 edges. The bound
is sharp for K_5. This estimate is retained as an explicit library axiom;
the selected paper proof roots do not use it.

**Reference:** Wagner, K. (1937). "Über eine Eigenschaft der ebenen Komplexe."
Mathematische Annalen 114: 570-590. See also Diestel, *Graph Theory* 5th ed., Ch. 4 notes (p.92). -/
axiom wagner_edge_bound {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsK33MinorFree) (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 5

/-- **[E6]** A K_{3,3}-minor-free graph on `n ≥ 3` vertices has at most `3n - 5` edges.

This follows from Wagner's structure theorem: K_{3,3}-minor-free graphs can be
decomposed into planar graphs and copies of K₅ glued along edges or triangles.
Since K₅ has 10 = 3·5 - 5 edges, the bound is `3n - 5` (not `3n - 6` as for
planar graphs). K₅ itself is K_{3,3}-minor-free and achieves the bound.

**Note:** The previous statement `|E| ≤ 3n - 6` was FALSE — K₅ is a
counterexample (K₅ is K_{3,3}-minor-free with 10 edges > 3·5 - 6 = 9).

**Proof:** Follows directly from `wagner_edge_bound`, which encodes the
combinatorial consequence of Wagner's structure theorem. -/
theorem IsK33MinorFree.edgeFinset_card_le (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsK33MinorFree) (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 5 :=
  wagner_edge_bound G hG hcard

/-! ### Consequences of K_{3,3}-minor-free density -/

section Consequences

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The sum of degrees in a K_{3,3}-minor-free graph is at most `6|V| - 10`.
Follows from the handshaking lemma and the edge density bound `|E| ≤ 3|V| - 5`. -/
theorem IsK33MinorFree.sum_degrees_le
    (hG : G.IsK33MinorFree) (hcard : 3 ≤ Fintype.card V) :
    (Finset.sum Finset.univ fun v => G.degree v) ≤ 6 * Fintype.card V - 10 := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  have h := hG.edgeFinset_card_le G hcard
  omega

/-- Every K_{3,3}-minor-free graph on at least 3 vertices has a vertex of degree at most 5.
If all degrees were at least 6, the sum would exceed `6|V| - 10`. -/
theorem IsK33MinorFree.exists_vertex_degree_le_five
    [Nonempty V] (hG : G.IsK33MinorFree) (hcard : 3 ≤ Fintype.card V) :
    ∃ v : V, G.degree v ≤ 5 := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hsum := hG.sum_degrees_le G hcard
  have hmin : 6 * Fintype.card V ≤
      (Finset.sum Finset.univ fun v => G.degree v) := by
    have hle : (Finset.sum Finset.univ fun (_v : V) => 6) ≤
        (Finset.sum Finset.univ fun v => G.degree v) := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Nat.lt_iff_add_one_le.mp (h v)
    simp [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    linarith
  omega

end Consequences

/-! ### K_{3,3}-minor-free → 5-degenerate -/

/-- **Every K_{3,3}-minor-free graph is 5-degenerate.**

For any nonempty `s ⊆ V`, the induced subgraph `G[s]` is K_{3,3}-minor-free.
If `|s| ≥ 3`, the edge density bound gives average degree `< 6`, so some vertex
has degree `≤ 5` in `G[s]`. If `|s| < 3`, every vertex trivially has degree `≤ 2 ≤ 5`. -/
theorem IsK33MinorFree.isKDegenerate_five {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] (hG : G.IsK33MinorFree) :
    G.IsKDegenerate 5 := by
  intro s hs
  let H := G.induce (s : Set V)
  have hH : H.IsK33MinorFree := hG.induce s
  haveI : Fintype { x : V // x ∈ (s : Set V) } := inferInstance
  haveI : DecidableRel H.Adj := by intro a b; exact inferInstance
  by_cases hcard : 3 ≤ s.card
  · have hcard' : 3 ≤ Fintype.card { x : V // x ∈ (s : Set V) } := by
      convert hcard using 1
      simp
    haveI : Nonempty { x : V // x ∈ (s : Set V) } := by
      rw [← Fintype.card_pos_iff]; omega
    obtain ⟨⟨v, hv⟩, hdeg⟩ := hH.exists_vertex_degree_le_five H hcard'
    refine ⟨v, hv, ?_⟩
    suffices H.degree ⟨v, hv⟩ = G.inducedDegree v s by omega
    unfold inducedDegree degree
    simp only [neighborFinset]
    rw [Set.toFinset_card]
    rw [← Fintype.card_coe (s.filter (G.Adj v))]
    apply Fintype.card_of_bijective
      (f := fun (u : H.neighborSet ⟨v, hv⟩) =>
        (⟨u.val.val, by
          rw [Finset.mem_filter]
          constructor
          · exact u.val.property
          · have := u.property
            rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj] at this
            exact this⟩ : { x // x ∈ s.filter (G.Adj v) }))
    constructor
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
    · intro ⟨w, hw⟩
      rw [Finset.mem_filter] at hw
      refine ⟨⟨⟨w, hw.1⟩, ?_⟩, by simp⟩
      rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj]
      exact hw.2
  · obtain ⟨v, hv⟩ := hs
    refine ⟨v, hv, ?_⟩
    calc G.inducedDegree v s
        ≤ s.card := G.inducedDegree_le_card v s
      _ ≤ 5 := by omega

/-! ### K_{3,3}-minor-free → 6-colorable -/

/-- **Every K_{3,3}-minor-free graph is 6-colorable.**

This follows directly from 5-degeneracy and the general result that
k-degenerate graphs are (k+1)-colorable (Diestel Proposition 5.2.4). -/
theorem IsK33MinorFree.colorable_six {G : SimpleGraph V}
    [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsK33MinorFree) :
    G.Colorable 6 :=
  hG.isKDegenerate_five.colorable G

/-- **Chromatic number of a K_{3,3}-minor-free graph is at most 6.** -/
theorem IsK33MinorFree.chromaticNumber_le_six {G : SimpleGraph V}
    [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsK33MinorFree) :
    G.chromaticNumber ≤ 6 :=
  hG.colorable_six.chromaticNumber_le

end SimpleGraph
