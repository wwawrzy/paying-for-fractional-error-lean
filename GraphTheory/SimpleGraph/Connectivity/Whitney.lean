/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

/-!
# Vertex/Edge Connectivity and Whitney's Inequality (Diestel Ch 3)

We formalize the basic notions of vertex and edge connectivity for simple graphs,
and state Whitney's inequality: kappa(G) <= lambda(G) <= delta(G)
(Diestel Proposition 3.3.1).

Mathlib currently has no upstream `IsKConnected`, `vertexConnectivity`, or
`edgeConnectivity` for `SimpleGraph` (only `IsEdgeConnected` from
`Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity`).
This file fills that gap and is intended for upstream promotion.

## Main definitions

* `SimpleGraph.IsVertexConnected` -- a graph is k-vertex-connected if it has more
  than k vertices and removing any fewer than k vertices leaves it connected.
* `SimpleGraph.vertexConnectivity` -- kappa(G), the maximum k such that G is
  k-vertex-connected.
* `SimpleGraph.edgeConnectivity` -- lambda(G), the maximum k such that G is
  k-edge-connected.

## Main results

* `SimpleGraph.whitney_kappa_le_lambda` -- kappa(G) <= lambda(G).
* `SimpleGraph.whitney_lambda_le_delta` -- lambda(G) <= delta(G).
* `SimpleGraph.whitney_inequality` -- the combined Whitney inequality.

## References

* Diestel, *Graph Theory*, 5th ed., Proposition 3.3.1 (Whitney's inequality).
-/

set_option linter.style.whitespace false

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Vertex connectivity -/

/-- A graph `G` is **k-vertex-connected** if it has more than `k` vertices and
for every set `S` of fewer than `k` vertices, `G - S` is connected.

This follows Diestel's Definition 3.3: a graph is k-connected if `|V| > k` and
`G - S` is connected for every set S of vertices with `|S| < k`. -/
def IsVertexConnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : Nat) : Prop :=
  And (k < Fintype.card V)
    (forall (S : Finset V), S.card < k ->
      (G.induce ((Finset.univ \ S : Finset V) : Set V)).Connected)

/-- **Diestel §1.4 (U1.4.2).** Every nonempty graph is 0-vertex-connected. The deletion
condition is vacuous; nonemptiness is exactly the remaining cardinality condition. -/
theorem IsVertexConnected.zero (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] : G.IsVertexConnected 0 := by
  refine ⟨Fintype.card_pos, ?_⟩
  intro S hS
  omega

/-- **Diestel §1.4 (U1.4.3).** A graph is 1-vertex-connected if and only if it is
nontrivial and connected. -/
theorem isVertexConnected_one_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.IsVertexConnected 1 ↔ Nontrivial V ∧ G.Connected := by
  constructor
  · rintro ⟨hcard, hdelete⟩
    have hnontrivial : Nontrivial V :=
      Fintype.one_lt_card_iff_nontrivial.mp hcard
    have hinduced := hdelete ∅ (by simp)
    have hunivset : ((Finset.univ \ ∅ : Finset V) : Set V) = Set.univ := by
      ext
      simp
    rw [hunivset] at hinduced
    exact ⟨hnontrivial, G.induceUnivIso.connected_iff.mp hinduced⟩
  · rintro ⟨hnontrivial, hconn⟩
    refine ⟨Fintype.one_lt_card_iff_nontrivial.mpr hnontrivial, ?_⟩
    intro S hS
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    have huniv : (G.induce Set.univ).Connected :=
      G.induceUnivIso.connected_iff.mpr hconn
    have hunivset : ((Finset.univ \ ∅ : Finset V) : Set V) = Set.univ := by
      ext
      simp
    rw [hunivset]
    exact huniv

/-! ## Vertex connectivity number -/

/-- **Vertex connectivity** kappa(G): the largest `k` such that `G` is
k-vertex-connected. For a complete graph K_n, kappa(K_n) = n - 1
by convention.

Defined as `sSup {k | G.IsVertexConnected k}`. -/
noncomputable def vertexConnectivity (G : SimpleGraph V)
    [DecidableRel G.Adj] : Nat :=
  sSup {k : Nat | G.IsVertexConnected k}

private lemma bddAbove_isVertexConnected (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    BddAbove {k : Nat | G.IsVertexConnected k} := by
  use Fintype.card V
  intro k ⟨hk, _⟩
  omega

/-- kappa(G) is the largest k for which G is k-vertex-connected. -/
theorem vertexConnectivity_spec
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] :
    G.IsVertexConnected G.vertexConnectivity := by
  have hne : Set.Nonempty {k : Nat | G.IsVertexConnected k} :=
    ⟨0, Fintype.card_pos, fun S hS => by omega⟩
  exact Nat.sSup_mem hne (bddAbove_isVertexConnected G)

/-- If G is k-vertex-connected, then k <= kappa(G). -/
theorem le_vertexConnectivity_of_isVertexConnected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nontrivial V] {k : Nat}
    (h : G.IsVertexConnected k) :
    k <= G.vertexConnectivity := by
  exact le_csSup (bddAbove_isVertexConnected G) h

private theorem vertexConnectivity_eq_zero_of_subsingleton
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] [Subsingleton V] :
    G.vertexConnectivity = 0 := by
  unfold vertexConnectivity
  apply Nat.eq_zero_of_le_zero
  apply csSup_le
  · exact ⟨0, IsVertexConnected.zero G⟩
  · intro k hk
    have hcard : Fintype.card V ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    have hkcard : k < Fintype.card V := hk.1
    omega

private theorem vertexConnectivity_eq_zero_of_not_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hconn : ¬ G.Connected) :
    G.vertexConnectivity = 0 := by
  cases subsingleton_or_nontrivial V with
  | inl hsub =>
      letI : Subsingleton V := hsub
      exact vertexConnectivity_eq_zero_of_subsingleton G
  | inr hnt =>
      letI : Nontrivial V := hnt
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have hspec := G.vertexConnectivity_spec
      have hempty : (∅ : Finset V).card < G.vertexConnectivity := by
        simpa using hpos
      have hinduced := hspec.2 ∅ hempty
      have hunivset : ((Finset.univ \ ∅ : Finset V) : Set V) = Set.univ := by
        ext
        simp
      rw [hunivset] at hinduced
      exact hconn (G.induceUnivIso.connected_iff.mp hinduced)

/-- **Diestel §1.4 (U1.4.4).** For a nonempty finite graph, vertex connectivity is zero
exactly when the graph is disconnected or its vertex type is a singleton. -/
theorem vertexConnectivity_eq_zero_iff_not_connected_or_subsingleton
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    G.vertexConnectivity = 0 ↔ ¬ G.Connected ∨ Subsingleton V := by
  constructor
  · intro hk
    by_cases hsub : Subsingleton V
    · exact Or.inr hsub
    · left
      letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      intro hconn
      have hvc : G.IsVertexConnected 1 :=
        (G.isVertexConnected_one_iff).mpr ⟨inferInstance, hconn⟩
      have hle : 1 ≤ G.vertexConnectivity :=
        G.le_vertexConnectivity_of_isVertexConnected hvc
      omega
  · rintro (hconn | hsub)
    · exact vertexConnectivity_eq_zero_of_not_connected G hconn
    · letI : Subsingleton V := hsub
      exact vertexConnectivity_eq_zero_of_subsingleton G

/-- **Diestel §1.4 (U1.4.5).** The complete graph on a nonempty finite vertex type has
vertex connectivity `|V| - 1`. -/
theorem vertexConnectivity_completeGraph [Nonempty V] :
    (⊤ : SimpleGraph V).vertexConnectivity = Fintype.card V - 1 := by
  cases subsingleton_or_nontrivial V with
  | inl hsub =>
      letI : Subsingleton V := hsub
      rw [vertexConnectivity_eq_zero_of_subsingleton]
      have hcard : Fintype.card V = 1 := by
        exact Fintype.card_eq_one_iff.mpr
          ⟨Classical.arbitrary V, fun y => Subsingleton.elim _ _⟩
      simp [hcard]
  | inr hnt =>
      letI : Nontrivial V := hnt
      apply le_antisymm
      · have hspec := (⊤ : SimpleGraph V).vertexConnectivity_spec
        have hlt : (⊤ : SimpleGraph V).vertexConnectivity < Fintype.card V :=
          hspec.1
        have hcard : 1 < Fintype.card V :=
          Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
        omega
      · apply (⊤ : SimpleGraph V).le_vertexConnectivity_of_isVertexConnected
        refine ⟨by
          have hcard : 1 < Fintype.card V :=
            Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
          omega, ?_⟩
        intro S hS
        have hSlt : S.card < Fintype.card V := by omega
        obtain ⟨v, -, hv⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card
            (show S.card < Finset.univ.card by simpa using hSlt)
        letI : Nonempty {x : V // x ∈ (↑(Finset.univ \ S) : Set V)} :=
          ⟨⟨v, by simp [hv]⟩⟩
        rw [induce_top]
        exact connected_top

/-! ## Edge connectivity number -/

/-- **Edge connectivity** lambda(G): the largest `k` such that `G` is
k-edge-connected (in the sense of `SimpleGraph.IsEdgeConnected`).

Defined as `sSup {k | G.IsEdgeConnected k}`. -/
noncomputable def edgeConnectivity (G : SimpleGraph V)
    [DecidableRel G.Adj] : Nat :=
  sSup {k : Nat | G.IsEdgeConnected k}

private lemma bddAbove_isEdgeConnected (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V] :
    BddAbove {k : Nat | G.IsEdgeConnected k} := by
  obtain ⟨v, _, _⟩ := Nontrivial.exists_pair_ne (α := V)
  exact ⟨G.degree v, fun k hk => hk.le_degree⟩

/-- lambda(G) is the largest k for which G is k-edge-connected. -/
theorem edgeConnectivity_spec
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsEdgeConnected G.edgeConnectivity := by
  unfold edgeConnectivity
  by_cases hnt : Nontrivial V
  · exact Nat.sSup_mem ⟨0, IsEdgeConnected.zero⟩ (bddAbove_isEdgeConnected G)
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact IsEdgeConnected.of_subsingleton

/-- If G is k-edge-connected, then k <= lambda(G). -/
theorem le_edgeConnectivity_of_isEdgeConnected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nontrivial V] {k : Nat} (h : G.IsEdgeConnected k) :
    k <= G.edgeConnectivity := by
  exact le_csSup (bddAbove_isEdgeConnected G) h

/-- **Diestel §1.4 (U1.4.6).** A nonempty disconnected graph has edge connectivity zero. -/
theorem edgeConnectivity_eq_zero_of_not_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hconn : ¬ G.Connected) :
    G.edgeConnectivity = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact hconn ((G.edgeConnectivity_spec).connected (Nat.ne_of_gt hpos))

/-! ## Helper: deleting one edge preserves vertex connectivity -/

/-- If G is (n+1)-vertex-connected, then deleting any single edge leaves
G at least n-vertex-connected. -/
theorem isVertexConnected_deleteEdges_singleton
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : Nat} (hvc : G.IsVertexConnected (n + 1)) (e : Sym2 V) :
    (G.deleteEdges {e}).IsVertexConnected n := by
  obtain ⟨hcard, hconn⟩ := hvc
  refine ⟨by omega, fun S hSn => ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
    -- Case split: does the edge {a,b} have an endpoint in S?
    by_cases haS : a ∈ S
    · -- a ∈ S: edge {a,b} can't appear in induce (V \ S) since a ∉ V \ S
      convert hconn S (by omega) using 1
      ext ⟨x, hx⟩ ⟨y, hy⟩
      simp only [induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
      constructor
      · exact fun ⟨hadj, _⟩ => hadj
      · intro hadj
        simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx hy
        refine ⟨hadj, fun heq => ?_⟩
        rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨_, rfl⟩
        · exact hx haS
        · exact hy haS
    · by_cases hbS : b ∈ S
      · -- b ∈ S: symmetric
        convert hconn S (by omega) using 1
        ext ⟨x, hx⟩ ⟨y, hy⟩
        simp only [induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
        constructor
        · exact fun ⟨hadj, _⟩ => hadj
        · intro hadj
          simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx hy
          refine ⟨hadj, fun heq => ?_⟩
          rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨rfl, _⟩
          · exact hy hbS
          · exact hx hbS
      · -- Hard case: neither a nor b is in S.
        -- G[V\(S∪{a})] and G[V\(S∪{b})] are both connected
        have hSa : (insert a S).card < n + 1 := by
          rw [Finset.card_insert_of_notMem haS]; omega
        have hSb : (insert b S).card < n + 1 := by
          rw [Finset.card_insert_of_notMem hbS]; omega
        have hca := hconn (insert a S) hSa
        have hcb := hconn (insert b S) hSb
        by_cases hab : a = b
        · -- a = b: deleting self-loop s(a,a) is no-op
          rw [hab]
          have hno : G.deleteEdges {s(b, b)} = G := by
            ext x y; simp [deleteEdges_adj]
          rw [hno]
          exact hconn S (by omega)
        · -- a ≠ b: use union of two connected induced subgraphs
          -- V\S = V\(S∪{a}) ∪ V\(S∪{b}) when a ≠ b
          have hset : (↑(Finset.univ \ S) : Set V) =
              (↑(Finset.univ \ insert a S) : Set V) ∪
              (↑(Finset.univ \ insert b S) : Set V) := by
            ext x; simp only [Finset.coe_sdiff, Finset.coe_univ, Finset.coe_insert,
              Set.mem_diff, Set.mem_univ, true_and, Set.mem_union, Set.mem_insert_iff, not_or]
            constructor
            · intro hx
              by_cases hxa : x = a
              · right; exact ⟨fun hxb => hab (hxa ▸ hxb), hx⟩
              · left; exact ⟨hxa, hx⟩
            · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
          -- The intersection is V\(S∪{a,b}), which is nonempty
          have hinter : (↑(Finset.univ \ insert a S) : Set V) ∩
              (↑(Finset.univ \ insert b S) : Set V) |>.Nonempty := by
            -- V\(S∪{a}) ∩ V\(S∪{b}) = V\(S∪{a,b}), nonempty since
            -- |S∪{a,b}| ≤ |S|+2 ≤ n+1 < |V|
            have hSab_card : (insert b (insert a S)).card ≤ S.card + 2 := by
              calc (insert b (insert a S)).card
                  ≤ (insert a S).card + 1 := Finset.card_insert_le b _
                _ ≤ (S.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le a S) 1
                _ = S.card + 2 := by omega
            have hSab_lt : (insert b (insert a S)).card < Fintype.card V := by omega
            have ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
              (show (insert b (insert a S)).card < Finset.univ.card from by
                rwa [Finset.card_univ])
            simp only [Finset.mem_insert] at hc
            push_neg at hc
            obtain ⟨hcb, hca, hcS⟩ := hc
            exact ⟨c, by
              simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_sdiff,
                Finset.mem_univ, true_and, Finset.mem_insert]
              exact ⟨fun h => h.elim (fun h => hca h) (fun h => hcS h),
                     fun h => h.elim (fun h => hcb h) (fun h => hcS h)⟩⟩
          -- Show each half is connected in G' = G.deleteEdges {s(a,b)}
          -- On V\(S∪{a}): a ∉ this set, so edge {a,b} is irrelevant
          have heq1 : (G.deleteEdges {s(a, b)}).induce
              (↑(Finset.univ \ insert a S) : Set V) =
              G.induce (↑(Finset.univ \ insert a S) : Set V) := by
            ext ⟨x, hx⟩ ⟨y, hy⟩
            simp only [induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
            constructor
            · exact fun ⟨hadj, _⟩ => hadj
            · intro hadj
              simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
                Finset.mem_insert] at hx hy
              refine ⟨hadj, fun heq => ?_⟩
              rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hx (Or.inl rfl)
              · exact hy (Or.inl rfl)
          have heq2 : (G.deleteEdges {s(a, b)}).induce
              (↑(Finset.univ \ insert b S) : Set V) =
              G.induce (↑(Finset.univ \ insert b S) : Set V) := by
            ext ⟨x, hx⟩ ⟨y, hy⟩
            simp only [induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
            constructor
            · exact fun ⟨hadj, _⟩ => hadj
            · intro hadj
              simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
                Finset.mem_insert] at hx hy
              refine ⟨hadj, fun heq => ?_⟩
              rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hy (Or.inl rfl)   -- y = b, b ∈ insert b S
              · exact hx (Or.inl rfl)   -- x = b, b ∈ insert b S
          -- Apply induce_union_connected
          rw [hset]
          apply induce_union_connected
          · rw [heq1]; exact hca.preconnected
          · rw [heq2]; exact hcb.preconnected
          · exact hinter

/-- Vertex-connected implies edge-connected: the core of Whitney's first
inequality. -/
private theorem isVertexConnected_imp_isEdgeConnected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : Nat} (hvc : G.IsVertexConnected k) :
    G.IsEdgeConnected k := by
  match k with
  | 0 => exact IsEdgeConnected.zero
  | 1 =>
    rw [isEdgeConnected_one]
    intro u v
    have hconn := hvc.2 ∅ (by simp)
    have huniv : ((Finset.univ \ ∅ : Finset V) : Set V) = Set.univ := by simp
    rw [huniv] at hconn
    exact G.induceUnivIso.connected_iff.mp hconn |>.preconnected u v
  | k + 2 =>
    rw [isEdgeConnected_add_one (by omega)]
    intro e
    have hdel := isVertexConnected_deleteEdges_singleton G hvc e
    exact isVertexConnected_imp_isEdgeConnected (G.deleteEdges {e}) hdel

/-! ## Whitney's inequality -/

/-- **Whitney's inequality, first part** (Diestel Prop 3.3.1):
vertex connectivity is at most edge connectivity.

Proof: If G is k-vertex-connected, by Menger's theorem (set version)
for any two vertices s,t every {s}-{t} separator has size ≥ k.
In particular, removing any < k edges cannot disconnect the graph
(each edge removal can be "covered" by at most one vertex).
Hence G is also k-edge-connected, giving κ(G) ≤ λ(G). -/
-- WAS: axiom whitney_kappa_le_lambda (removed to prove from Menger)
theorem whitney_kappa_le_lambda
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] :
    G.vertexConnectivity <= G.edgeConnectivity := by
  exact le_edgeConnectivity_of_isEdgeConnected G
    (isVertexConnected_imp_isEdgeConnected G (vertexConnectivity_spec G))

/-- **Whitney's inequality, second part** (Diestel Prop 3.3.1):
edge connectivity is at most minimum degree.

Proof: the edges incident to a minimum-degree vertex form an edge cut
of size delta(G), so lambda(G) <= delta(G). Mathlib provides
`IsEdgeConnected.le_degree` which gives `k <= G.degree v` for any `v`
when `G` is k-edge-connected. -/
theorem whitney_lambda_le_delta
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] :
    G.edgeConnectivity <= G.minDegree := by
  have hec := edgeConnectivity_spec G
  apply le_minDegree_of_forall_le_degree
  intro v
  exact hec.le_degree

/-- **Whitney's inequality** (Diestel Prop 3.3.1):
kappa(G) <= lambda(G) <= delta(G). -/
theorem whitney_inequality (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V] :
    And (G.vertexConnectivity <= G.edgeConnectivity)
      (G.edgeConnectivity <= G.minDegree) :=
  And.intro (whitney_kappa_le_lambda G) (whitney_lambda_le_delta G)

/-- Vertex connectivity is at most minimum degree.
An immediate corollary of Whitney's inequality. -/
theorem vertexConnectivity_le_minDegree (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V] :
    G.vertexConnectivity <= G.minDegree :=
  le_trans (whitney_kappa_le_lambda G) (whitney_lambda_le_delta G)

/-! ## k-connected graph predicate (convenience) -/

/-- A graph is **k-connected** if its vertex connectivity is at
least `k`. This is the standard usage in Diestel Chapter 3. -/
def IsKConnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : Nat) : Prop :=
  k <= G.vertexConnectivity

/-- A k-connected graph is also k-vertex-connected. -/
theorem IsKConnected.isVertexConnected (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V] {k : Nat}
    (h : G.IsKConnected k) :
    G.IsVertexConnected k := by
  have hvc := vertexConnectivity_spec G
  unfold IsKConnected at h
  exact And.intro (by linarith [hvc.1]) (fun S hS => hvc.2 S (by linarith))

/-- A k-connected graph is also k-edge-connected. -/
theorem IsKConnected.isEdgeConnected (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V] {k : Nat}
    (h : G.IsKConnected k) :
    G.IsEdgeConnected k := by
  have hec := edgeConnectivity_spec G
  have hkl : k <= G.edgeConnectivity :=
    le_trans h (whitney_kappa_le_lambda G)
  intro u v
  exact (hec u v).anti hkl

/-- A 2-connected graph has no cut vertices: removing any single
vertex leaves it connected. -/
theorem IsKConnected.no_cut_vertex (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V]
    (h : G.IsKConnected 2) (v : V) :
    (G.induce ((Finset.univ \ {v} : Finset V) : Set V)).Connected := by
  have hvc := h.isVertexConnected
  exact hvc.2 {v} (by simp)

/-- A 3-connected graph remains connected after removing any two
vertices. -/
theorem IsKConnected.remove_two (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V]
    (h : G.IsKConnected 3) (u v : V) (huv : Ne u v) :
    (G.induce ((Finset.univ \ {u, v} : Finset V) : Set V)).Connected := by
  have hvc := h.isVertexConnected
  exact hvc.2 {u, v} (by simp [Finset.card_pair huv])

/-! ## Transfer of `IsKConnected` along graph isomorphisms 

These lemmas allow transferring vertex/k-connectivity through a
`SimpleGraph.Iso`. They are used in `MdsLean/Wheel.lean` to bridge
`IsKConnected 3` between `contrInPlace` and `contrGraph` (Phase TW.D.B). -/

section IsoTransfer

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **TW.D.B.1, helper**: `induce` transfers along a graph isomorphism.

Given `e : G ≃g H` and `s : Set V`, restricting `G` to `s` is isomorphic
(via the same vertex bijection, on the image) to restricting `H` to
`e '' s`. The vertex part is `Equiv.Set.image e s e.injective`, and
adjacency is preserved by `e.map_rel_iff`. -/
noncomputable def Iso.induceImage {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (s : Set V) :
    G.induce s ≃g H.induce ((e : V → W) '' s) where
  toEquiv := Equiv.Set.image e s e.injective
  map_rel_iff' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [induce_adj, induce_adj]
    change H.Adj (e x) (e y) ↔ G.Adj x y
    exact e.map_rel_iff

/-- Image of `Finset.univ \ S` under an iso `e` equals `Finset.univ \ S.image e`. -/
private lemma image_compl_finset {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (S : Finset V) :
    (e : V → W) '' ((Finset.univ \ S : Finset V) : Set V)
      = ((Finset.univ \ S.image e.toEquiv : Finset W) : Set W) := by
  classical
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
      true_and, Finset.coe_image, Set.mem_image] at hv ⊢
    rintro ⟨v', hv', heq⟩
    have : v' = v := e.toEquiv.injective heq
    subst this
    exact hv hv'
  · intro hw
    simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
      true_and, Finset.coe_image, Set.mem_image] at hw
    refine ⟨e.symm w, ?_, e.toEquiv.apply_symm_apply w⟩
    simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
      true_and]
    intro hmem
    apply hw
    exact ⟨e.symm w, hmem, e.toEquiv.apply_symm_apply w⟩

/-- One direction of the `IsVertexConnected` transfer: from `G` to `H`. -/
private lemma isVertexConnected_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) {k : Nat} (hG : G.IsVertexConnected k) :
    H.IsVertexConnected k := by
  refine ⟨?_, ?_⟩
  · -- Card transfer.
    rw [← Iso.card_eq e]; exact hG.1
  · intro S hS
    -- Pull S back along `e` to a Finset in V.
    let S' : Finset V := S.image e.symm.toEquiv
    have hS'card : S'.card = S.card :=
      Finset.card_image_of_injective S e.symm.toEquiv.injective
    have hG_S' := hG.2 S' (by rw [hS'card]; exact hS)
    -- S = S'.image e, since S' = S.image e.symm and e ∘ e.symm = id.
    have hS_eq : S'.image e.toEquiv = S := by
      ext w
      simp only [S', Finset.mem_image]
      constructor
      · rintro ⟨w', ⟨v, hv, rfl⟩, rfl⟩; simpa using hv
      · intro hw
        exact ⟨e.symm w, ⟨w, hw, rfl⟩, by simp⟩
    -- Build the iso between the two induced subgraphs and transfer connectedness.
    have hiso := Iso.induceImage e ((Finset.univ \ S' : Finset V) : Set V)
    have heq := image_compl_finset e S'
    rw [hS_eq] at heq
    rw [heq] at hiso
    exact hiso.connected_iff.mp hG_S'

/-- **TW.D.B.1 (a)**: `IsVertexConnected k` is invariant under graph
isomorphism. -/
theorem Iso.isVertexConnected_iff {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (k : Nat) :
    G.IsVertexConnected k ↔ H.IsVertexConnected k :=
  ⟨isVertexConnected_of_iso e, isVertexConnected_of_iso e.symm⟩

/-- **TW.D.B.1 (b)**: vertex connectivity is invariant under graph
isomorphism. -/
theorem Iso.vertexConnectivity_eq {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) :
    G.vertexConnectivity = H.vertexConnectivity := by
  unfold vertexConnectivity
  congr 1
  ext k
  exact e.isVertexConnected_iff k

/-- **TW.D.B.1 (main)**: `IsKConnected k` is invariant under graph
isomorphism.

Combined with the bridge iso `contrInPlaceInduceIsoContrGraph`
(Wheel.lean, Phase TW.D.A.2), this lets us translate
`IsKConnected.three_exists_contractible_edge` (on `contrGraph`)
into the form needed by `IsBuildableFromWheel.of_contrInPlace`
(on `contrInPlace`). -/
theorem Iso.isKConnected_iff {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (k : Nat) :
    G.IsKConnected k ↔ H.IsKConnected k := by
  unfold IsKConnected
  rw [e.vertexConnectivity_eq]

end IsoTransfer

end SimpleGraph
