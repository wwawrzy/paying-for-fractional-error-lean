/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Duplicate
import Mathlib.Data.List.NodupEquivFin

/-!
# Bipartite graphs and odd cycles

This file proves the classical characterization of bipartite graphs in terms
of odd cycles (Diestel, *Graph Theory* 5th ed., Proposition 1.6.1):
a simple graph is bipartite iff it does not contain a cycle of odd length.

This answers the TODO in `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`
("Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.").

## Main definitions

* `SimpleGraph.HasOddCycle G`: the proposition that `G` contains a cycle of odd length.

## Main results

* `SimpleGraph.isBipartite_iff_no_odd_cycle`:
  `G.IsBipartite ↔ ¬G.HasOddCycle`.
* `SimpleGraph.isBipartite_iff_forall_cycle_even`:
  `G.IsBipartite ↔ ∀ v (p : G.Walk v v), p.IsCycle → Even p.length`.

## Implementation notes

The proof proceeds via `two_colorable_iff_forall_loop_even` from
`Mathlib.Combinatorics.SimpleGraph.ConcreteColorings`. The non-trivial
direction (no odd cycle implies bipartite) reduces to showing that every
odd-length closed walk contains an odd cycle, which is proved by strong
induction on the walk length: if the walk is not already a cycle, it is
either not a trail (has a repeated edge) or has a repeated vertex in
`support.tail`. In either case the walk can be shortened while preserving
odd length, providing the recursion.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

open Walk

/-- A graph has an odd cycle if there is a closed walk forming a cycle of odd length. -/
def HasOddCycle (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ Odd p.length

/-- If a closed walk `p : G.Walk v v` has odd length and some vertex `u` appears
twice in `p.support.tail`, then there exists a strictly shorter closed walk
of odd length in `G`. -/
private lemma odd_shorter_walk_of_duplicate_vertex
    [DecidableEq V] {v : V} (p : G.Walk v v)
    (hodd : Odd p.length)
    (u : V)
    (h_dup : List.Duplicate u p.support.tail) :
    ∃ (w : V) (q : G.Walk w w), Odd q.length ∧ q.length < p.length := by
  -- Extract two Fin indices where u appears in p.support.tail
  rw [List.duplicate_iff_exists_distinct_get] at h_dup
  obtain ⟨n, m, hnm, hu_n, hu_m⟩ := h_dup
  have h_supp_len : p.support.length = p.length + 1 := Walk.length_support p
  have h_tail_len : p.support.tail.length = p.length := by
    simp [List.length_tail, h_supp_len]
  have hni_lt : n.val < p.length := by
    have := n.isLt; omega
  have hmi_lt : m.val < p.length := by
    have := m.isLt; omega
  have hlt : n.val < m.val := hnm
  -- getVert at positions n.val+1 and m.val+1 equals u
  have h_gv_n : p.getVert (n.val + 1) = u := by
    have hbound : n.val + 1 < p.support.length := by omega
    rw [← Walk.support_getElem_eq_getVert p hbound]
    have h_eq : p.support[n.val + 1]'hbound =
        p.support.tail[n.val]'(by omega) := by
      simp [List.getElem_tail]
    rw [h_eq]
    have : p.support.tail.get ⟨n.val, by omega⟩ = u := hu_n.symm
    simpa [List.get_eq_getElem] using this
  have h_gv_m : p.getVert (m.val + 1) = u := by
    have hbound : m.val + 1 < p.support.length := by omega
    rw [← Walk.support_getElem_eq_getVert p hbound]
    have h_eq : p.support[m.val + 1]'hbound =
        p.support.tail[m.val]'(by omega) := by
      simp [List.getElem_tail]
    rw [h_eq]
    have : p.support.tail.get ⟨m.val, by omega⟩ = u := hu_m.symm
    simpa [List.get_eq_getElem] using this
  -- Split p at the two occurrences of u (positions a = n+1, b = m+1).
  set a := n.val + 1
  set b := m.val + 1
  have h_a_lt_b : a < b := by simp [a, b]; omega
  have h_b_le : b ≤ p.length := by simp [b]; omega
  have h_gv_a : p.getVert a = u := h_gv_n
  have h_gv_b : p.getVert b = u := h_gv_m
  have h_drop_end : (p.drop a).getVert (b - a) = u := by
    rw [Walk.drop_getVert]
    have : a + (b - a) = b := by omega
    rw [this]; exact h_gv_b
  have h_drop_len : (p.drop a).length = p.length - a := Walk.drop_length p a
  have h_ba_le : b - a ≤ (p.drop a).length := by omega
  have hW1_len : ((p.drop a).take (b - a)).length = b - a := by
    rw [Walk.take_length]; omega
  have hW2_len : (((p.take a).copy rfl h_gv_a).append ((p.drop b).copy h_gv_b rfl)).length =
      p.length - (b - a) := by
    simp [Walk.length_append, Walk.length_copy, Walk.take_length, Walk.drop_length]; omega
  have hsum : (b - a) + (p.length - (b - a)) = p.length := by omega
  -- Since p.length is odd and = (b-a) + (p.length - (b-a)), at least one summand is odd.
  have hone_odd : Odd (b - a) ∨ Odd (p.length - (b - a)) := by
    rcases Nat.even_or_odd (b - a) with heven | hodd_ba
    · right
      rw [← Nat.not_even_iff_odd]
      intro heven2
      have heven_sum : Even p.length := by
        have hsum2 : p.length = b - a + (p.length - (b - a)) := by omega
        rw [hsum2]; exact heven.add heven2
      exact (Nat.not_even_iff_odd.mpr hodd) heven_sum
    · left; exact hodd_ba
  have h_ba_pos : 1 ≤ b - a := by omega
  have h_rest_pos : 1 ≤ p.length - (b - a) := by omega
  have hW1_lt : b - a < p.length := by omega
  have hW2_lt : p.length - (b - a) < p.length := by omega
  -- Construct the two shorter closed sub-walks.
  let W1 : G.Walk u u :=
    ((p.drop a).take (b - a)).copy h_gv_a h_drop_end
  have W1_len : W1.length = b - a := by
    simp only [W1, Walk.length_copy, Walk.take_length, Walk.drop_length]; omega
  let W2 : G.Walk v v :=
    ((p.take a).copy rfl h_gv_a).append ((p.drop b).copy h_gv_b rfl)
  have W2_len : W2.length = p.length - (b - a) := by
    simp only [W2, Walk.length_append, Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  rcases hone_odd with hodd1 | hodd2
  · exact ⟨u, W1, W1_len ▸ hodd1, W1_len ▸ hW1_lt⟩
  · exact ⟨v, W2, W2_len ▸ hodd2, W2_len ▸ hW2_lt⟩

/-- If a closed walk `p : G.Walk v v` of odd length is not a trail (has a repeated edge),
then there exists a strictly shorter closed walk of odd length in `G`.

The argument reduces to `odd_shorter_walk_of_duplicate_vertex` by showing that
a repeated edge forces a repeated vertex in `p.support.tail`. -/
private lemma odd_shorter_walk_of_repeated_edge
    [DecidableEq V] {v : V} (p : G.Walk v v)
    (hodd : Odd p.length)
    (h_not_trail : ¬p.IsTrail) :
    ∃ (w : V) (q : G.Walk w w), Odd q.length ∧ q.length < p.length := by
  rw [Walk.isTrail_def] at h_not_trail
  rw [← List.exists_duplicate_iff_not_nodup] at h_not_trail
  obtain ⟨e, h_edge_dup⟩ := h_not_trail
  rw [List.duplicate_iff_exists_distinct_get] at h_edge_dup
  obtain ⟨ni, mi, hlt, he_ni, he_mi⟩ := h_edge_dup
  have h_edges_len : p.edges.length = p.length := Walk.length_edges p
  -- Reduce to producing a duplicate in `p.support.tail`, then apply the vertex lemma.
  suffices h : ¬p.support.tail.Nodup by
    rw [← List.exists_duplicate_iff_not_nodup] at h
    obtain ⟨u, h_dup⟩ := h
    exact odd_shorter_walk_of_duplicate_vertex p hodd u h_dup
  have hni_lt : ni.val < p.length := by
    have h := ni.isLt; simp [h_edges_len] at h; exact h
  have hmi_lt : mi.val < p.length := by
    have h := mi.isLt; simp [h_edges_len] at h; exact h
  have htail_len : p.support.tail.length = p.length := by
    simp [List.length_tail, Walk.length_support]
  -- Identify p.edges[k] with the unordered pair of consecutive support entries.
  have h_en : p.edges[ni.val]'ni.isLt =
      s(p.support[ni.val]'(by rw [Walk.length_support]; omega),
        p.support.tail[ni.val]'(by omega)) := by
    simp only [Walk.edges_eq_zipWith_support, List.getElem_zipWith]
  have h_em : p.edges[mi.val]'mi.isLt =
      s(p.support[mi.val]'(by rw [Walk.length_support]; omega),
        p.support.tail[mi.val]'(by omega)) := by
    simp only [Walk.edges_eq_zipWith_support, List.getElem_zipWith]
  have h_eq : p.edges[ni.val]'ni.isLt = p.edges[mi.val]'mi.isLt := by
    have hni' : e = p.edges[ni.val]'ni.isLt := by
      simp only [List.get_eq_getElem] at he_ni; exact he_ni
    have hmi' : e = p.edges[mi.val]'mi.isLt := by
      simp only [List.get_eq_getElem] at he_mi; exact he_mi
    rw [← hni', hmi']
  rw [h_en, h_em] at h_eq
  -- Translate support/tail accesses into `getVert`.
  have hsn : p.support[ni.val]'(by rw [Walk.length_support]; omega) =
      p.getVert ni.val :=
    Walk.support_getElem_eq_getVert p (by rw [Walk.length_support]; omega)
  have hsm : p.support[mi.val]'(by rw [Walk.length_support]; omega) =
      p.getVert mi.val :=
    Walk.support_getElem_eq_getVert p (by rw [Walk.length_support]; omega)
  have htn : p.support.tail[ni.val]'(by omega) = p.getVert (ni.val + 1) := by
    rw [List.getElem_tail]
    exact Walk.support_getElem_eq_getVert p (by rw [Walk.length_support]; omega)
  have htm : p.support.tail[mi.val]'(by omega) = p.getVert (mi.val + 1) := by
    rw [List.getElem_tail]
    exact Walk.support_getElem_eq_getVert p (by rw [Walk.length_support]; omega)
  rw [hsn, hsm, htn, htm] at h_eq
  rw [Sym2.eq_iff] at h_eq
  -- Reduce to finding two distinct indices k1, k2 with getVert (k1+1) = getVert (k2+1).
  suffices h_dup : ∃ (k1 k2 : Nat), k1 < p.length ∧ k2 < p.length ∧ k1 ≠ k2 ∧
      p.getVert (k1 + 1) = p.getVert (k2 + 1) by
    obtain ⟨k1, k2, hk1, hk2, hne, heq⟩ := h_dup
    exact List.not_nodup_of_get_eq_of_ne p.support.tail
      (Fin.mk k1 (by omega)) (Fin.mk k2 (by omega))
      (by simp only [List.get_eq_getElem, List.getElem_tail,
            Walk.support_getElem_eq_getVert]; exact heq)
      (by simp [Fin.ext_iff]; exact hne)
  rcases h_eq with ⟨_, h2⟩ | ⟨h1, h2⟩
  · -- Case A: getVert(ni+1) = getVert(mi+1) — direct duplicate in tail.
    exact ⟨ni.val, mi.val, hni_lt, hmi_lt, by omega, h2⟩
  · -- Case B: getVert(ni) = getVert(mi+1) and getVert(ni+1) = getVert(mi).
    by_cases hni_eq : ni.val = mi.val - 1
    · -- Adjacent edges: mi = ni + 1, so getVert(ni) = getVert(ni+2).
      by_cases hni_zero : ni.val = 0
      · -- ni = 0, mi = 1: getVert 0 = v = getVert 2, and getVert p.length = v.
        have h_plen_ne_2 : p.length ≠ 2 := by
          intro heq; rw [heq] at hodd; simp [Nat.odd_iff] at hodd
        have hgv2_v : p.getVert 2 = v := by
          have hv : p.getVert 0 = v := Walk.getVert_zero p
          have : ni.val = 0 := hni_zero
          have : mi.val = 1 := by omega
          rw [this] at h1; rw [hni_zero] at h1; rw [hv] at h1; exact h1.symm
        have hplen_pos : p.length ≥ 1 := hodd.pos
        have h1_ne : (1 : Nat) ≠ p.length - 1 := by
          intro heq; exact h_plen_ne_2 (by omega)
        refine ⟨1, p.length - 1, by omega, by omega, h1_ne, ?_⟩
        rw [show p.length - 1 + 1 = p.length from by omega]
        rw [hgv2_v, Walk.getVert_length]
      · -- ni ≥ 1: getVert(ni-1+1) = getVert(ni+1+1) gives a duplicate at distinct indices.
        have hmi_eq : mi.val = ni.val + 1 := by omega
        rw [hmi_eq] at h1
        refine ⟨ni.val - 1, ni.val + 1, by omega, by omega, by omega, ?_⟩
        rw [show ni.val - 1 + 1 = ni.val from by omega,
            show ni.val + 1 + 1 = ni.val + 2 from by omega]
        exact h1
    · -- Non-adjacent: getVert(ni+1) = getVert((mi-1)+1), with ni ≠ mi - 1.
      refine ⟨ni.val, mi.val - 1, hni_lt, by omega, by omega, ?_⟩
      rw [show mi.val - 1 + 1 = mi.val from by omega]
      exact h2

/-- Strong induction body for `odd_closedWalk_contains_odd_cycle`. -/
private lemma odd_closedWalk_contains_odd_cycle_aux :
    ∀ n : ℕ, ∀ (v : V) (p : G.Walk v v), p.length = n → Odd p.length →
    G.HasOddCycle := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v p hlen hodd
  by_cases hcyc : p.IsCycle
  · exact ⟨v, p, hcyc, hodd⟩
  have h_not_nil : p ≠ Walk.nil := by
    intro heq; simp [heq] at hodd
  rw [Walk.isCycle_def] at hcyc
  push_neg at hcyc
  by_cases htrail : p.IsTrail
  · -- Trail with a duplicate vertex in support.tail.
    have h_nodup : ¬p.support.tail.Nodup := hcyc htrail h_not_nil
    rw [← List.exists_duplicate_iff_not_nodup] at h_nodup
    obtain ⟨u, h_dup⟩ := h_nodup
    obtain ⟨w, q, hq_odd, hq_lt⟩ :=
      odd_shorter_walk_of_duplicate_vertex p hodd u h_dup
    exact ih q.length (hlen ▸ hq_lt) w q rfl hq_odd
  · -- Not a trail: repeated edge.
    obtain ⟨w, q, hq_odd, hq_lt⟩ :=
      odd_shorter_walk_of_repeated_edge p hodd htrail
    exact ih q.length (hlen ▸ hq_lt) w q rfl hq_odd

/-- Every odd-length closed walk in `G` contains an odd cycle. -/
private lemma odd_closedWalk_contains_odd_cycle {v : V} (p : G.Walk v v)
    (hodd : Odd p.length) : G.HasOddCycle :=
  odd_closedWalk_contains_odd_cycle_aux p.length v p rfl hodd

/-- A bipartite graph contains no odd cycle.

Every closed walk in a `2`-colorable graph has even length
(`two_colorable_iff_forall_loop_even`), hence no cycle can have odd length. -/
theorem isBipartite_no_odd_cycle (hG : G.IsBipartite) : ¬G.HasOddCycle := by
  intro hodd
  have heven : Even (hodd.choose_spec.choose.length) :=
    two_colorable_iff_forall_loop_even.mp hG _ _
  have hpodd : Odd (hodd.choose_spec.choose.length) :=
    hodd.choose_spec.choose_spec.2
  simp [Nat.even_iff, Nat.odd_iff] at heven hpodd
  omega

/-- A graph containing no odd cycle is bipartite.

By `two_colorable_iff_forall_loop_even` it suffices to show that every closed
walk has even length; an odd-length closed walk would contain an odd cycle by
`odd_closedWalk_contains_odd_cycle`. -/
theorem isBipartite_of_no_odd_cycle (h : ¬G.HasOddCycle) : G.IsBipartite := by
  apply two_colorable_iff_forall_loop_even.mpr
  intro u w
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  exact h (odd_closedWalk_contains_odd_cycle w hne)

/-- **Diestel, Proposition 1.6.1.** A simple graph is bipartite iff it has no odd cycle. -/
theorem isBipartite_iff_no_odd_cycle :
    G.IsBipartite ↔ ¬G.HasOddCycle :=
  ⟨isBipartite_no_odd_cycle, isBipartite_of_no_odd_cycle⟩

/-- A simple graph is bipartite iff every cycle has even length. -/
theorem isBipartite_iff_forall_cycle_even :
    G.IsBipartite ↔ ∀ v : V, ∀ p : G.Walk v v, p.IsCycle → Even p.length := by
  constructor
  · intro hG v p _hcyc
    exact two_colorable_iff_forall_loop_even.mp hG v p
  · intro h
    apply isBipartite_of_no_odd_cycle
    intro hodd
    have hpodd : Odd hodd.choose_spec.choose.length :=
      hodd.choose_spec.choose_spec.2
    have hcyc : hodd.choose_spec.choose.IsCycle :=
      hodd.choose_spec.choose_spec.1
    have heven : Even hodd.choose_spec.choose.length :=
      h hodd.choose hodd.choose_spec.choose hcyc
    simp [Nat.even_iff, Nat.odd_iff] at heven hpodd
    omega

end SimpleGraph
