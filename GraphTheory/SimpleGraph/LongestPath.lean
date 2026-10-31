/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Longest paths and walk surgery (shared basics)

General, self-contained utilities about **length-maximal paths** and closing paths
into cycles. These are pure Mathlib-level facts (no Hamilton/Dirac content) that are
reused both by the quantitative form of Diestel Prop 1.3.1 (`CycleExistence.lean`)
and by the Pósa-rotation proofs of Dirac/Ore (`Hamilton/`).

* `exists_maximal_isPath` — a finite graph has a path of maximum length.
* `Adj.mem_support_of_maximal_isPath` — neighbours of a maximal path's start lie on it.
* `Walk.IsPath.eq_singleton_of_mem_edges` — a path containing the edge between its
  endpoints is that single edge.
* `Walk.IsPath.append_reverse_isCycle` — two internally disjoint `m`–`m'` paths close
  up to a cycle.
* `Walk.length_takeUntil_getVert` — on a path, `takeUntil (getVert j)` has length `j`.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A length-maximal path exists. -/
theorem exists_maximal_isPath [Nonempty V] :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧
      ∀ (c d : V) (q : G.Walk c d), q.IsPath → q.length ≤ p.length := by
  classical
  set n := Fintype.card V with hn
  set S : Finset ℕ :=
    (Finset.range (n + 1)).filter
      (fun k => ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.length = k) with hS
  have hmem : ∀ k, k ∈ S ↔ k ≤ n ∧ ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.length = k := by
    intro k
    rw [hS, Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
  obtain ⟨a₀⟩ := (inferInstance : Nonempty V)
  have h0 : (0 : ℕ) ∈ S := by
    rw [hmem]; exact ⟨by omega, a₀, a₀, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hSne : S.Nonempty := ⟨0, h0⟩
  set ℓ := S.max' hSne with hℓ
  have hℓmem : ℓ ∈ S := S.max'_mem hSne
  rw [hmem] at hℓmem
  obtain ⟨-, a, b, p, hp, hplen⟩ := hℓmem
  refine ⟨a, b, p, hp, fun c d q hq => ?_⟩
  have hqmem : q.length ∈ S := by rw [hmem]; exact ⟨(hq.length_lt).le, c, d, q, hq, rfl⟩
  have : q.length ≤ ℓ := Finset.le_max' S q.length hqmem
  omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- Neighbours of a maximal path's start lie on the path. -/
theorem Adj.mem_support_of_maximal_isPath
    {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (hmax : ∀ (c d : V) (q : G.Walk c d), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : G.Adj a x) : x ∈ p.support := by
  by_contra hxs
  have hpath : (Walk.cons hx.symm p).IsPath := (Walk.cons_isPath_iff hx.symm p).2 ⟨hp, hxs⟩
  have hle := hmax x b (Walk.cons hx.symm p) hpath
  rw [Walk.length_cons] at hle
  omega

namespace Walk

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A path from `u` to `v` using the edge `s(u, v)` is that single edge. -/
theorem IsPath.eq_singleton_of_mem_edges {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (he : s(u, v) ∈ p.edges) :
    ∃ h : G.Adj u v, p = Walk.cons h Walk.nil := by
  cases p with
  | nil => simp at he
  | cons h p' =>
    rw [edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨h, by rw [(isPath_iff_eq_nil _).mp hp.of_cons]⟩
      · exact absurd rfl h.ne
    · exact absurd (p'.fst_mem_support_of_mem_edges he)
        ((cons_isPath_iff h p').mp hp).2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two distinct internally disjoint paths `p q` from `m` to `m'` close up to a
cycle `p.append q.reverse`. -/
theorem IsPath.append_reverse_isCycle {m m' : V} {p q : G.Walk m m'}
    (hp : p.IsPath) (hq : q.IsPath) (hne : p ≠ q)
    (hdisj : ∀ x ∈ p.support, x ∈ q.support → x = m ∨ x = m') :
    (p.append q.reverse).IsCycle := by
  have hmm : m ≠ m' := by
    rintro rfl
    rw [isPath_iff_eq_nil] at hp hq
    exact hne (hp.trans hq.symm)
  rw [isCycle_def]
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [edges_append, edges_reverse, List.nodup_append']
    refine ⟨hp.isTrail.edges_nodup, List.nodup_reverse.mpr hq.isTrail.edges_nodup, ?_⟩
    intro e hep heq
    rw [List.mem_reverse] at heq
    have key : ∀ e, e ∈ p.edges → e ∈ q.edges → e = s(m, m') := by
      intro e
      induction e using Sym2.ind with
      | _ x y =>
        intro hep heq
        have hadj : G.Adj x y := p.edges_subset_edgeSet hep
        rcases hdisj x (p.fst_mem_support_of_mem_edges hep)
            (q.fst_mem_support_of_mem_edges heq) with rfl | rfl <;>
          rcases hdisj y (p.snd_mem_support_of_mem_edges hep)
            (q.snd_mem_support_of_mem_edges heq) with rfl | rfl
        · exact absurd rfl hadj.ne
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hadj.ne
    have hpe : s(m, m') ∈ p.edges := key e hep heq ▸ hep
    have hqe : s(m, m') ∈ q.edges := key e hep heq ▸ heq
    obtain ⟨h₁, rfl⟩ := hp.eq_singleton_of_mem_edges hpe
    obtain ⟨h₂, rfl⟩ := hq.eq_singleton_of_mem_edges hqe
    exact hne rfl
  · intro hcon
    have hlen : p.length + q.length = 0 := by
      simpa [length_append, length_reverse] using congrArg length hcon
    exact hmm (Walk.eq_of_length_eq_zero (p := p) (by omega))
  · rw [tail_support_append, List.nodup_append']
    refine ⟨hp.support_nodup.tail, hq.reverse.support_nodup.tail, ?_⟩
    intro x hxp hxq
    have hxp' : x ∈ p.support := List.mem_of_mem_tail hxp
    have hxq' : x ∈ q.support := by
      have := List.mem_of_mem_tail hxq
      rwa [support_reverse, List.mem_reverse] at this
    rcases hdisj x hxp' hxq' with rfl | rfl
    · have hnd := hp.support_nodup
      rw [support_eq_cons, List.nodup_cons] at hnd
      exact hnd.1 hxp
    · have hnd := hq.reverse.support_nodup
      rw [support_eq_cons, List.nodup_cons] at hnd
      exact hnd.1 hxq

/-- On a path, `takeUntil` at `getVert j` has length exactly `j`. -/
lemma length_takeUntil_getVert {a b : V} {p : G.Walk a b} (hp : p.IsPath) {j : ℕ}
    (hj : j ≤ p.length) :
    (p.takeUntil (p.getVert j) (p.getVert_mem_support j)).length = j := by
  have h1 := p.getVert_length_takeUntil (p.getVert_mem_support j)
  have h2 := p.length_takeUntil_le (p.getVert_mem_support j)
  exact hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) h1

end Walk

end SimpleGraph
