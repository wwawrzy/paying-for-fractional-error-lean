import GraphTheory.SimpleGraph.Planar.Basic
import GraphTheory.SimpleGraph.Tree.Leaf
import GraphTheory.SimpleGraph.Planar.RotationSystem
import GraphTheory.SimpleGraph.Connectivity.Whitney
import GraphTheory.SimpleGraph.Planar.GirthDensityBound
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Planar girth density bound

For a planar graph with girth at least `g` (where `g ≥ 3`), the classical
density bound is:

    |E| * (g - 2) <= g * (|V| - 2)

This generalizes the two special cases already formalized:
* `g = 3` (general planar): `|E| <= 3|V| - 6`  (Planar.lean, D3)
* `g = 4` (triangle-free planar): `|E| <= 2|V| - 4`  (Planar.lean, D4)

## Approach

The predicate `HasMinGirth G g` expresses that every cycle in `G` has length
at least `g`. The density theorem is proved in
`GraphTheory.SimpleGraph.Planar.GirthDensityBound` from a planar rotation
system and block decomposition; it requires `¬G.IsAcyclic`. This exception is
necessary: an acyclic graph can satisfy any girth lower bound while violating
the density inequality. From the density theorem we derive:

* Sum-of-degrees bound: `sum deg(v) * (g-2) <= 2g * (|V| - 2)`.
* Existence of a low-degree vertex.
* Degeneracy: a planar graph with girth >= g is `floor(2g/(g-2))`-degenerate.

For the degeneracy corollary we use a concrete bound: every non-empty induced
subgraph has a vertex of degree at most `2 * g / (g - 2)` (natural division).

## Main results

* `SimpleGraph.IsPlanar.edgeFinset_card_girth_bound` -- the density theorem.
* `SimpleGraph.IsPlanar.sum_degrees_girth_bound` -- degree-sum consequence.
* `SimpleGraph.IsPlanar.exists_vertex_degree_le_girth` -- low-degree vertex.
* `SimpleGraph.IsPlanar.isKDegenerate_girth` -- degeneracy corollary.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}

/-! ### Girth predicate -/

-- `HasMinGirth`, `HasMinGirth.mono`, and `HasMinGirth.induce` are defined in
-- `GraphTheory.SimpleGraph.Planar.GirthDensityBound` so the density theorem
-- can be proved there without cyclic imports. They are available here by import.

/-- A triangle-free graph has girth at least 4. -/
theorem HasMinGirth.of_cliqueFree_three {G : SimpleGraph V}
    (htf : G.CliqueFree 3) : G.HasMinGirth 4 := by
  unfold HasMinGirth
  rw [le_egirth]
  intro a w hw
  suffices h : 4 ≤ w.length by exact_mod_cast h
  have h3 := hw.three_le_length
  by_contra hlt
  push Not at hlt
  have hlen : w.length = 3 := by omega
  have hexists : Exists (fun s => G.IsNClique 3 s) := by
    rw [is3Clique_iff_exists_cycle_length_three]
    exact Exists.intro a (Exists.intro w (And.intro hw hlen))
  exact hexists.elim (fun s hs => htf s hs)

/-- Every graph trivially has girth at least 3 (the shortest possible cycle
has length 3). -/
theorem hasMinGirth_three (G : SimpleGraph V) : G.HasMinGirth 3 := by
  unfold HasMinGirth
  exact three_le_egirth

-- The topological input `IsPlanar.hasPlanarRotationSystem` (Kuratowski–Wagner /
-- Heffter–Edmonds; Diestel, Proposition 4.2.5) is provided by
-- `GraphTheory.SimpleGraph.Planar.GirthDensityBound` and imported here.

-- `IsPlanar.edgeFinset_card_girth_bound` is proved in
-- `GraphTheory.SimpleGraph.Planar.GirthDensityBound` using Diestel's block
-- decomposition: planar rotation systems on 2-connected blocks, bridge handling,
-- and the block-tree identity `Σ cutVertexMultiplicity = |blocks| - 1`.

/-! ### Consequences of the girth density bound -/

section GirthConsequences

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Sum-of-degrees bound for non-acyclic planar graphs with girth ≥ g:
`(∑ deg(v)) · (g - 2) ≤ 2g · (|V| - 2)`.
Follows from the handshaking lemma `∑ deg = 2|E|` and the density bound.
Requires `¬G.IsAcyclic` (see `edgeFinset_card_girth_bound`). -/
theorem IsPlanar.sum_degrees_girth_bound [inst : Fintype G.edgeSet]
    (hplanar : IsPlanar G) (hgirth : G.HasMinGirth g)
    (hconn : G.Connected) (hcycle : ¬G.IsAcyclic)
    (hg : 3 ≤ g) (hcard : 3 ≤ Fintype.card V) :
    (Finset.sum Finset.univ fun v => G.degree v) * (g - 2) ≤
      2 * g * (Fintype.card V - 2) := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hinst : inst = G.fintypeEdgeSet := Subsingleton.elim _ _
  subst hinst
  have h := hplanar.edgeFinset_card_girth_bound G hgirth hconn hcycle hg hcard
  calc 2 * G.edgeFinset.card * (g - 2)
      = 2 * (G.edgeFinset.card * (g - 2)) := by ring
    _ ≤ 2 * (g * (Fintype.card V - 2)) := Nat.mul_le_mul_left 2 h
    _ = 2 * g * (Fintype.card V - 2) := by ring

/-- Every non-acyclic planar graph with girth ≥ g on at least 3 vertices has a
vertex of degree at most `2 * g / (g - 2)` (natural division, i.e. floor).

Proof: by contradiction. If all degrees exceeded `2g/(g-2)`, i.e. were at least
`2g/(g-2) + 1`, the sum of degrees times `(g-2)` would exceed `2g*(|V|-2)`,
contradicting `sum_degrees_girth_bound`. The key arithmetic fact is
`Nat.lt_div_mul_add`: `2g < (2g/(g-2) + 1) * (g-2)`.

Requires `¬G.IsAcyclic` (see `edgeFinset_card_girth_bound`). For acyclic
graphs, the stronger bound `∃ v, degree v ≤ 1` holds via
`IsAcyclic.exists_degree_le_one`. -/
theorem IsPlanar.exists_vertex_degree_le_girth [Fintype G.edgeSet] [Nonempty V]
    (hplanar : IsPlanar G) (hgirth : G.HasMinGirth g)
    (hconn : G.Connected) (hcycle : ¬G.IsAcyclic)
    (hg : 3 ≤ g) (hcard : 3 ≤ Fintype.card V) :
    ∃ v : V, G.degree v ≤ 2 * g / (g - 2) := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hsum := hplanar.sum_degrees_girth_bound G hgirth hconn hcycle hg hcard
  have hmin : Fintype.card V * (2 * g / (g - 2) + 1) ≤
      (Finset.sum Finset.univ fun v => G.degree v) := by
    have hle : (Finset.sum Finset.univ fun (_ : V) => 2 * g / (g - 2) + 1) ≤
        (Finset.sum Finset.univ fun v => G.degree v) := by
      apply Finset.sum_le_sum
      intro v _
      exact h v
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    exact hle
  have hg2 : 0 < g - 2 := by omega
  have hk := Nat.lt_div_mul_add (a := 2 * g) hg2
  have hk2 : 2 * g + 1 ≤ (2 * g / (g - 2) + 1) * (g - 2) := by linarith
  have chain1 : Fintype.card V * (2 * g + 1) ≤
      Fintype.card V * ((2 * g / (g - 2) + 1) * (g - 2)) :=
    Nat.mul_le_mul_left _ hk2
  have chain2 : Fintype.card V * (2 * g / (g - 2) + 1) * (g - 2) ≤
      (Finset.sum Finset.univ fun v => G.degree v) * (g - 2) :=
    Nat.mul_le_mul_right _ hmin
  have chain2b : Fintype.card V * ((2 * g / (g - 2) + 1) * (g - 2)) =
      Fintype.card V * (2 * g / (g - 2) + 1) * (g - 2) := by ring
  have combined : Fintype.card V * (2 * g + 1) ≤
      2 * g * (Fintype.card V - 2) := by linarith
  have h1 : 2 * g * (Fintype.card V - 2) + 2 * g * 2 =
      2 * g * Fintype.card V := by
    nlinarith [Nat.sub_add_cancel (show 2 ≤ Fintype.card V by omega)]
  nlinarith

end GirthConsequences

/-! ### Helper: transfer walks between induced subgraphs -/

/-- Transfer a Walk from `G.induce s` to `G.induce s'` when `s' ⊆ s` and all
vertices on the walk belong to `s'`. -/
private noncomputable def walk_transfer {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {s : Finset V}
    (s' : Finset V) (hs' : s' ⊆ s) :
    ∀ {a b : {x // x ∈ (s : Set V)}}
    (w : (G.induce (s : Set V)).Walk a b)
    (ha : a.val ∈ s') (hb : b.val ∈ s')
    (hall : ∀ x ∈ w.support, x.val ∈ s'),
    (G.induce (s' : Set V)).Walk ⟨a.val, ha⟩ ⟨b.val, hb⟩
  | _, _, .nil, ha, hb, _ => by
    have : ha = hb := Subsingleton.elim _ _
    subst this; exact Walk.nil
  | a, _, @Walk.cons _ _ _ mid _ hadj wtail, ha, hb, hall => by
    have hmid_s' : mid.val ∈ s' :=
      hall mid (List.mem_cons_of_mem _ (Walk.start_mem_support wtail))
    have hall' : ∀ x ∈ wtail.support, x.val ∈ s' :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have hadj_G : G.Adj a.val mid.val := by
      rw [induce_adj] at hadj; exact hadj
    have hstep : (G.induce (s' : Set V)).Adj ⟨a.val, ha⟩ ⟨mid.val, hmid_s'⟩ := by
      rw [induce_adj]; exact hadj_G
    exact Walk.cons hstep (walk_transfer s' hs' wtail hmid_s' hb hall')

/-! ### Degeneracy corollary -/

/-- **Planar graphs with girth ≥ g are `(2g/(g-2))`-degenerate** (nat division).

For any nonempty `s ⊆ V`, the induced subgraph `G[s]` is planar and has
girth ≥ g. If `|s| ≥ 3` and `G[s]` is not acyclic, the girth density bound
gives a vertex of degree at most `2g/(g-2)`. If `G[s]` is acyclic,
`IsAcyclic.exists_degree_le_one` gives degree ≤ 1 ≤ `2g/(g-2)`.
If `|s| < 3`, degrees are trivially small.

Concrete instances:
* `g = 3`: 6/1 = 6, but the sharper `5` comes from `3n-6` (D3).
* `g = 4`: 8/2 = 4, but the sharper `3` comes from `2n-4` (D4).
* `g = 5`: 10/3 = 3 (nat div).
* `g = 6`: 12/4 = 3.
* `g ≥ 7`: 2 (since `2g/(g-2)` converges to 2 from above). -/
theorem IsPlanar.isKDegenerate_girth {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] (hplanar : IsPlanar G) (hgirth : G.HasMinGirth g)
    (hg : 3 ≤ g) :
    G.IsKDegenerate (2 * g / (g - 2)) := by
  intro s hs
  let H := G.induce (s : Set V)
  have hH : IsPlanar H := hplanar.induce s
  have hHg : H.HasMinGirth g := hgirth.induce s
  haveI : Fintype (s : Set V) := inferInstance
  haveI : DecidableRel H.Adj := inferInstance
  by_cases hcard : 3 ≤ s.card
  · have hcard' : 3 ≤ Fintype.card { x : V // x ∈ (s : Set V) } := by
      change 3 ≤ Fintype.card (s : Set V)
      simp; omega
    haveI : Nonempty { x : V // x ∈ (s : Set V) } := by
      rw [← Fintype.card_pos_iff]; omega
    -- The induced subgraph may or may not be acyclic. If acyclic, we use the
    -- stronger bound degree ≤ 1; otherwise we use the girth density bound.
    by_cases hacH : H.IsAcyclic
    · -- Acyclic case: exists vertex of degree ≤ 1 ≤ 2g/(g-2)
      obtain ⟨⟨v, hv⟩, hdeg⟩ := IsAcyclic.exists_degree_le_one (G := H) hacH
      refine ⟨v, hv, ?_⟩
      have hbound : 1 ≤ 2 * g / (g - 2) := by
        have hge : 1 ≤ g - 2 := by omega
        rw [Nat.le_div_iff_mul_le hge]; omega
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
    · -- Non-acyclic case: H = G[s] may not be connected. Extract the
      -- connected component containing a cycle and apply density bound.
      classical
      -- Extract cycle
      simp only [IsAcyclic] at hacH; push Not at hacH
      obtain ⟨⟨v₀, hv₀⟩, cyc, hcyc⟩ := hacH
      -- s' = component of v₀ (vertices reachable from v₀ in H)
      let inComp : V → Prop := fun w => ∃ (hw : w ∈ (s : Set V)),
        H.Reachable ⟨v₀, hv₀⟩ ⟨w, hw⟩
      haveI : DecidablePred inComp := fun w => Classical.dec _
      let s' := s.filter inComp
      -- s' ⊆ s
      have hs'_sub : s' ⊆ s := Finset.filter_subset _ _
      -- v₀ ∈ s'
      have hv₀s' : v₀ ∈ s' := by
        simp only [s', Finset.mem_filter]; exact ⟨hv₀, hv₀, ⟨Walk.nil⟩⟩
      -- Key property: neighbors in s of vertices in s' are also in s'
      have hclosed : ∀ v ∈ s', ∀ w ∈ s, G.Adj v w → w ∈ s' := by
        intro v hv w hw hadj
        simp only [s', Finset.mem_filter] at hv ⊢
        obtain ⟨_, hvm, hvr⟩ := hv
        exact ⟨hw, hw, hvr.trans ((induce_adj.mpr hadj).reachable)⟩
      -- Therefore: inducedDegree v s = inducedDegree v s' for v ∈ s'
      have hdeg_eq : ∀ v ∈ s', G.inducedDegree v s = G.inducedDegree v s' := by
        intro v hv
        unfold inducedDegree
        congr 1; ext w; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hws, hadj⟩; exact ⟨hclosed v hv w hws hadj, hadj⟩
        · rintro ⟨hws', hadj⟩; exact ⟨hs'_sub hws', hadj⟩
      -- Set up G.induce s'
      let H' := G.induce (s' : Set V)
      have hH'p : IsPlanar H' := hplanar.induce s'
      have hH'g : H'.HasMinGirth g := hgirth.induce s'
      -- |s'| ≥ 3 (cycle has ≥ 3 distinct vertices, all reachable from v₀)
      have hmem_s' : ∀ u ∈ cyc.support, u.val ∈ s' := by
        intro u hu
        simp only [s', Finset.mem_filter]
        exact ⟨u.property, u.property, (cyc.takeUntil u hu).reachable⟩
      have hs'_card : 3 ≤ s'.card := by
        have htail_nodup := hcyc.support_nodup
        have htail_len : 3 ≤ cyc.support.tail.length := by
          have h1 := hcyc.three_le_length
          have h2 := cyc.length_support
          rw [List.length_tail]; omega
        have hmapped_nodup : (cyc.support.tail.map Subtype.val).Nodup :=
          htail_nodup.map Subtype.val_injective
        have hmapped_sub : ∀ w ∈ (cyc.support.tail.map Subtype.val), w ∈ s' := by
          intro w hw; rw [List.mem_map] at hw
          obtain ⟨u, hu, rfl⟩ := hw
          exact hmem_s' u (List.tail_subset _ hu)
        calc 3 ≤ (cyc.support.tail.map Subtype.val).toFinset.card := by
              rw [List.toFinset_card_of_nodup hmapped_nodup, List.length_map]
              exact htail_len
          _ ≤ s'.card := Finset.card_le_card (fun w hw =>
              hmapped_sub w (List.mem_toFinset.mp hw))
      have hcard'' : 3 ≤ Fintype.card { x : V // x ∈ (s' : Set V) } := by
        change 3 ≤ Fintype.card (s' : Set V); simp; omega
      haveI : Nonempty { x : V // x ∈ (s' : Set V) } := by
        rw [← Fintype.card_pos_iff]; omega
      -- H' is connected (all vertices reachable from v₀)
      have hreach_v0 : ∀ (u : { x // x ∈ (s' : Set V) }),
          H'.Reachable ⟨v₀, hv₀s'⟩ u := by
        intro ⟨w, hw⟩
        obtain ⟨hw', hrw⟩ := (Finset.mem_filter.mp (show w ∈ s' from hw)).2
        obtain ⟨ww⟩ := hrw
        have hall : ∀ x ∈ ww.support, x.val ∈ s' := by
          intro x hx; simp only [s', Finset.mem_filter]
          exact ⟨x.property, x.property, (ww.takeUntil x hx).reachable⟩
        exact (walk_transfer s' hs'_sub ww hv₀s' hw hall).reachable
      have hH'conn : H'.Connected :=
        Connected.mk (fun u w => (hreach_v0 u).symm.trans (hreach_v0 w))
      -- H' may or may not be acyclic. Handle both cases.
      -- Helper: degree in H' = inducedDegree v s' for v ∈ s'
      have hdeg_H' : ∀ (v : V) (hv : v ∈ (s' : Set V)),
          H'.degree ⟨v, hv⟩ = G.inducedDegree v s' := by
        intro v hv
        unfold inducedDegree degree; simp only [neighborFinset]
        rw [Set.toFinset_card, ← Fintype.card_coe (s'.filter (G.Adj v))]
        apply Fintype.card_of_bijective
          (f := fun (u : H'.neighborSet ⟨v, hv⟩) =>
            (⟨u.val.val, by
              rw [Finset.mem_filter]; exact ⟨u.val.property, by
                have := u.property
                rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj] at this
                exact this⟩⟩ : { x // x ∈ s'.filter (G.Adj v) }))
        constructor
        · intro a b hab; simp only [Subtype.mk.injEq] at hab
          exact Subtype.ext (Subtype.ext hab)
        · intro ⟨w, hw⟩; rw [Finset.mem_filter] at hw
          exact ⟨⟨⟨w, hw.1⟩, by rw [mem_neighborSet, induce_adj]; exact hw.2⟩, by simp⟩
      by_cases hH'cyc : H'.IsAcyclic
      · -- H' is acyclic: use degree ≤ 1 ≤ 2g/(g-2)
        obtain ⟨⟨v, hv⟩, hdeg⟩ := IsAcyclic.exists_degree_le_one (G := H') hH'cyc
        have hvs : v ∈ s := hs'_sub hv
        refine ⟨v, hvs, ?_⟩
        have hbound : 1 ≤ 2 * g / (g - 2) := by
          have hge : 1 ≤ g - 2 := by omega
          rw [Nat.le_div_iff_mul_le hge]; omega
        have hv' : v ∈ s' := Finset.mem_coe.mp hv
        calc G.inducedDegree v s
            = G.inducedDegree v s' := hdeg_eq v hv'
          _ = H'.degree ⟨v, hv⟩ := (hdeg_H' v hv).symm
          _ ≤ 1 := hdeg
          _ ≤ 2 * g / (g - 2) := hbound
      · -- H' is not acyclic: use the density bound
        obtain ⟨⟨v, hv⟩, hdeg⟩ :=
          hH'p.exists_vertex_degree_le_girth H' hH'g hH'conn hH'cyc hg hcard''
        have hvs : v ∈ s := hs'_sub hv
        refine ⟨v, hvs, ?_⟩
        have hv' : v ∈ s' := Finset.mem_coe.mp hv
        calc G.inducedDegree v s
            = G.inducedDegree v s' := hdeg_eq v hv'
          _ = H'.degree ⟨v, hv⟩ := (hdeg_H' v hv).symm
          _ ≤ 2 * g / (g - 2) := hdeg
  · obtain ⟨v, hv⟩ := hs
    refine ⟨v, hv, ?_⟩
    calc G.inducedDegree v s
        ≤ s.card := G.inducedDegree_le_card v s
      _ ≤ 2 * g / (g - 2) := by
        have hge : 1 ≤ g - 2 := by omega
        have : 2 ≤ 2 * g / (g - 2) := by
          rw [Nat.le_div_iff_mul_le hge]
          -- 2 * (g - 2) ≤ 2 * g
          have : g - 2 ≤ g := Nat.sub_le g 2
          calc 2 * (g - 2) ≤ 2 * g := Nat.mul_le_mul_left 2 this
            _ ≤ 2 * g := le_refl _
        omega

/-! ### Specialization: girth ≥ 5 gives 3-degenerate -/

/-- Planar graphs with girth ≥ 5 are 3-degenerate.
Since `2 * 5 / (5 - 2) = 10 / 3 = 3` (nat div), this is a direct
consequence of `isKDegenerate_girth`. -/
theorem IsPlanar.isKDegenerate_three_of_girth_five {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj]
    (hplanar : IsPlanar G) (hgirth : G.HasMinGirth 5) :
    G.IsKDegenerate 3 := by
  have h := hplanar.isKDegenerate_girth hgirth (by norm_num : 3 ≤ 5)
  -- 2 * 5 / (5 - 2) = 10 / 3 = 3
  norm_num at h
  exact h

/-- Planar graphs with girth ≥ 6 are 3-degenerate.
Since `2 * 6 / (6 - 2) = 12 / 4 = 3` (nat div). -/
theorem IsPlanar.isKDegenerate_three_of_girth_six {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj]
    (hplanar : IsPlanar G) (hgirth : G.HasMinGirth 6) :
    G.IsKDegenerate 3 := by
  have h := hplanar.isKDegenerate_girth hgirth (by norm_num : 3 ≤ 6)
  norm_num at h
  exact h

/-- Planar graphs with girth ≥ 7 are 2-degenerate.
Since `2 * 7 / (7 - 2) = 14 / 5 = 2` (nat div). -/
theorem IsPlanar.isKDegenerate_two_of_girth_seven {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj]
    (hplanar : IsPlanar G) (hgirth : G.HasMinGirth 7) :
    G.IsKDegenerate 2 := by
  have h := hplanar.isKDegenerate_girth hgirth (by norm_num : 3 ≤ 7)
  norm_num at h
  exact h

/-! ### Triangle-free planar density from girth bound -/

/-- A connected component's `toSimpleGraph` equals `G.induce C.supp`. -/
private theorem ConnectedComponent.toSimpleGraph_eq_induce {G : SimpleGraph V}
    (C : G.ConnectedComponent) : C.toSimpleGraph = G.induce C.supp := by
  ext ⟨u, hu⟩ ⟨v, hv⟩; exact C.toSimpleGraph_adj hu hv

/-- Helper: planarity of a connected component's toSimpleGraph. -/
private theorem IsPlanar.component {G : SimpleGraph V}
    (hplanar : IsPlanar G) (C : G.ConnectedComponent) :
    IsPlanar C.toSimpleGraph := by
  rw [C.toSimpleGraph_eq_induce]; exact hplanar.induce C.supp

/-- Helper: triangle-freeness of a connected component. -/
private theorem CliqueFree.component {G : SimpleGraph V}
    (htf : G.CliqueFree 3) (C : G.ConnectedComponent) :
    C.toSimpleGraph.CliqueFree 3 := by
  rw [C.toSimpleGraph_eq_induce]; exact htf.induce C.supp

/-- **Triangle-free planar density (non-acyclic case)** — proved from girth bound.

Proved by decomposing into connected components:
- Each component C satisfies |E(C)| + 2 ≤ 2|V(C)| (tree or girth bound).
- Summing: |E| + 2k ≤ 2|V| where k = #components.
- Case k ≥ 2: |E| ≤ 2|V| - 2k ≤ 2|V| - 4.
- Case k = 1: G is connected; apply girth bound directly with g = 4. -/
theorem IsPlanar.edgeFinset_card_le_triangle_free_of_girth {V : Type*}
    {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hplanar : IsPlanar G) (htf : G.CliqueFree 3)
    (hcycle : ¬G.IsAcyclic)
    (hcard : LE.le 3 (Fintype.card V)) :
    LE.le G.edgeFinset.card (2 * Fintype.card V - 4) := by
  classical
  haveI : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
  -- Component decomposition
  have hE := sum_edgeFinset_components_eq (G := G)
  have hV := sum_card_components_eq (G := G)
  -- Per-component weak bound: |E(C)| + 2 ≤ 2|V(C)|
  have hper : ∀ C : G.ConnectedComponent,
      C.toSimpleGraph.edgeFinset.card + 2 ≤ 2 * Fintype.card ↥C := by
    intro C
    haveI : Nonempty ↥C := by
      obtain ⟨v, hv⟩ := C.nonempty_supp; exact ⟨⟨v, hv⟩⟩
    have hCconn := C.connected_toSimpleGraph
    by_cases hCac : C.toSimpleGraph.IsAcyclic
    · -- Tree: |E| + 1 = |V|
      have htree := (IsTree.mk hCconn hCac).card_edgeFinset
      have hpos : 0 < Fintype.card ↥C := Fintype.card_pos
      omega
    · -- Non-acyclic component: use girth bound with g = 4
      have hCgirth := HasMinGirth.of_cliqueFree_three (htf.component C)
      -- |V(C)| ≥ 3: a cycle needs ≥ 3 distinct vertices
      have hCcard : 3 ≤ Fintype.card ↥C := by
        by_contra hlt; push Not at hlt
        simp only [IsAcyclic] at hCac; push Not at hCac
        obtain ⟨v, w, hw⟩ := hCac
        have h3 := hw.three_le_length
        have hnd := hw.support_nodup
        have hlen := w.length_support
        have hsup := List.Nodup.length_le_card hnd
        rw [List.length_tail] at hsup
        omega
      have hbound := IsPlanar.edgeFinset_card_girth_bound
        C.toSimpleGraph (hplanar.component C) hCgirth hCconn hCac
        (by omega : 3 ≤ 4) hCcard
      -- hbound : |E| * (4 - 2) ≤ 4 * (|V| - 2)
      -- i.e. |E| * 2 ≤ 4 * (|V| - 2) = 4|V| - 8
      -- so |E| ≤ 2|V| - 4, hence |E| + 2 ≤ 2|V| - 2 ≤ 2|V|
      have h2 : 2 ≤ Fintype.card ↥C := by omega
      nlinarith [Nat.sub_add_cancel h2]
  -- Sum: |E| + 2k ≤ 2|V|
  have hsum : G.edgeFinset.card + 2 * Fintype.card G.ConnectedComponent ≤
      2 * Fintype.card V := by
    -- ∑ C, (|E(C)| + 2) ≤ ∑ C, (2 * |V(C)|)
    have h1 : (∑ C : G.ConnectedComponent, (C.toSimpleGraph.edgeFinset.card + 2)) ≤
        (∑ C : G.ConnectedComponent, (2 * Fintype.card ↥C)) :=
      Finset.sum_le_sum (fun C _ => hper C)
    -- Resolve Fintype instance mismatch between classical and synthesized instances
    have hE' : ∑ C : G.ConnectedComponent, C.toSimpleGraph.edgeFinset.card =
        G.edgeFinset.card := by convert hE
    have hV' : ∑ C : G.ConnectedComponent, Fintype.card ↥C = Fintype.card V := by
      convert hV
    -- LHS = |E| + 2k
    have h2 : (∑ C : G.ConnectedComponent, (C.toSimpleGraph.edgeFinset.card + 2)) =
        G.edgeFinset.card + 2 * Fintype.card G.ConnectedComponent := by
      rw [Finset.sum_add_distrib, hE']
      simp [Finset.sum_const, Finset.card_univ]; ring
    -- RHS = 2|V|
    have h3 : (∑ C : G.ConnectedComponent, (2 * Fintype.card ↥C)) =
        2 * Fintype.card V := by
      rw [← Finset.mul_sum, hV']
    linarith
  -- Case split: k ≥ 2 or k = 1
  have hk : 1 ≤ Fintype.card G.ConnectedComponent := Fintype.card_pos
  by_cases hk2 : 2 ≤ Fintype.card G.ConnectedComponent
  · -- k ≥ 2: |E| ≤ 2|V| - 2k ≤ 2|V| - 4
    omega
  · -- k = 1: G is connected; use girth bound directly
    have hk1 : Fintype.card G.ConnectedComponent = 1 := by omega
    have hconn : G.Connected := by
      rw [connected_iff]; constructor
      · intro u v
        have := Fintype.card_le_one_iff.mp (le_of_eq hk1)
        exact ConnectedComponent.exact (this
          (G.connectedComponentMk u) (G.connectedComponentMk v))
      · exact ⟨Classical.arbitrary V⟩
    have hgirth : G.HasMinGirth 4 := HasMinGirth.of_cliqueFree_three htf
    have hbound := IsPlanar.edgeFinset_card_girth_bound
      G hplanar hgirth hconn hcycle (by omega : 3 ≤ 4) hcard
    -- hbound : |E| * (4 - 2) ≤ 4 * (|V| - 2)
    -- Normalize: |E| * 2 ≤ 4 * (|V| - 2)
    -- Since |V| ≥ 2: 4 * (|V| - 2) + 8 = 4 * |V|, so |E| * 2 + 8 ≤ 4 * |V|
    -- Hence |E| + 4 ≤ 2 * |V|, i.e. |E| ≤ 2|V| - 4
    have hv2 : 2 ≤ Fintype.card V := by omega
    -- Additive form: |E| * 2 + 8 ≤ 4 * |V|
    have hadd : G.edgeFinset.card * 2 + 8 ≤ 4 * Fintype.card V := by
      have := Nat.sub_add_cancel hv2
      nlinarith
    omega

/-! ### Triangle-free planar density consequences -/

section TriangleFree

variable {V : Type*}

/-- **Triangle-free planar edge density** (Diestel Prop 4.4.2): A triangle-free
planar graph on `n ≥ 3` vertices has at most `2n - 4` edges.

**Proved** by case analysis:
* **Acyclic:** `|E| < |V|` (forest edge bound), so `|E| ≤ 2|V| - 4` when `|V| ≥ 3`.
* **Non-acyclic:** from `edgeFinset_card_le_triangle_free_of_girth`, which uses
  the girth density bound with g = 4 and connected component decomposition. -/
theorem IsPlanar.edgeFinset_card_le_triangle_free (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [inst : Fintype G.edgeSet]
    (hplanar : IsPlanar G) (htf : G.CliqueFree 3)
    (hcard : LE.le 3 (Fintype.card V)) :
    LE.le G.edgeFinset.card (2 * Fintype.card V - 4) := by
  have hinst : inst = G.fintypeEdgeSet := Subsingleton.elim _ _
  subst hinst
  by_cases hac : G.IsAcyclic
  · haveI : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
    have h := hac.edgeFinset_card_lt
    omega
  · exact hplanar.edgeFinset_card_le_triangle_free_of_girth htf hac hcard

/-- In a **connected** triangle-free planar graph, every face is bounded by at
least 4 edges, so `4|F| ≤ 2|E|`. Proved from the triangle-free edge density
bound `|E| ≤ 2|V| - 4` and Euler's formula for connected graphs. -/
theorem IsPlanar.four_mul_numFaces_le {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hplanar : IsPlanar G) (htf : G.CliqueFree 3)
    (hconn : G.Connected)
    (hcard : LE.le 3 (Fintype.card V)) :
    LE.le (4 * hplanar.numFaces) (2 * G.edgeFinset.card) := by
  unfold numFaces
  rw [connected_card_connectedComponent hconn]
  have hedge := hplanar.edgeFinset_card_le_triangle_free G htf hcard
  have hconn_le := connected_card_le_edgeFinset hconn
  omega

/-- The sum of degrees in a triangle-free planar graph is at most `4|V| - 8`.
Follows from the handshaking lemma and the triangle-free edge density bound. -/
theorem IsPlanar.sum_degrees_le_triangle_free (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hplanar : IsPlanar G) (htf : G.CliqueFree 3)
    (hcard : LE.le 3 (Fintype.card V)) :
    LE.le (Finset.sum Finset.univ fun v => G.degree v) (4 * Fintype.card V - 8) := by
  have h := hplanar.edgeFinset_card_le_triangle_free G htf hcard
  have hconv : @SimpleGraph.edgeFinset V G (inferInstance) =
    @SimpleGraph.edgeFinset V G G.fintypeEdgeSet := by
    congr 1; exact Subsingleton.elim _ _
  rw [hconv] at h
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  omega

/-- Every triangle-free planar graph on at least 3 vertices has a vertex of
degree at most 3. If all degrees were ≥ 4, the sum would be ≥ 4|V|, but
it is at most 4|V| - 8. -/
theorem IsPlanar.exists_vertex_degree_le_three
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Nonempty V]
    (hplanar : IsPlanar G) (htf : G.CliqueFree 3)
    (hcard : LE.le 3 (Fintype.card V)) :
    Exists fun v : V => LE.le (G.degree v) 3 := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hsum := hplanar.sum_degrees_le_triangle_free G htf hcard
  have hmin : LE.le (4 * Fintype.card V)
      (Finset.sum Finset.univ fun v => G.degree v) := by
    have hle : LE.le (Finset.sum Finset.univ fun (_v : V) => 4)
        (Finset.sum Finset.univ fun v => G.degree v) := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Nat.lt_iff_add_one_le.mp (h v)
    simp [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    linarith
  omega

/-- **Every triangle-free planar graph is 3-degenerate.**

For any nonempty `s ⊆ V`, the induced subgraph `G[s]` is both planar and
triangle-free. If `|s| ≥ 3`, the triangle-free edge density bound gives
average degree `< 4`, so some vertex has degree `≤ 3` in `G[s]`.
If `|s| < 3`, every vertex trivially has degree `≤ 2 ≤ 3`. -/
theorem IsPlanar.isKDegenerate_three {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] (hplanar : IsPlanar G) (htf : G.CliqueFree 3) :
    G.IsKDegenerate 3 := by
  intro s hs
  let H := G.induce (s : Set V)
  have hH : IsPlanar H := hplanar.induce s
  have hHtf : H.CliqueFree 3 := htf.induce s
  haveI : Fintype (s : Set V) := inferInstance
  haveI : DecidableRel H.Adj := inferInstance
  by_cases hcard : 3 ≤ s.card
  · have hcard' : 3 ≤ Fintype.card { x : V // x ∈ (s : Set V) } := by
      change 3 ≤ Fintype.card (s : Set V)
      simp; omega
    haveI : Nonempty { x : V // x ∈ (s : Set V) } := by
      rw [← Fintype.card_pos_iff]; omega
    obtain ⟨⟨v, hv⟩, hdeg⟩ := hH.exists_vertex_degree_le_three H hHtf hcard'
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
      _ ≤ 3 := by omega

end TriangleFree

/-- **General planar density (non-acyclic case)** — proved from girth bound with g=3.

Proved by decomposing into connected components:
- Each component C satisfies |E(C)| + 3 ≤ 3|V(C)| (tree or girth bound).
- Summing: |E| + 3k ≤ 3|V| where k = #components.
- Case k ≥ 2: |E| ≤ 3|V| - 3k ≤ 3|V| - 6.
- Case k = 1: G is connected; apply girth bound directly with g = 3. -/
theorem IsPlanar.edgeFinset_card_le_nonacyclic_of_girth {V : Type*}
    {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hplanar : IsPlanar G) (hcycle : ¬G.IsAcyclic)
    (hcard : LE.le 3 (Fintype.card V)) :
    LE.le G.edgeFinset.card (3 * Fintype.card V - 6) := by
  classical
  haveI : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
  -- Component decomposition
  have hE := sum_edgeFinset_components_eq (G := G)
  have hV := sum_card_components_eq (G := G)
  -- Per-component weak bound: |E(C)| + 3 ≤ 3|V(C)|
  have hper : ∀ C : G.ConnectedComponent,
      C.toSimpleGraph.edgeFinset.card + 3 ≤ 3 * Fintype.card ↥C := by
    intro C
    haveI : Nonempty ↥C := by
      obtain ⟨v, hv⟩ := C.nonempty_supp; exact ⟨⟨v, hv⟩⟩
    have hCconn := C.connected_toSimpleGraph
    by_cases hCac : C.toSimpleGraph.IsAcyclic
    · -- Tree: |E| + 1 = |V|, and |V| + 2 ≤ 3|V| since |V| ≥ 1
      have htree := (IsTree.mk hCconn hCac).card_edgeFinset
      have hpos : 0 < Fintype.card ↥C := Fintype.card_pos
      omega
    · -- Non-acyclic component: use girth bound with g = 3
      have hCgirth := hasMinGirth_three C.toSimpleGraph
      -- |V(C)| ≥ 3: a cycle needs ≥ 3 distinct vertices
      have hCcard : 3 ≤ Fintype.card ↥C := by
        by_contra hlt; push Not at hlt
        simp only [IsAcyclic] at hCac; push Not at hCac
        obtain ⟨v, w, hw⟩ := hCac
        have h3 := hw.three_le_length
        have hnd := hw.support_nodup
        have hlen := w.length_support
        have hsup := List.Nodup.length_le_card hnd
        rw [List.length_tail] at hsup
        omega
      have hbound := IsPlanar.edgeFinset_card_girth_bound
        C.toSimpleGraph (hplanar.component C) hCgirth hCconn hCac
        (by omega : 3 ≤ 3) hCcard
      -- hbound : |E| * (3 - 2) ≤ 3 * (|V| - 2)
      -- i.e. |E| * 1 ≤ 3 * (|V| - 2) = 3|V| - 6
      -- so |E| + 3 ≤ 3|V| - 3 ≤ 3|V|
      have h2 : 2 ≤ Fintype.card ↥C := by omega
      nlinarith [Nat.sub_add_cancel h2]
  -- Sum: |E| + 3k ≤ 3|V|
  have hsum : G.edgeFinset.card + 3 * Fintype.card G.ConnectedComponent ≤
      3 * Fintype.card V := by
    -- ∑ C, (|E(C)| + 3) ≤ ∑ C, (3 * |V(C)|)
    have h1 : (∑ C : G.ConnectedComponent, (C.toSimpleGraph.edgeFinset.card + 3)) ≤
        (∑ C : G.ConnectedComponent, (3 * Fintype.card ↥C)) :=
      Finset.sum_le_sum (fun C _ => hper C)
    -- Resolve Fintype instance mismatch between classical and synthesized instances
    have hE' : ∑ C : G.ConnectedComponent, C.toSimpleGraph.edgeFinset.card =
        G.edgeFinset.card := by convert hE
    have hV' : ∑ C : G.ConnectedComponent, Fintype.card ↥C = Fintype.card V := by
      convert hV
    -- LHS = |E| + 3k
    have h2 : (∑ C : G.ConnectedComponent, (C.toSimpleGraph.edgeFinset.card + 3)) =
        G.edgeFinset.card + 3 * Fintype.card G.ConnectedComponent := by
      rw [Finset.sum_add_distrib, hE']
      simp [Finset.sum_const, Finset.card_univ]; ring
    -- RHS = 3|V|
    have h3 : (∑ C : G.ConnectedComponent, (3 * Fintype.card ↥C)) =
        3 * Fintype.card V := by
      rw [← Finset.mul_sum, hV']
    linarith
  -- Case split: k ≥ 2 or k = 1
  have hk : 1 ≤ Fintype.card G.ConnectedComponent := Fintype.card_pos
  by_cases hk2 : 2 ≤ Fintype.card G.ConnectedComponent
  · -- k ≥ 2: |E| ≤ 3|V| - 3k ≤ 3|V| - 6
    omega
  · -- k = 1: G is connected; use girth bound directly
    have hk1 : Fintype.card G.ConnectedComponent = 1 := by omega
    have hconn : G.Connected := by
      rw [connected_iff]; constructor
      · intro u v
        have := Fintype.card_le_one_iff.mp (le_of_eq hk1)
        exact ConnectedComponent.exact (this
          (G.connectedComponentMk u) (G.connectedComponentMk v))
      · exact ⟨Classical.arbitrary V⟩
    have hgirth : G.HasMinGirth 3 := hasMinGirth_three G
    have hbound := IsPlanar.edgeFinset_card_girth_bound
      G hplanar hgirth hconn hcycle (by omega : 3 ≤ 3) hcard
    -- hbound : |E| * (3 - 2) ≤ 3 * (|V| - 2)
    -- Normalize: |E| * 1 ≤ 3 * (|V| - 2)
    -- Since |V| ≥ 2: 3 * (|V| - 2) + 6 = 3 * |V|, so |E| + 6 ≤ 3 * |V|
    have hv2 : 2 ≤ Fintype.card V := by omega
    have hadd : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
      have := Nat.sub_add_cancel hv2
      nlinarith
    omega

/-! ### Edge density bound (Diestel Corollary 4.2.10) and consequences

These results use `IsPlanar.edgeFinset_card_le_nonacyclic_of_girth`, proved
from `edgeFinset_card_girth_bound` and the decomposition into connected
components. They are placed here so the density proof and its consequences
share the required imports. -/

/-- A planar graph on `n ≥ 3` vertices has at most `3n - 6` edges (Diestel Cor 4.2.10).

**Proved** by case analysis:
* **Acyclic:** `|E| < |V|` (forest edge bound), so `|E| ≤ 3|V| - 6` when `|V| ≥ 3`.
* **Non-acyclic:** apply `edgeFinset_card_le_nonacyclic_of_girth`, which uses
  `edgeFinset_card_girth_bound` and the decomposition into connected components. -/
theorem IsPlanar.edgeFinset_card_le {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [inst : Fintype G.edgeSet]
    (hplanar : IsPlanar G) (hcard : LE.le 3 (Fintype.card V)) :
    LE.le G.edgeFinset.card (3 * Fintype.card V - 6) := by
  have hinst : inst = G.fintypeEdgeSet := Subsingleton.elim _ _
  subst hinst
  by_cases hac : G.IsAcyclic
  · -- Acyclic case: |E| < |V|, so |E| ≤ |V| - 1 ≤ 3|V| - 6 when |V| ≥ 3
    haveI : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
    have h := hac.edgeFinset_card_lt
    omega
  · -- Non-acyclic case: from `edgeFinset_card_le_nonacyclic_of_girth`
    exact hplanar.edgeFinset_card_le_nonacyclic_of_girth hac hcard

/-- Alias for the former name `edgeFinset_card_le_nonacyclic`; the proof is
exactly `edgeFinset_card_le_nonacyclic_of_girth`. -/
theorem IsPlanar.edgeFinset_card_le_nonacyclic {V : Type*}
    {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hplanar : IsPlanar G) (hcycle : ¬G.IsAcyclic)
    (hcard : LE.le 3 (Fintype.card V)) :
    LE.le G.edgeFinset.card (3 * Fintype.card V - 6) :=
  hplanar.edgeFinset_card_le_nonacyclic_of_girth hcycle hcard

/-- In a **connected** planar graph, every face is bounded by at least 3 edges,
and every edge borders at most 2 faces, so `3|F| ≤ 2|E|`.
Proved from the edge density bound `|E| ≤ 3|V| - 6` and Euler's formula for
connected graphs (`F = E - V + 2`). The connectivity hypothesis is necessary:
the statement is false for disconnected graphs. -/
theorem IsPlanar.three_mul_numFaces_le {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hplanar : IsPlanar G)
    (hconn : G.Connected)
    (hcard : LE.le 3 (Fintype.card V)) :
    LE.le (3 * hplanar.numFaces) (2 * G.edgeFinset.card) := by
  unfold numFaces
  rw [connected_card_connectedComponent hconn]
  have hinst : ‹Fintype G.edgeSet› = G.fintypeEdgeSet := Subsingleton.elim _ _
  subst hinst
  have hedge := hplanar.edgeFinset_card_le G hcard
  have hconn_le := connected_card_le_edgeFinset hconn
  omega

/-! ### Useful consequences -/

section PlanarConsequences

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A planar graph is sparse: `2 * |E|` is at most `6 * |V| - 12` (equivalent
to the density bound, but in a form that avoids natural-number subtraction
issues). -/
theorem IsPlanar.two_mul_edgeFinset_card_le [Fintype G.edgeSet]
    (hplanar : IsPlanar G) (hcard : LE.le 3 (Fintype.card V)) :
    LE.le (2 * G.edgeFinset.card) (6 * Fintype.card V - 12) := by
  have h := hplanar.edgeFinset_card_le G hcard
  omega

/-- The sum of degrees in a planar graph is at most `6|V| - 12`.
This follows from the handshaking lemma and the edge density bound. -/
theorem IsPlanar.sum_degrees_le
    (hplanar : IsPlanar G) (hcard : LE.le 3 (Fintype.card V)) :
    LE.le (Finset.sum Finset.univ fun v => G.degree v) (6 * Fintype.card V - 12) := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  exact hplanar.two_mul_edgeFinset_card_le G hcard

/-- Every planar graph on at least 3 vertices has a vertex of degree at most 5.
This follows from the sum-of-degrees bound: if all degrees were at least 6,
the sum would exceed `6|V| - 12`. -/
theorem IsPlanar.exists_vertex_degree_le_five
    [Nonempty V] (hplanar : IsPlanar G) (hcard : LE.le 3 (Fintype.card V)) :
    Exists fun v : V => LE.le (G.degree v) 5 := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hsum := hplanar.sum_degrees_le G hcard
  have hmin : LE.le (6 * Fintype.card V)
      (Finset.sum Finset.univ fun v => G.degree v) := by
    have hle : LE.le (Finset.sum Finset.univ fun (_v : V) => 6)
        (Finset.sum Finset.univ fun v => G.degree v) := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Nat.lt_iff_add_one_le.mp (h v)
    simp [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    linarith
  omega

end PlanarConsequences

/-! ### Planar → 5-degenerate (Diestel Cor 4.2.10) -/

/-- **Every planar graph is 5-degenerate** (Diestel, Corollary 4.2.10).

For any nonempty `s ⊆ V`, the induced subgraph `G[s]` is planar. If `|s| ≥ 3`,
the edge density bound gives average degree `< 6`, so some vertex has degree
`≤ 5` in `G[s]`. If `|s| < 3`, every vertex trivially has degree `≤ 2 ≤ 5`. -/
theorem IsPlanar.isKDegenerate_five {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] (hplanar : IsPlanar G) :
    G.IsKDegenerate 5 := by
  intro s hs
  let H := G.induce (s : Set V)
  have hH : IsPlanar H := hplanar.induce s
  haveI : Fintype (s : Set V) := inferInstance
  haveI : DecidableRel H.Adj := inferInstance
  by_cases hcard : 3 ≤ s.card
  · have hcard' : 3 ≤ Fintype.card { x : V // x ∈ (s : Set V) } := by
      change 3 ≤ Fintype.card (s : Set V)
      simp; omega
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

end SimpleGraph
