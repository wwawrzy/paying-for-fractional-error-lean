/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib

/-!
# Graph minors via branch sets (Diestel §1.7)

A graph `H` is a *minor* of `G` (written `H ≤m G`) if there exists a family of
pairwise disjoint, connected subsets of `V(G)` — called *branch sets* — one for
each vertex of `H`, such that whenever two vertices are adjacent in `H` there
is an edge in `G` between their branch sets.


Source: `MdsLean/MdsLean/Minor.lean`.

The related files `MdsLean/MdsLean/Contraction.lean` and
`MdsLean/MdsLean/ContractibleEdge.lean` (edge contraction operations) may be
merged into this `Minor/` directory in a future KID.

Mathlib currently has no upstream notion of graph minor in the branch-set sense
nor of `H`-minor-freeness; this file fills that gap and is intended for upstream
promotion.

## Main definitions

* `SimpleGraph.MinorModel` — a minor model (branch set mapping) from `H` into `G`.
* `SimpleGraph.IsMinor` — `H` is a minor of `G` (existence of a minor model),
  written `H ≤m G`.
* `SimpleGraph.IsHMinorFree` — `G` is `H`-minor-free (`H` is not a minor of `G`).
* `SimpleGraph.IsK5MinorFree` — `G` is `K₅`-minor-free.
* `SimpleGraph.IsK33MinorFree` — `G` is `K₃,₃`-minor-free.
* `SimpleGraph.IsKMinorFree` — `G` is `Kₕ`-minor-free (parametric in `h`).

## Main results

* `SimpleGraph.MinorModel.refl` — every graph is a minor of itself
  (identity model with singleton branch sets).
* `SimpleGraph.IsMinor.refl` — reflexivity of the minor relation.
* `SimpleGraph.IsMinor.trans` — transitivity of the minor relation.
* `SimpleGraph.IsMinor.of_subgraph` — every subgraph is a minor.
* `SimpleGraph.IsMinor.bot_of_empty` — the empty graph on `Empty` is a minor
  of any graph.
* `SimpleGraph.isMinor_isPreorder` — the minor relation is a preorder.
* `SimpleGraph.isK5MinorFree_iff_isKMinorFree` — `IsK5MinorFree` agrees with
  `IsKMinorFree 5`.
* `SimpleGraph.isHMinorFree_of_empty` — the empty graph on `Empty` is
  `H`-minor-free whenever `H` is nonempty.
* `SimpleGraph.bot_isHMinorFree_of_hasEdge` — edgeless graphs are
  `H`-minor-free whenever `H` has at least one edge.
* `SimpleGraph.bot_isHMinorFree_completeGraph_two` — edgeless graphs are
  `K₂`-minor-free.
* `SimpleGraph.bot_isK5MinorFree` — edgeless graphs are `K₅`-minor-free.
* `SimpleGraph.bot_isK33MinorFree` — edgeless graphs are `K₃,₃`-minor-free.
* `SimpleGraph.IsHMinorFree.minor` — `H`-minor-freeness is preserved under
  taking minors.
* `SimpleGraph.IsHMinorFree.of_minor` — `H`-minor-freeness transfers to
  larger excluded minors.

## Implementation notes

The proof of transitivity composes minor models: for each vertex `a` of `A`,
the combined branch set is `⋃ b ∈ mAB.branchSet a, mBC.branchSet b`. Connectedness
of the union is established by walking along a walk in `B.induce (mAB.branchSet a)`
and chaining reachability within and between the corresponding branch sets in `C`
(see the private lemma `walk_branchSet_union_connected`).

## References

* Diestel, *Graph Theory*, 5th ed., §1.7.
-/

namespace SimpleGraph

universe u v

/-! ### Minor model -/

/-- A *minor model* of `H` in `G` is a family of branch sets witnessing `H ≤_m G`.

Each vertex `h` of `H` is mapped to a nonempty connected subset `branchSet h` of
the vertices of `G`. The branch sets are pairwise disjoint, and for each edge
`{h₁, h₂}` in `H` there is an edge in `G` between `branchSet h₁` and `branchSet h₂`. -/
structure MinorModel {VH : Type u} {VG : Type v}
    (H : SimpleGraph VH) (G : SimpleGraph VG) where
  /-- The branch set for each vertex of `H`. -/
  branchSet : VH → Set VG
  /-- Branch sets are nonempty. -/
  nonempty : ∀ h, (branchSet h).Nonempty
  /-- Branch sets are pairwise disjoint. -/
  disjoint : ∀ h₁ h₂, h₁ ≠ h₂ → Disjoint (branchSet h₁) (branchSet h₂)
  /-- Each branch set induces a connected subgraph of `G`. -/
  connected : ∀ h, (G.induce (branchSet h)).Connected
  /-- Adjacent vertices in `H` have branch sets joined by an edge in `G`. -/
  adjacent : ∀ h₁ h₂, H.Adj h₁ h₂ →
    ∃ v₁ ∈ branchSet h₁, ∃ v₂ ∈ branchSet h₂, G.Adj v₁ v₂

/-- `H` is a minor of `G` if there exists a minor model of `H` in `G`. -/
def IsMinor {VH : Type u} {VG : Type v}
    (H : SimpleGraph VH) (G : SimpleGraph VG) : Prop :=
  Nonempty (MinorModel H G)

@[inherit_doc] scoped infixl:50 " ≤m " => IsMinor

/-! ### Reflexivity -/

section Refl

variable {V : Type u} (G : SimpleGraph V)

/-- The identity minor model: each vertex maps to the singleton containing itself. -/
def MinorModel.refl : MinorModel G G where
  branchSet v := {v}
  nonempty v := ⟨v, rfl⟩
  disjoint v₁ v₂ hne := by
    rw [Set.disjoint_iff]
    intro x ⟨hx₁, hx₂⟩
    rw [Set.mem_singleton_iff] at hx₁ hx₂
    exact hne (hx₁.symm.trans hx₂)
  connected v := by
    rw [connected_iff_exists_forall_reachable]
    exact ⟨⟨v, rfl⟩, fun ⟨w, hw⟩ => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact Reachable.refl _⟩
  adjacent v₁ v₂ hadj := ⟨v₁, rfl, v₂, rfl, hadj⟩

/-- Every graph is a minor of itself. -/
theorem IsMinor.refl : G ≤m G :=
  ⟨MinorModel.refl G⟩

end Refl

/-! ### Subgraph to minor -/

section Subgraph

variable {V : Type u} {G H : SimpleGraph V}

/-- If `G` is a subgraph of `H` (i.e. `G ≤ H`), then `G` is a minor of `H`.
The branch sets are singletons `{v}`. -/
theorem IsMinor.of_subgraph (h : G ≤ H) : G ≤m H :=
  ⟨{
    branchSet := fun v => {v}
    nonempty := fun v => ⟨v, rfl⟩
    disjoint := fun v₁ v₂ hne => by
      rw [Set.disjoint_iff]
      intro x ⟨hx₁, hx₂⟩
      rw [Set.mem_singleton_iff] at hx₁ hx₂
      exact hne (hx₁.symm.trans hx₂)
    connected := fun v => by
      rw [connected_iff_exists_forall_reachable]
      exact ⟨⟨v, rfl⟩, fun ⟨w, hw⟩ => by
        rw [Set.mem_singleton_iff] at hw; subst hw; exact Reachable.refl _⟩
    adjacent := fun v₁ v₂ hadj =>
      ⟨v₁, rfl, v₂, rfl, h hadj⟩
  }⟩

end Subgraph

/-! ### Transitivity -/

section Trans

universe w₁ w₂ w₃
variable {VA : Type w₁} {VB : Type w₂} {VC : Type w₃}

/-- Inclusion homomorphism: if `s ⊆ t`, then `G.induce s →g G.induce t`. -/
private def induceHomOfSubset (G : SimpleGraph VC) {s t : Set VC} (h : s ⊆ t) :
    (G.induce s) →g (G.induce t) where
  toFun := Set.inclusion h
  map_rel' hab := hab

/-- Connected subgraph of an induced graph lifts to a larger induced graph:
if `(C.induce s).Reachable x y` and `s ⊆ t`, then the corresponding elements
are reachable in `C.induce t`. -/
private lemma reachable_induce_of_subset {C : SimpleGraph VC} {s t : Set VC}
    (hst : s ⊆ t) {x y : s} (hr : (C.induce s).Reachable x y) :
    (C.induce t).Reachable (Set.inclusion hst x) (Set.inclusion hst y) :=
  hr.map (induceHomOfSubset C hst)

/-- Key helper for transitivity: the union of branch sets along a walk is connected.

Given a walk `b₀ → b₁ → ⋯ → bₙ` in `B.induce S` and a minor model `mBC`,
the set `⋃ b ∈ walk.support, mBC.branchSet b` is connected in `C`. We prove
the stronger statement that the union along the walk is connected, which is
a subset of the full `⋃ b ∈ S, mBC.branchSet b`. -/
private lemma walk_branchSet_union_connected
    {B : SimpleGraph VB} {C : SimpleGraph VC}
    (mBC : MinorModel B C) {S : Set VB}
    {bx by_ : S}
    (w : (B.induce S).Walk bx by_)
    (T : Set VC)
    (hT : ∀ b : VB, b ∈ S → mBC.branchSet b ⊆ T) :
    ∀ (cx : T) (cy : T),
      (↑cx ∈ mBC.branchSet ↑bx) →
      (↑cy ∈ mBC.branchSet ↑by_) →
      (C.induce T).Reachable cx cy := by
  induction w with
  | @nil u =>
    -- bx = by_ = u, so cx and cy are in the same branch set, which is connected
    intro cx cy hcx hcy
    -- Both cx and cy are in mBC.branchSet u.val, which is connected
    have hconn := (mBC.connected u.val).preconnected
    have hr := hconn ⟨_, hcx⟩ ⟨_, hcy⟩
    exact reachable_induce_of_subset (hT u.val u.prop) hr
  | @cons u v_mid w_end hadj wtail ih =>
    intro cx cy hcx hcy
    -- u is adjacent to v_mid in B.induce S, i.e. B.Adj u.val v_mid.val
    -- Get an edge in C between their branch sets
    have hadj_B : B.Adj ↑u ↑v_mid := hadj
    obtain ⟨e₁, he₁, e₂, he₂, hedge⟩ := mBC.adjacent ↑u ↑v_mid hadj_B
    have he₂T : e₂ ∈ T := hT ↑v_mid v_mid.prop he₂
    have he₁T : e₁ ∈ T := hT ↑u u.prop he₁
    -- e₂ reachable to cy via the tail walk (ih)
    have hr_tail := ih ⟨e₂, he₂T⟩ cy he₂ hcy
    -- cx reachable to e₁ within branchSet u (both in it, and it's connected)
    have hr_cx_e₁ : (C.induce (mBC.branchSet ↑u)).Reachable ⟨↑cx, hcx⟩ ⟨e₁, he₁⟩ :=
      (mBC.connected _).preconnected ⟨_, hcx⟩ ⟨_, he₁⟩
    have hr_cx_e₁T := reachable_induce_of_subset (hT ↑u u.prop) hr_cx_e₁
    -- e₁ adjacent to e₂ in C, both in T, so reachable in C.induce T
    have hadj_T : (C.induce T).Adj ⟨e₁, he₁T⟩ ⟨e₂, he₂T⟩ := hedge
    have hr_e₁_e₂ : (C.induce T).Reachable ⟨e₁, he₁T⟩ ⟨e₂, he₂T⟩ :=
      ⟨Walk.cons hadj_T Walk.nil⟩
    -- Chain: cx ~> e₁ ~> e₂ ~> cy
    exact hr_cx_e₁T.trans (hr_e₁_e₂.trans hr_tail)

/-- The minor relation is transitive: if `A ≤m B` and `B ≤m C` then `A ≤m C`.

The proof composes the two minor models: for each vertex `a` of `A`, the combined
branch set is `⋃ b ∈ mAB.branchSet a, mBC.branchSet b`. -/
theorem IsMinor.trans {A : SimpleGraph VA} {B : SimpleGraph VB} {C : SimpleGraph VC}
    (hAB : A ≤m B) (hBC : B ≤m C) : A ≤m C := by
  obtain ⟨mAB⟩ := hAB
  obtain ⟨mBC⟩ := hBC
  exact ⟨{
    branchSet := fun a => ⋃ b ∈ mAB.branchSet a, mBC.branchSet b
    nonempty := by
      intro a
      rw [Set.nonempty_biUnion]
      obtain ⟨b, hb⟩ := mAB.nonempty a
      exact ⟨b, hb, mBC.nonempty b⟩
    disjoint := by
      intro a₁ a₂ hne
      rw [Set.disjoint_left]
      intro c hc₁ hc₂
      rw [Set.mem_iUnion₂] at hc₁ hc₂
      obtain ⟨b₁, hb₁a₁, hcb₁⟩ := hc₁
      obtain ⟨b₂, hb₂a₂, hcb₂⟩ := hc₂
      by_cases hbne : b₁ = b₂
      · subst hbne
        exact (mAB.disjoint a₁ a₂ hne).ne_of_mem hb₁a₁ hb₂a₂ rfl
      · exact (mBC.disjoint b₁ b₂ hbne).ne_of_mem hcb₁ hcb₂ rfl
    connected := by
      intro a
      rw [connected_iff_exists_forall_reachable]
      obtain ⟨b₀, hb₀⟩ := mAB.nonempty a
      obtain ⟨c₀, hc₀⟩ := mBC.nonempty b₀
      refine ⟨⟨c₀, Set.mem_biUnion hb₀ hc₀⟩, ?_⟩
      intro ⟨c, hc⟩
      rw [Set.mem_iUnion₂] at hc
      obtain ⟨b, hb_mem, hc_mem⟩ := hc
      -- b₀ and b are both in mAB.branchSet a, which is connected in B
      have hconn_a := mAB.connected a
      rw [connected_iff_exists_forall_reachable] at hconn_a
      obtain ⟨root_a, hroot_a⟩ := hconn_a
      have hr_b₀ := hroot_a ⟨b₀, hb₀⟩
      have hr_b := hroot_a ⟨b, hb_mem⟩
      have walk_reach := hr_b₀.symm.trans hr_b
      -- Get a walk from b₀ to b in B.induce (mAB.branchSet a)
      obtain ⟨w⟩ := walk_reach
      -- Use the helper lemma
      have hT : ∀ b' : VB, b' ∈ mAB.branchSet a →
          mBC.branchSet b' ⊆ ⋃ b'' ∈ mAB.branchSet a, mBC.branchSet b'' :=
        fun b' hb' => Set.subset_biUnion_of_mem hb'
      exact walk_branchSet_union_connected mBC w _ hT
        ⟨c₀, Set.mem_biUnion hb₀ hc₀⟩ ⟨c, Set.mem_biUnion hb_mem hc_mem⟩ hc₀ hc_mem
    adjacent := by
      intro a₁ a₂ hadj
      obtain ⟨b₁, hb₁, b₂, hb₂, hbadj⟩ := mAB.adjacent a₁ a₂ hadj
      obtain ⟨c₁, hc₁, c₂, hc₂, hcadj⟩ := mBC.adjacent b₁ b₂ hbadj
      exact ⟨c₁, Set.mem_biUnion hb₁ hc₁, c₂, Set.mem_biUnion hb₂ hc₂, hcadj⟩
  }⟩

end Trans

/-! ### Preorder -/

/-- The minor relation is a preorder: it is reflexive and transitive. -/
theorem isMinor_isPreorder (V : Type u) :
    IsPreorder (SimpleGraph V) (· ≤m ·) where
  refl G := IsMinor.refl G
  trans _ _ _ := IsMinor.trans

/-! ### Bot is a minor of everything -/

section Bot

variable {V : Type u} (G : SimpleGraph V)

/-- The empty graph (⊥) on `Empty` is a minor of any graph. -/
theorem IsMinor.bot_of_empty : (⊥ : SimpleGraph Empty) ≤m G :=
  ⟨{
    branchSet := Empty.elim
    nonempty := fun h => h.elim
    disjoint := fun h => h.elim
    connected := fun h => h.elim
    adjacent := fun h => h.elim
  }⟩

end Bot

/-! ### H-minor-free graphs -/

section MinorFree

/-- A graph `G` is *H-minor-free* if `H` is not a minor of `G`. -/
def IsHMinorFree {VH : Type*} {VG : Type*}
    (G : SimpleGraph VG) (H : SimpleGraph VH) : Prop :=
  ¬ (H ≤m G)

/-- A graph `G` is *K₅-minor-free* if `K₅` is not a minor of `G`. -/
def IsK5MinorFree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsHMinorFree (completeGraph (Fin 5))

/-- A graph `G` is *K₃,₃-minor-free* if `K₃,₃` is not a minor of `G`. -/
def IsK33MinorFree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsHMinorFree (completeBipartiteGraph (Fin 3) (Fin 3))

/-- A graph `G` is *Kₕ-minor-free* if `Kₕ` (the complete graph on `h` vertices) is not
a minor of `G`. This generalises `IsK5MinorFree`. -/
def IsKMinorFree {V : Type*} (G : SimpleGraph V) (h : ℕ) : Prop :=
  G.IsHMinorFree (completeGraph (Fin h))

/-- `IsK5MinorFree` is the same as `IsKMinorFree 5`. -/
theorem isK5MinorFree_iff_isKMinorFree {V : Type*} (G : SimpleGraph V) :
    G.IsK5MinorFree ↔ G.IsKMinorFree 5 :=
  Iff.rfl

/-! #### Basic properties of H-minor-free graphs -/

/-- The empty graph on `Empty` is H-minor-free for every `H` with at least one vertex,
because no branch set can be nonempty in `Empty`. -/
theorem isHMinorFree_of_empty {VH : Type*} [Nonempty VH]
    (H : SimpleGraph VH) :
    (⊥ : SimpleGraph Empty).IsHMinorFree H := by
  intro ⟨m⟩
  obtain ⟨v⟩ : Nonempty VH := inferInstance
  obtain ⟨w, hw⟩ := m.nonempty v
  exact w.elim

/-- The bot (edgeless) graph on any type is H-minor-free whenever `H` has at least
one edge, because the `adjacent` condition of a minor model requires an edge in `G`. -/
theorem bot_isHMinorFree_of_hasEdge {VH : Type*} (V : Type*)
    {H : SimpleGraph VH} {h₁ h₂ : VH} (hadj : H.Adj h₁ h₂) :
    (⊥ : SimpleGraph V).IsHMinorFree H := by
  intro ⟨m⟩
  obtain ⟨v₁, _, v₂, _, hbot⟩ := m.adjacent h₁ h₂ hadj
  exact hbot

/-- The bot graph on any type is K₂-minor-free (it has no edges, so `K₂`
cannot be embedded). -/
theorem bot_isHMinorFree_completeGraph_two (V : Type*) :
    (⊥ : SimpleGraph V).IsHMinorFree (completeGraph (Fin 2)) :=
  bot_isHMinorFree_of_hasEdge V
    (h₁ := (0 : Fin 2)) (h₂ := (1 : Fin 2)) (by decide)

/-- The bot graph on any type is K₅-minor-free. -/
theorem bot_isK5MinorFree (V : Type*) :
    (⊥ : SimpleGraph V).IsK5MinorFree :=
  bot_isHMinorFree_of_hasEdge V (H := completeGraph (Fin 5))
    (h₁ := (0 : Fin 5)) (h₂ := (1 : Fin 5)) (by decide)

/-- The bot graph on any type is K₃,₃-minor-free. -/
theorem bot_isK33MinorFree (V : Type*) :
    (⊥ : SimpleGraph V).IsK33MinorFree :=
  bot_isHMinorFree_of_hasEdge V (H := completeBipartiteGraph (Fin 3) (Fin 3))
    (h₁ := Sum.inl (0 : Fin 3)) (h₂ := Sum.inr (0 : Fin 3))
    (by simp [completeBipartiteGraph])

/-- **Monotonicity in the graph**: if `G` is `H`-minor-free and `G'` is a minor of `G`,
then `G'` is also `H`-minor-free. Contrapositively, if `H` were a minor of `G'`,
then by transitivity `H` would be a minor of `G`, contradicting the assumption.

This relies on `IsMinor.trans`. -/
theorem IsHMinorFree.minor {VH : Type*} {VG : Type*} {VG' : Type*}
    {G : SimpleGraph VG} {G' : SimpleGraph VG'} {H : SimpleGraph VH}
    (hfree : G.IsHMinorFree H) (hminor : G' ≤m G) :
    G'.IsHMinorFree H := by
  intro hHG'
  exact hfree (hHG'.trans hminor)

/-- **Monotonicity in the excluded minor**: if `G` is `H'`-minor-free and `H'` is a minor
of `H`, then `G` is `H`-minor-free. Because if `H` were a minor of `G`, then
`H'` being a minor of `H` and `H` being a minor of `G` gives `H' ≤m G` by transitivity.

This relies on `IsMinor.trans`. -/
theorem IsHMinorFree.of_minor {VH : Type*} {VH' : Type*} {VG : Type*}
    {G : SimpleGraph VG} {H : SimpleGraph VH} {H' : SimpleGraph VH'}
    (hfree : G.IsHMinorFree H') (hminor : H' ≤m H) :
    G.IsHMinorFree H := by
  intro hHG
  exact hfree (hminor.trans hHG)

end MinorFree

/-! ### Vertex deletion -/

/-- Deleting all vertices outside `s` produces a minor.  The minor model uses
the singleton branch set `{v}` for each vertex `v : s`. -/
theorem IsMinor.of_induce {V : Type u} (G : SimpleGraph V) (s : Set V) :
    G.induce s ≤m G := by
  refine ⟨{
    branchSet := fun v => {v.1}
    nonempty := fun v => Set.singleton_nonempty v.1
    disjoint := ?_
    connected := ?_
    adjacent := ?_
  }⟩
  · intro v w hvw
    rw [Set.disjoint_singleton]
    exact fun h => hvw (Subtype.val_injective h)
  · intro v
    rw [connected_iff_exists_forall_reachable]
    exact ⟨⟨v.1, rfl⟩, fun ⟨w, hw⟩ => by
      simp only [Set.mem_singleton_iff] at hw
      subst w
      exact Reachable.refl _⟩
  · intro v w hvw
    exact ⟨v.1, rfl, w.1, rfl, hvw⟩

end SimpleGraph
