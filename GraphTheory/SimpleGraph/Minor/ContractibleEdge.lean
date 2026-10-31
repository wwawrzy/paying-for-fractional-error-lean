/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Minor.Contraction
import GraphTheory.SimpleGraph.Connectivity.Whitney

/-! # Edge contraction and 3-connectivity (Diestel Lemma 3.2.1)

This file develops separator and reachability arguments for a graph `G` and
its edge contraction `G/{u,v}`, culminating in the contractible-edge theorem:
every 3-connected graph not isomorphic to `K4` has an edge whose contraction
is 3-connected.

The inverse image of a separator in the contraction separates `G` and has
at most one additional vertex. In a 3-connected graph, a separator of size
at most two in the contraction must contain the contracted class and have
size exactly two. Its inverse image is therefore a triple `{u,v,w}`.
The proof chooses such a triple and a component of minimum size, then uses
a neighboring edge to construct a strictly smaller component.

Reference: Diestel, Graph Theory, 5th edition, Lemma 3.2.1, pp. 45–46. -/

set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace SimpleGraph

namespace EdgeContraction

variable {V : Type*}

/-! ### Inverse image of a set of quotient classes -/

section Preimage

variable [DecidableEq V]

/-- The inverse image of `S : Finset (ContrVertex u v)` consists of vertices
whose quotient class belongs to `S`. -/
def preimageSet (u v : V) (S : Finset (ContrVertex u v)) : Set V :=
  fun w => contrMk u v w ∈ S

/-- Membership in `preimageSet`. -/
@[simp] theorem mem_preimageSet_iff (u v : V)
    (S : Finset (ContrVertex u v)) (w : V) :
    w ∈ preimageSet u v S ↔ contrMk u v w ∈ S := Iff.rfl

/-- The inverse image of a set containing `[u]` also contains `v`. -/
theorem v_mem_preimageSet_of_mem (u v : V)
    (S : Finset (ContrVertex u v)) (h : contrMk u v u ∈ S) :
    v ∈ preimageSet u v S := by
  change contrMk u v v ∈ S
  rw [← contrMk_eq u v]; exact h

end Preimage

section PreimageFintype

variable [Fintype V] [DecidableEq V]

/-- The inverse image as a finset, using decidability of quotient membership. -/
noncomputable def preimageFinset (u v : V)
    (S : Finset (ContrVertex u v)) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => contrMk u v w ∈ S)

@[simp] theorem mem_preimageFinset_iff (u v : V)
    (S : Finset (ContrVertex u v)) (w : V) :
    w ∈ preimageFinset u v S ↔ contrMk u v w ∈ S := by
  classical
  unfold preimageFinset
  simp

end PreimageFintype

/-! ### Cardinality of an inverse image -/

section CardPreimage

variable [Fintype V] [DecidableEq V]

/-- **Inverse-image bound:** `|π⁻¹(S)| ≤ |S| + 1`.
The quotient map is injective away from `v`, so the inverse image has at most
`|S|` vertices other than `v`, and possibly `v` itself. -/
theorem preimageFinset_card_le (u v : V) (huv : u ≠ v)
    (S : Finset (ContrVertex u v)) :
    (preimageFinset u v S).card ≤ S.card + 1 := by
  classical
  -- The quotient map is a bijection from V \ {v} to ContrVertex u v.
  -- preimageFinset u v S ⊆ (preimageFinset u v S \ {v}) ∪ {v}
  -- |preimageFinset u v S| ≤ |preimageFinset u v S \ {v}| + 1.
  -- The vertices other than v mapping into S inject into S.
  have hsub : preimageFinset u v S ⊆ (preimageFinset u v S).erase v ∪ {v} := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv; simp
    · simp [Finset.mem_erase, hw, hwv]
  calc (preimageFinset u v S).card
      ≤ ((preimageFinset u v S).erase v ∪ {v}).card :=
        Finset.card_le_card hsub
    _ ≤ ((preimageFinset u v S).erase v).card + ({v} : Finset V).card :=
        Finset.card_union_le _ _
    _ = ((preimageFinset u v S).erase v).card + 1 := by
        rw [Finset.card_singleton]
    _ ≤ S.card + 1 := by
        -- Injectivity away from v follows from contrMk_injOn_compl_v.
        have hinj : Set.InjOn (contrMk u v)
            ((preimageFinset u v S).erase v : Set V) := by
          intro a ha b hb hab
          simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe] at ha hb
          exact contrMk_injOn_compl_v u v
            (Set.mem_setOf_eq ▸ ha.2) (Set.mem_setOf_eq ▸ hb.2) hab
        have hmaps : ∀ w ∈ ((preimageFinset u v S).erase v),
            contrMk u v w ∈ S := by
          intro w hw
          rw [Finset.mem_erase] at hw
          have := hw.2
          rw [mem_preimageFinset_iff] at this
          exact this
        -- An injection into S bounds the domain cardinality by |S|.
        have h1 := Finset.card_le_card_of_injOn (s := (preimageFinset u v S).erase v)
          (t := S) (f := contrMk u v) hmaps hinj
        exact Nat.add_le_add_right h1 1

/-- If the contracted class does not belong to `S`, then `|π⁻¹(S)| ≤ |S|`.
Indeed, `v` is absent from the inverse image, and the quotient map is injective
on the remaining vertices. -/
theorem preimageFinset_card_le_of_not_mem (u v : V)
    (S : Finset (ContrVertex u v)) (hnotMem : contrMk u v u ∉ S) :
    (preimageFinset u v S).card ≤ S.card := by
  classical
  -- v ∉ preimageFinset u v S
  have hvnot : v ∉ preimageFinset u v S := by
    rw [mem_preimageFinset_iff]
    rw [← contrMk_eq u v]
    exact hnotMem
  have hsub : (preimageFinset u v S : Set V) ⊆ {w | w ≠ v} := by
    intro w hw
    simp only [Set.mem_setOf_eq]
    intro heq
    apply hvnot
    rwa [heq] at hw
  -- The quotient map is injective on vertices other than v.
  have hinj : Set.InjOn (contrMk u v) (preimageFinset u v S : Set V) := by
    intro a ha b hb hab
    exact contrMk_injOn_compl_v u v (hsub ha) (hsub hb) hab
  have hmaps : ∀ w ∈ preimageFinset u v S, contrMk u v w ∈ S := by
    intro w hw; rwa [mem_preimageFinset_iff] at hw
  exact Finset.card_le_card_of_injOn (f := contrMk u v) hmaps hinj

/-- The bound `|π⁻¹(S)| ≤ |S| + 1` also covers sets containing the contracted
class. That class has at most two representatives; all other fibers are
singletons. -/
theorem preimageFinset_card_le_succ_of_mem (u v : V) (huv : u ≠ v)
    (S : Finset (ContrVertex u v)) :
    (preimageFinset u v S).card ≤ S.card + 1 :=
  preimageFinset_card_le u v huv S

end CardPreimage

/-! ### Mapping walks to the contraction

To lift a separator, argue contrapositively: connectedness of `G - π⁻¹(S)`
implies connectedness of `(G/uv) - S`. A walk avoiding the inverse image
maps to reachability between the quotient classes. -/

section WalkLift

variable [DecidableEq V]

/-- An edge whose endpoint classes avoid `T` gives reachability in
`(contrGraph G u v).induce Tᶜ`. Equal classes use reflexivity; distinct classes
are adjacent in the contraction. -/
theorem reachable_in_contrGraph_induce_of_adj (G : SimpleGraph V) (u v : V)
    (T : Set (ContrVertex u v))
    {a b : V} (ha : contrMk u v a ∉ T) (hb : contrMk u v b ∉ T)
    (hadj : G.Adj a b) :
    ((contrGraph G u v).induce Tᶜ).Reachable
      ⟨contrMk u v a, ha⟩ ⟨contrMk u v b, hb⟩ := by
  classical
  by_cases hcl : contrMk u v a = contrMk u v b
  · -- Equal classes are reachable by reflexivity, after identifying their types.
    refine ⟨?_⟩
    refine Walk.nil.copy rfl ?_
    apply Subtype.ext
    exact hcl
  · -- Distinct classes are joined by a contracted edge.
    refine Adj.reachable ?_
    rw [induce_adj]
    exact contrGraph_adj_of_adj G u v hadj hcl

/-- A walk in `G` whose vertices have classes outside `T` gives reachability
between its endpoint classes in `(contrGraph G u v).induce Tᶜ`. -/
theorem reachable_in_contrGraph_induce_of_walk (G : SimpleGraph V) (u v : V)
    (T : Set (ContrVertex u v))
    {a b : V} (p : G.Walk a b)
    (hsupp : ∀ w ∈ p.support, contrMk u v w ∉ T) :
    ((contrGraph G u v).induce Tᶜ).Reachable
      ⟨contrMk u v a, hsupp a p.start_mem_support⟩
      ⟨contrMk u v b, hsupp b p.end_mem_support⟩ := by
  classical
  -- Induct on the walk p.
  induction p with
  | nil =>
    exact Reachable.refl _
  | @cons x y z hadj p' ih =>
    -- The first edge is x–y, followed by the walk from y to z.
    have hxnot : contrMk u v x ∉ T := hsupp x (by simp)
    have hynot : contrMk u v y ∉ T := hsupp y (by simp)
    have hsupp' : ∀ w ∈ p'.support, contrMk u v w ∉ T := by
      intro w hw; exact hsupp w (by simp [hw])
    -- First, the class of x is reachable from the class of y.
    have hxy := reachable_in_contrGraph_induce_of_adj G u v T hxnot hynot hadj
    -- The induction hypothesis connects the classes of y and z.
    have hyz := ih hsupp'
    exact hxy.trans hyz

end WalkLift

/-! ### Lifting walks from the contraction

The reverse reachability argument lifts a walk in `(G/uv) - T` to a walk
in `G - π⁻¹(T)` between arbitrary representatives of its endpoint classes. -/

section WalkLiftBackward

variable [DecidableEq V]

/-- An edge between quotient classes avoiding `T` lifts to reachability
between arbitrary representatives in `G - π⁻¹(T)`. Changing representatives
within the contracted class uses the actual edge `huv : G.Adj u v`. -/
theorem reachable_in_G_induce_of_contrAdj
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (T : Set (ContrVertex u v))
    {a' b' : V}
    (ha' : a' ∈ ((contrMk u v) ⁻¹' T)ᶜ)
    (hb' : b' ∈ ((contrMk u v) ⁻¹' T)ᶜ)
    (hadjC : (contrGraph G u v).Adj (contrMk u v a') (contrMk u v b')) :
    (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
      ⟨a', ha'⟩ ⟨b', hb'⟩ := by
  classical
  -- Choose adjacent representatives a,b of the two quotient classes.
  obtain ⟨a, b, ha_eq, hb_eq, hab⟩ :=
    contrGraph_adj_imp_exists G u v hadjC
  -- Equal classes give equality or the two orientations of the contracted pair.
  have ha_alt : a = a' ∨ (a = u ∧ a' = v) ∨ (a = v ∧ a' = u) :=
    (contrMk_eq_iff u v a a').mp ha_eq
  have hb_alt : b = b' ∨ (b = u ∧ b' = v) ∨ (b = v ∧ b' = u) :=
    (contrMk_eq_iff u v b b').mp hb_eq
  -- If representatives differ, connect them using huv or its symmetric edge.
  -- The two possible changes of representative use the edge u–v.
  -- Every intermediate representative must have its class outside T.
  -- The original representatives a' and b' avoid the inverse image by hypothesis.
  -- The chosen representatives have the same classes, so they also avoid it.
  have ha_pre : a ∈ ((contrMk u v) ⁻¹' T)ᶜ := by
    show contrMk u v a ∉ T
    rw [ha_eq]
    exact ha'
  have hb_pre : b ∈ ((contrMk u v) ⁻¹' T)ᶜ := by
    show contrMk u v b ∉ T
    rw [hb_eq]
    exact hb'
  -- Concatenate the walks a' to a, a to b, and b to b'.
  -- Use reflexivity for equal representatives, otherwise huv or its reverse.
  have step1 : (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
      ⟨a', ha'⟩ ⟨a, ha_pre⟩ := by
    rcases ha_alt with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Reachable.refl _
    · -- For a = u and a' = v, use huv.symm.
      refine Adj.reachable ?_
      rw [induce_adj]
      exact huv.symm
    · -- For a = v and a' = u, use huv.
      refine Adj.reachable ?_
      rw [induce_adj]
      exact huv
  have step2 : (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
      ⟨a, ha_pre⟩ ⟨b, hb_pre⟩ := by
    refine Adj.reachable ?_
    rw [induce_adj]
    exact hab
  have step3 : (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
      ⟨b, hb_pre⟩ ⟨b', hb'⟩ := by
    rcases hb_alt with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Reachable.refl _
    · refine Adj.reachable ?_
      rw [induce_adj]
      exact huv
    · refine Adj.reachable ?_
      rw [induce_adj]
      exact huv.symm
  exact step1.trans (step2.trans step3)

/-- Reachable classes in `(contrGraph G u v).induce Tᶜ` have arbitrary
representatives reachable in `G.induce ((contrMk u v) ⁻¹' T)ᶜ`. -/
theorem reachable_in_G_induce_of_contrReachable
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (T : Set (ContrVertex u v))
    {x y : ContrVertex u v}
    (hx : x ∉ T) (hy : y ∉ T)
    (hxy : ((contrGraph G u v).induce Tᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩)
    {a b : V}
    (ha_pre : a ∈ ((contrMk u v) ⁻¹' T)ᶜ)
    (hb_pre : b ∈ ((contrMk u v) ⁻¹' T)ᶜ)
    (ha_eq : contrMk u v a = x) (hb_eq : contrMk u v b = y) :
    (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
      ⟨a, ha_pre⟩ ⟨b, hb_pre⟩ := by
  classical
  -- Induct on a walk witnessing reachability.
  -- Generalize the endpoints to handle the dependent walk types
  -- and their subtype representatives uniformly.
  -- Generalize the hypotheses depending on the two endpoints.
  obtain ⟨p⟩ := hxy
  -- Prove the statement for arbitrary subtype endpoints and a walk between them.
  suffices hmain : ∀ (xs ys : (Tᶜ : Set (ContrVertex u v)))
      (_ : ((contrGraph G u v).induce Tᶜ).Walk xs ys)
      {a b : V}
      (ha_pre : a ∈ ((contrMk u v) ⁻¹' T)ᶜ)
      (hb_pre : b ∈ ((contrMk u v) ⁻¹' T)ᶜ)
      (_ : contrMk u v a = xs.val) (_ : contrMk u v b = ys.val),
      (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
        ⟨a, ha_pre⟩ ⟨b, hb_pre⟩ by
    exact hmain ⟨x, hx⟩ ⟨y, hy⟩ p ha_pre hb_pre ha_eq hb_eq
  intro xs ys p
  induction p with
  | nil =>
    intro a b ha_pre hb_pre ha_eq hb_eq
    -- For a nil walk, the endpoint classes are equal.
    have hclEq : contrMk u v a = contrMk u v b := by
      rw [ha_eq, hb_eq]
    rcases (contrMk_eq_iff u v a b).mp hclEq with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Reachable.refl _
    · refine Adj.reachable ?_
      rw [induce_adj]
      exact huv
    · refine Adj.reachable ?_
      rw [induce_adj]
      exact huv.symm
  | @cons xs2 ys2 zs2 hadj p' ih =>
    intro a b ha_pre hb_pre ha_eq hb_eq
    -- Choose a representative m of the intermediate class ys2.val.
    obtain ⟨m, hm_eq⟩ := contrMk_surjective u v ys2.val
    have hm_pre : m ∈ ((contrMk u v) ⁻¹' T)ᶜ := by
      show contrMk u v m ∉ T
      rw [hm_eq]
      exact ys2.property
    rw [induce_adj] at hadj
    have hadj_xs_ys : (contrGraph G u v).Adj xs2.val ys2.val := hadj
    have hadj_repr :
        (contrGraph G u v).Adj (contrMk u v a) (contrMk u v m) := by
      rw [ha_eq, hm_eq]
      exact hadj_xs_ys
    have step1 : (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
        ⟨a, ha_pre⟩ ⟨m, hm_pre⟩ :=
      reachable_in_G_induce_of_contrAdj G huv T ha_pre hm_pre hadj_repr
    have step2 : (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Reachable
        ⟨m, hm_pre⟩ ⟨b, hb_pre⟩ :=
      ih hm_pre hb_pre hm_eq hb_eq
    exact step1.trans step2

end WalkLiftBackward

/-! ### Lifting separators through contraction

A separator of size at most two in the contraction lifts to one of size
at most three in `G`. This section uses sets to avoid finiteness instances
for quotient types; cardinality bounds are applied separately. -/

section SeparatorLift

variable [DecidableEq V]

/-- If `G - π⁻¹(T)` is connected, then `(G/uv) - T` is connected.
Equivalently, a quotient set whose inverse image does not separate `G`
does not separate the contraction. -/
theorem contrGraph_induce_connected_of_induce_connected
    (G : SimpleGraph V) (u v : V) (T : Set (ContrVertex u v))
    (hG : (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Connected) :
    ((contrGraph G u v).induce Tᶜ).Connected := by
  classical
  -- Nonemptiness: choose a quotient vertex outside the deleted set.
  have hne_G : Nonempty (((contrMk u v) ⁻¹' T)ᶜ : Set V) := hG.nonempty
  obtain ⟨w, hw⟩ := hne_G
  have hwnot : contrMk u v w ∉ T := hw
  haveI : Nonempty (Tᶜ : Set (ContrVertex u v)) :=
    ⟨⟨contrMk u v w, hwnot⟩⟩
  refine Connected.mk ?_
  -- Show that any two quotient classes outside T are reachable.
  intro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨a, rfl⟩ := contrMk_surjective u v x
  obtain ⟨b, rfl⟩ := contrMk_surjective u v y
  have hax : contrMk u v a ∉ T := hx
  have hby : contrMk u v b ∉ T := hy
  -- Connectedness of G minus the inverse image connects their representatives.
  have hapre : a ∈ (((contrMk u v) ⁻¹' T)ᶜ : Set V) := hax
  have hbpre : b ∈ (((contrMk u v) ⁻¹' T)ᶜ : Set V) := hby
  have hreach :
      (G.induce (((contrMk u v) ⁻¹' T)ᶜ : Set V)).Reachable
        ⟨a, hapre⟩ ⟨b, hbpre⟩ := hG.preconnected _ _
  obtain ⟨p⟩ := hreach
  -- Map the induced-subgraph walk into G.
  let f : (G.induce (((contrMk u v) ⁻¹' T)ᶜ : Set V)) →g G :=
    (Embedding.induce _).toHom
  let p' : G.Walk a b := p.map f
  -- Every vertex of the mapped walk avoids the inverse image of T.
  have hsupp : ∀ w ∈ p'.support, contrMk u v w ∉ T := by
    intro w hw
    show contrMk u v w ∉ T
    have hsubt : ∀ x ∈ p.support, (x : V) ∉ ((contrMk u v) ⁻¹' T) :=
      fun x _ => x.2
    have hsupEq : p'.support = List.map (⇑f) p.support := Walk.support_map f p
    rw [hsupEq, List.mem_map] at hw
    obtain ⟨x, hxsup, hxeq⟩ := hw
    have hh := hsubt x hxsup
    rw [← hxeq]
    exact hh
  exact reachable_in_contrGraph_induce_of_walk G u v T p' hsupp

/-- Connectedness of the contraction after deleting `T` gives connectedness
of `G` after deleting its inverse image, provided the remaining vertex set
is nonempty. The proof lifts reachability between quotient classes to
arbitrary representatives. -/
theorem induce_connected_of_contrGraph_induce_connected
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (T : Set (ContrVertex u v))
    (hC : ((contrGraph G u v).induce Tᶜ).Connected) :
    (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Connected := by
  classical
  -- The induced graph on the complement of the inverse image is nonempty.
  obtain ⟨⟨c, hc⟩⟩ := hC.nonempty
  -- Choose a representative c0 of the class c.
  obtain ⟨c0, hc0_eq⟩ := contrMk_surjective u v c
  have hc0_pre : c0 ∈ ((contrMk u v) ⁻¹' T)ᶜ := by
    show contrMk u v c0 ∉ T
    rw [hc0_eq]
    exact hc
  haveI : Nonempty (((contrMk u v) ⁻¹' T)ᶜ : Set V) := ⟨⟨c0, hc0_pre⟩⟩
  refine Connected.mk ?_
  intro ⟨a, ha_pre⟩ ⟨b, hb_pre⟩
  -- Both endpoint representatives avoid the inverse image of T.
  have ha_T : contrMk u v a ∉ T := ha_pre
  have hb_T : contrMk u v b ∉ T := hb_pre
  -- Their classes are connected in the induced contracted graph.
  have hReachC :
      ((contrGraph G u v).induce Tᶜ).Reachable
        ⟨contrMk u v a, ha_T⟩ ⟨contrMk u v b, hb_T⟩ :=
    hC.preconnected _ _
  exact reachable_in_G_induce_of_contrReachable G huv T
    ha_T hb_T hReachC ha_pre hb_pre rfl rfl

/-- Contrapositively, if `(G/uv) - T` is disconnected, then `G - π⁻¹(T)`
is disconnected. -/
theorem induce_disconnected_of_contrGraph_induce_disconnected
    (G : SimpleGraph V) (u v : V) (T : Set (ContrVertex u v))
    (hcontr : ¬ ((contrGraph G u v).induce Tᶜ).Connected) :
    ¬ (G.induce ((contrMk u v) ⁻¹' T)ᶜ).Connected :=
  fun hG => hcontr (contrGraph_induce_connected_of_induce_connected G u v T hG)

end SeparatorLift

/-! ### Consequences of 3-connectivity for a contraction -/

section ContrThreeConnected

variable [Fintype V] [DecidableEq V]

/-- For a finite vertex set `S`, its set complement equals the coercion of
`Finset.univ \ S`. This connects the set and finset formulations of deletion. -/
theorem set_compl_finset_eq_univ_sdiff
    (S : Finset V) :
    ((↑S : Set V))ᶜ = (↑(Finset.univ \ S) : Set V) := by
  ext x
  simp

/-- **Separator translation for a 3-connected graph.** If `G/uv` has a
separator `S` of size at most two, then `S` contains the contracted class
and has size exactly two.

Its inverse image separates `G`, so 3-connectivity forces at least three
vertices there. The inverse-image bound is `|S| + 1`. If the contracted class
were absent, the stronger bound `|π⁻¹(S)| ≤ |S|` would contradict
3-connectivity. Thus a contraction separator yields a triple `{u,v,w}`. -/
theorem contrSeparator_must_contain_class
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : u ≠ v)
    (h3 : G.IsKConnected 3)
    (S : Finset (ContrVertex u v))
    (hSize : S.card ≤ 2)
    (hSep : ¬ ((contrGraph G u v).induce
      ((↑S : Set (ContrVertex u v)))ᶜ).Connected) :
    contrMk u v u ∈ S ∧ S.card = 2 := by
  classical
  haveI hntV : Nontrivial V := ⟨u, v, huv⟩
  -- The finset inverse image is a separator in G.
  have hGsep_set : ¬ (G.induce
      ((contrMk u v ⁻¹' (↑S : Set (ContrVertex u v)))ᶜ : Set V)).Connected :=
    induce_disconnected_of_contrGraph_induce_disconnected G u v _ hSep
  -- Identify the finset inverse image with the set-theoretic inverse image.
  have hpreEq : (preimageFinset u v S : Set V) =
      contrMk u v ⁻¹' (↑S : Set (ContrVertex u v)) := by
    ext w
    simp [mem_preimageFinset_iff]
  -- Express deletion using Finset.univ minus the inverse image.
  have hGsep : ¬ (G.induce
      ((↑(Finset.univ \ preimageFinset u v S) : Set V))).Connected := by
    rw [← set_compl_finset_eq_univ_sdiff, hpreEq]
    exact hGsep_set
  -- Deleting fewer than three vertices preserves connectedness.
  have hvc : G.IsVertexConnected 3 := h3.isVertexConnected
  refine ⟨?_, ?_⟩
  · -- If the contracted class were absent, the lifted separator would have size at most two.
    by_contra huinS
    have hTcard : (preimageFinset u v S).card ≤ 2 :=
      le_trans (preimageFinset_card_le_of_not_mem u v S huinS) hSize
    have hconn := hvc.2 (preimageFinset u v S) (by omega)
    exact hGsep hconn
  · -- If S has size at most two but not exactly two, its size is at most one.
    by_contra hSne
    have hScard : S.card ≤ 1 := by omega
    have hTcard : (preimageFinset u v S).card ≤ 2 := by
      calc (preimageFinset u v S).card
          ≤ S.card + 1 := preimageFinset_card_le u v huv S
        _ ≤ 1 + 1 := Nat.add_le_add_right hScard 1
        _ = 2 := by ring
    have hconn := hvc.2 (preimageFinset u v S) (by omega)
    exact hGsep hconn

/-! ### Extracting a separator witness in G

The contraction separator consists of the contracted class and one other
class. Choose a representative `z` of the latter; then `z ≠ u,v` and
`{u,v,z}` separates `G`. -/

/-- For a 3-connected `G`, a separator of size at most two in `G/uv` yields
a vertex `z ≠ u,v` such that `G - {u,v,z}` is disconnected.
Choose the second quotient class and one of its representatives. The inverse
image of the two classes is exactly `{u,v,z}`, so separator lifting applies. -/
theorem exists_witness_separator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : u ≠ v)
    (h3 : G.IsKConnected 3)
    (S : Finset (ContrVertex u v))
    (hSize : S.card ≤ 2)
    (hSep : ¬ ((contrGraph G u v).induce
      ((↑S : Set (ContrVertex u v)))ᶜ).Connected) :
    ∃ z : V, z ≠ u ∧ z ≠ v ∧
      ¬ (G.induce ((↑({u, v, z} : Finset V) : Set V))ᶜ).Connected := by
  classical
  haveI : Nontrivial V := ⟨u, v, huv⟩
  obtain ⟨huInS, hScard⟩ := contrSeparator_must_contain_class G huv h3 S hSize hSep
  -- Choose the second element of S.
  -- There is a class Cz in S different from the contracted class.
  have hexCz : ∃ Cz ∈ S, Cz ≠ contrMk u v u := by
    -- Removing the contracted class from S leaves one element.
    have h1 : (S.erase (contrMk u v u)).card = 1 := by
      rw [Finset.card_erase_of_mem huInS, hScard]
    have h1ne : (S.erase (contrMk u v u)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨Cz, hCz⟩ := h1ne
    rw [Finset.mem_erase] at hCz
    exact ⟨Cz, hCz.2, hCz.1⟩
  obtain ⟨Cz, hCzInS, hCzNeU⟩ := hexCz
  -- Use surjectivity of the quotient map to choose z representing Cz.
  obtain ⟨z, hzEq⟩ := contrMk_surjective u v Cz
  -- If z = u, its class would be the contracted class, a contradiction.
  have hzNeU : z ≠ u := by
    intro hzu; subst hzu
    exact hCzNeU hzEq.symm
  -- If z = v, the same contradiction follows from [v] = [u].
  have hzNeV : z ≠ v := by
    intro hzv; subst hzv
    apply hCzNeU
    rw [← hzEq, contrMk_eq]
  refine ⟨z, hzNeU, hzNeV, ?_⟩
  -- Show that {u,v,z} separates G.
  -- The inverse image of S separates G because S separates the contraction.
  have hGsep_set : ¬ (G.induce
      ((contrMk u v ⁻¹' (↑S : Set (ContrVertex u v)))ᶜ : Set V)).Connected :=
    induce_disconnected_of_contrGraph_induce_disconnected G u v _ hSep
  -- Identify the set-theoretic inverse image with {u,v,z}.
  have hpreSet : (contrMk u v ⁻¹' (↑S : Set (ContrVertex u v)) : Set V) =
      ((↑({u, v, z} : Finset V) : Set V)) := by
    ext w
    constructor
    · intro hw
      -- Membership in S gives either the contracted class or the class of z.
      simp only [Set.mem_preimage, Finset.mem_coe] at hw
      have : contrMk u v w = contrMk u v u ∨ contrMk u v w = Cz := by
        -- Express S as the pair of its two distinct known elements.
        -- Prove S = {contrMk u v u, Cz}.
        have hS_eq : S = ({contrMk u v u, Cz} : Finset _) := by
          have hsub₁ : ({contrMk u v u, Cz} : Finset _) ⊆ S := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact huInS
            · exact hCzInS
          have hcard₁ : ({contrMk u v u, Cz} : Finset _).card = 2 := by
            rw [Finset.card_insert_of_notMem (by
              simp [Finset.mem_singleton, Ne.symm hCzNeU]),
              Finset.card_singleton]
          exact (Finset.eq_of_subset_of_card_le hsub₁ (by rw [hcard₁, hScard])).symm
        rw [hS_eq] at hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        exact hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rcases this with h1 | h2
      · -- [w] = [u] → w = u ∨ w = v.
        rw [contrMk_eq_u_iff] at h1
        rcases h1 with rfl | rfl
        · left; rfl
        · right; left; rfl
      · -- The class of z has the unique representative z because z differs from u,v.
        rw [← hzEq] at h2
        rw [contrMk_preimage_singleton u v hzNeU hzNeV] at h2
        right; right; exact h2
    · intro hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      simp only [Set.mem_preimage, Finset.mem_coe]
      rcases hw with hwu | hwv | hwz
      · rw [hwu]; exact huInS
      · -- w = v: [v] = [u] ∈ S.
        rw [hwv]
        have : contrMk u v v = contrMk u v u := (contrMk_eq u v).symm
        rw [this]; exact huInS
      · rw [hwz, hzEq]; exact hCzInS
  rw [hpreSet] at hGsep_set
  exact hGsep_set

end ContrThreeConnected

/-! ### Degree bounds in a 3-connected graph

The degree lower bound supplies neighbors outside any separator of size
at most three. -/

section DegreeKConnected

variable [Fintype V] [DecidableEq V]

/-- Every vertex of a k-connected graph has degree at least k.
Use Whitney's inequalities `κ(G) ≤ δ(G) ≤ deg(v)`. -/
theorem isKConnected_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nontrivial V] {k : ℕ} (h : G.IsKConnected k) (v : V) :
    k ≤ G.degree v := by
  have h1 : k ≤ G.minDegree := le_trans h (vertexConnectivity_le_minDegree G)
  exact le_trans h1 (G.minDegree_le_degree v)

/-- A vertex in a set `T` of at most three vertices has a neighbor outside
`T` in a 3-connected graph. Its degree is at least three, whereas `T` contains
at most two other vertices. The size restriction on `T` is essential. -/
theorem exists_neighbor_outside_separator
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (h3 : G.IsKConnected 3)
    {T : Finset V} (hTcard : T.card ≤ 3)
    {t : V} (htInT : t ∈ T) :
    ∃ w : V, w ∉ T ∧ G.Adj t w := by
  classical
  -- The vertex t has at least three neighbors.
  have hdeg : 3 ≤ G.degree t := isKConnected_le_degree G h3 t
  -- The finset G.neighborFinset t consists of the neighbors of t.
  -- Its cardinality is G.degree t.
  have hcard : 3 ≤ (G.neighborFinset t).card := by
    rw [G.card_neighborFinset_eq_degree]; exact hdeg
  -- Find a neighbor of t outside T.
  by_contra hAll
  -- hAll: ¬ ∃ w, w ∉ T ∧ G.Adj t w → ∀ w, w ∉ T → ¬ G.Adj t w.
  have hAll' : ∀ w, w ∉ T → ¬ G.Adj t w := by
    intro w hw hadj; exact hAll ⟨w, hw, hadj⟩
  -- The contrary assumption puts every neighbor of t in T.
  -- Thus neighborFinset t is a subset of T.
  have hsub : G.neighborFinset t ⊆ T := by
    intro w hw
    rw [G.mem_neighborFinset] at hw
    by_contra hwt
    exact hAll' w hwt hw
  -- Looplessness excludes t itself, so the neighbors lie in T.erase t.
  have hsub' : G.neighborFinset t ⊆ T.erase t := by
    intro w hw
    rw [Finset.mem_erase]
    refine ⟨?_, hsub hw⟩
    rw [G.mem_neighborFinset] at hw
    intro hwt; subst hwt; exact G.irrefl hw
  -- But T.erase t has at most two vertices, contradicting the degree bound.
  have herase_card : (T.erase t).card ≤ 2 := by
    rw [Finset.card_erase_of_mem htInT]
    omega
  have : (G.neighborFinset t).card ≤ 2 :=
    le_trans (Finset.card_le_card hsub') herase_card
  omega

end DegreeKConnected

/-! ### Extracting a separator from failure of 3-connectivity

A graph with at least four vertices that is not 3-connected has a separator
of size at most two. Apply this to a non-3-connected edge contraction. -/

section ExtractSeparator

variable [Fintype V] [DecidableEq V]

/-- A graph with at least four vertices that is not 3-connected admits a
set `S` of size at most two whose deletion is disconnected.
Otherwise all deletions of fewer than three vertices would be connected,
giving `IsVertexConnected 3` and hence contradicting the connectivity bound. -/
theorem not_isKConnected_three_extract
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (h : ¬ G.IsKConnected 3) :
    ∃ S : Finset V, S.card ≤ 2 ∧
      ¬ (G.induce ((↑S : Set V))ᶜ).Connected := by
  classical
  haveI : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    omega
  -- ¬ IsKConnected 3 = ¬ (3 ≤ vertexConnectivity G).
  unfold IsKConnected at h
  -- Failure of 3 ≤ vertexConnectivity gives vertexConnectivity < 3.
  have hlt : G.vertexConnectivity < 3 := Nat.lt_of_not_le h
  -- Use the specification of vertexConnectivity.
  -- Show that IsVertexConnected 3 cannot hold.
  by_contra hAll
  -- hAll : ¬ ∃ S, S.card ≤ 2 ∧ ¬ Connected
  -- The absence of a small separator would establish IsVertexConnected 3.
  have h3vc : G.IsVertexConnected 3 := by
    refine ⟨by omega, fun S hS => ?_⟩
    by_contra hC
    apply hAll
    refine ⟨S, by omega, ?_⟩
    -- Convert deletion by a finset complement to deletion by a set complement.
    rwa [← set_compl_finset_eq_univ_sdiff] at hC
  -- This contradicts the assumed upper bound on vertexConnectivity.
  have h3le : 3 ≤ G.vertexConnectivity :=
    le_vertexConnectivity_of_isVertexConnected G h3vc
  omega

end ExtractSeparator

/-! ### Vertex counts in a 3-connected graph

A 3-connected graph has at least four vertices. On exactly four vertices,
the degree lower bound forces the complete graph `K4`. Consequently a
3-connected graph not isomorphic to `K4` has at least five vertices, leaving
vertices outside a separator triple. -/

section CardKConnected

variable [Fintype V] [DecidableEq V]

/-- A 3-connected graph has at least four vertices.
The definition of vertex connectivity bounds it by `|V| - 1`, which combines
with the lower bound three. -/
theorem isKConnected_three_card_ge_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsKConnected 3) :
    4 ≤ Fintype.card V := by
  classical
  by_contra hc
  -- The contrary assumption gives fewer than four vertices.
  have hc : Fintype.card V < 4 := Nat.lt_of_not_le hc
  unfold IsKConnected at h
  unfold vertexConnectivity at h
  -- h : 3 ≤ sSup {k | IsVertexConnected k}
  rcases (Set.eq_empty_or_nonempty {k : Nat | G.IsVertexConnected k}) with hempty | hne
  · -- The supremum of the empty set is zero, contradicting the lower bound three.
    rw [hempty] at h; simp at h
  · -- For a nonempty set, each connectivity value is at most |V| - 1.
    have hsup : sSup {k : Nat | G.IsVertexConnected k} ≤ Fintype.card V - 1 := by
      apply csSup_le hne
      intro b ⟨hb, _⟩
      omega
    omega

/-- A 3-connected graph on four vertices is isomorphic to `K4`.
Every degree is at least three and at most `|V| - 1 = 3`, so the graph is
complete. A vertex equivalence with `Fin 4` gives the required isomorphism. -/
theorem isKConnected_three_card_eq_four_iff_K4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsKConnected 3) (hcard : Fintype.card V = 4) :
    Nonempty (G ≃g (⊤ : SimpleGraph (Fin 4))) := by
  classical
  haveI : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial]; omega
  -- Every vertex has degree exactly three.
  have hdeg_ge : ∀ v : V, 3 ≤ G.degree v :=
    fun v => isKConnected_le_degree G h3 v
  have hdeg_le : ∀ v : V, G.degree v ≤ 3 := by
    intro v
    have := G.degree_lt_card_verts v
    omega
  have hdeg_eq : ∀ v : V, G.degree v = 3 :=
    fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  -- Show G is the complete graph.
  have hGeq : G = (⊤ : SimpleGraph V) := by
    ext a b
    simp only [SimpleGraph.top_adj]
    refine ⟨fun hab => G.ne_of_adj hab, fun hab => ?_⟩
    -- Use neighborFinset a = univ.erase a to establish adjacency.
    have hcardN : (G.neighborFinset a).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, hdeg_eq]
    have hsub : G.neighborFinset a ⊆ Finset.univ.erase a := by
      intro w hw
      rw [Finset.mem_erase, G.mem_neighborFinset] at *
      exact ⟨(G.ne_of_adj hw).symm, Finset.mem_univ _⟩
    have hcardE : (Finset.univ.erase a : Finset V).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      omega
    have heq : G.neighborFinset a = Finset.univ.erase a :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← G.mem_neighborFinset, heq, Finset.mem_erase]
    exact ⟨hab.symm, Finset.mem_univ _⟩
  -- A vertex equivalence with Fin 4 induces an isomorphism of complete graphs.
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  have iso_top : (⊤ : SimpleGraph V) ≃g (⊤ : SimpleGraph (Fin 4)) := by
    rw [show (⊤ : SimpleGraph V) = SimpleGraph.completeGraph V from
          (SimpleGraph.completeGraph_eq_top V).symm,
        show (⊤ : SimpleGraph (Fin 4)) = SimpleGraph.completeGraph (Fin 4) from
          (SimpleGraph.completeGraph_eq_top (Fin 4)).symm]
    exact SimpleGraph.Iso.completeGraph e
  exact ⟨hGeq ▸ iso_top⟩

/-- A 3-connected graph not isomorphic to `K4` has at least five vertices.
There are at least four by connectivity, and equality would force `K4`.
This supplies vertices outside the separator triples used below. -/
theorem isKConnected_three_not_K4_card_ge_five
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsKConnected 3)
    (hnK4 : ¬ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 4)))) :
    5 ≤ Fintype.card V := by
  have h4 : 4 ≤ Fintype.card V := isKConnected_three_card_ge_four G h3
  rcases Nat.lt_or_ge 4 (Fintype.card V) with hgt | hle
  · omega
  · -- Four vertices would imply G is isomorphic to K4, contradicting hnK4.
    exfalso
    apply hnK4
    exact isKConnected_three_card_eq_four_iff_K4 G h3 (le_antisymm hle h4)

end CardKConnected

/-! ### Components of induced subgraphs

For a separator `T` and `a ∉ T`, `componentOf G T a ha` represents the
component of `a` in `G - T` as a set of original vertices.
`componentFinsetOf` and `componentSize` provide its finite representation
and cardinality, used in the minimum-component argument. -/

section ComponentInfra

variable [Fintype V] [DecidableEq V]

/-- The component containing `a` in `G - T`, represented as a subset of
the original vertex type. -/
noncomputable def componentOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) : Set V :=
  ((G.induce ((↑T : Set V))ᶜ).connectedComponentMk
    ⟨a, by simp [ha]⟩).supp.image Subtype.val

/-- The component as a finset of original vertices. -/
noncomputable def componentFinsetOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) : Finset V := by
  classical
  exact (componentOf G T a ha).toFinset

/-- The size of the component containing `a` in `G - T`. -/
noncomputable def componentSize (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) : ℕ :=
  (componentFinsetOf G T a ha).card

/-- A vertex belongs to its own component. -/
theorem mem_componentOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) :
    a ∈ componentOf G T a ha := by
  unfold componentOf
  simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff,
    Subtype.exists]
  refine ⟨a, by simp [ha], ?_, rfl⟩
  rfl

/-- The component contains no vertex of T. -/
theorem componentOf_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) :
    ∀ w ∈ componentOf G T a ha, w ∉ T := by
  intro w hw hwT
  unfold componentOf at hw
  simp only [Set.mem_image, Subtype.exists] at hw
  obtain ⟨w', hw', _, hweq⟩ := hw
  -- The subtype representative certifies that w is outside T.
  subst hweq
  simp only [Set.mem_compl_iff, Finset.mem_coe] at hw'
  exact hw' hwT

/-- The component is nonempty because it contains a. -/
theorem componentOf_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) :
    (componentOf G T a ha).Nonempty :=
  ⟨a, mem_componentOf G T a ha⟩

/-- The component size is positive because it contains a. -/
theorem componentSize_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) :
    0 < componentSize G T a ha := by
  classical
  unfold componentSize componentFinsetOf
  rw [Finset.card_pos]
  have hne : (componentOf G T a ha).Nonempty := componentOf_nonempty G T a ha
  rw [Set.toFinset_nonempty]
  exact hne

/-- The component is contained in the complement of T. -/
theorem componentOf_subset_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (a : V) (ha : a ∉ T) :
    componentOf G T a ha ⊆ ((↑T : Set V))ᶜ := by
  intro w hw
  simp only [Set.mem_compl_iff, Finset.mem_coe]
  exact componentOf_disjoint G T a ha w hw

end ComponentInfra

/-! ### Disconnectedness and minimum witnesses

Equality of components is characterized by reachability. Disconnectedness
provides vertices in different components, and each such component is a
proper subset of the remaining vertices. These facts support minimizing
`componentSize G {x,y,z} a` over separator witnesses. -/

section ComponentSplit

variable [Fintype V] [DecidableEq V]

/-- Two vertices outside `T` have the same component exactly when they
are reachable in `G - T`. -/
theorem componentOf_eq_iff_reachable (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) {a b : V} (ha : a ∉ T) (hb : b ∉ T) :
    componentOf G T a ha = componentOf G T b hb ↔
    (G.induce ((↑T : Set V))ᶜ).Reachable
      ⟨a, by simp [ha]⟩ ⟨b, by simp [hb]⟩ := by
  classical
  constructor
  · intro hEq
    -- componentOf a = componentOf b → b ∈ componentOf a → reachable.
    have hb_in_a : b ∈ componentOf G T a ha := by
      rw [hEq]; exact mem_componentOf G T b hb
    unfold componentOf at hb_in_a
    simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff,
      Subtype.exists] at hb_in_a
    obtain ⟨b', hb', hReach, hbeq⟩ := hb_in_a
    -- hReach : connectedComponentMk ⟨b', hb'⟩ = connectedComponentMk ⟨a, _⟩
    -- hbeq : b' = b
    subst hbeq
    have hReach' := SimpleGraph.ConnectedComponent.exact hReach
    exact hReach'.symm
  · intro hR
    -- Reachability identifies the connected components and their represented sets.
    have heq : (G.induce ((↑T : Set V))ᶜ).connectedComponentMk ⟨a, by simp [ha]⟩ =
        (G.induce ((↑T : Set V))ᶜ).connectedComponentMk ⟨b, by simp [hb]⟩ :=
      SimpleGraph.ConnectedComponent.sound hR
    unfold componentOf
    rw [heq]

/-- If `b` belongs to the component of `a`, then their represented
components are equal. -/
theorem componentOf_eq_of_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) {a b : V} (ha : a ∉ T) (hb : b ∉ T)
    (hba : b ∈ componentOf G T a ha) :
    componentOf G T b hb = componentOf G T a ha := by
  classical
  rw [componentOf_eq_iff_reachable]
  -- Membership in the component of a gives reachability from a.
  unfold componentOf at hba
  simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff,
    Subtype.exists] at hba
  obtain ⟨b', hb', hReach, hbeq⟩ := hba
  subst hbeq
  exact SimpleGraph.ConnectedComponent.exact hReach

/-- If `G - T` is disconnected and at least two vertices remain, choose
vertices `a,b ∉ T` with `b` outside the component of `a`. -/
theorem disconnected_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hcompl : 2 ≤ (Finset.univ \ T).card)
    (hSep : ¬ (G.induce ((↑T : Set V))ᶜ).Connected) :
    ∃ a : V, ∃ ha : a ∉ T, ∃ b : V, ∃ hb : b ∉ T,
      b ∉ componentOf G T a ha := by
  classical
  -- At least two remaining vertices imply a nonempty complement.
  have hne_compl : (Finset.univ \ T).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨a, ha_in⟩ := hne_compl
  rw [Finset.mem_sdiff] at ha_in
  obtain ⟨_, ha⟩ := ha_in
  refine ⟨a, ha, ?_⟩
  -- Find a vertex outside T and outside the component of a.
  -- Disconnectedness means that not every remaining vertex is reachable from a.
  -- First obtain nonemptiness of the remaining subtype.
  haveI : Nonempty (((↑T : Set V))ᶜ : Set V) := by
    refine ⟨⟨a, ?_⟩⟩; simp [ha]
  -- Since the subtype is nonempty, failure of Connected implies failure of Preconnected.
  have hNotPre : ¬ (G.induce ((↑T : Set V))ᶜ).Preconnected := by
    intro hPre
    apply hSep
    exact ⟨hPre⟩
  -- Failure of Preconnected gives two vertices that are not mutually reachable.
  unfold SimpleGraph.Preconnected at hNotPre
  push_neg at hNotPre
  obtain ⟨u, v, huv⟩ := hNotPre
  -- Split on whether a is reachable from u.
  -- Reachability from a to both u and v would connect u and v.
  -- Hence at least one of u,v is not reachable from a.
  -- If a reaches u, it cannot also reach v.
  -- Otherwise u itself is not reachable from a.
  by_cases hau : (G.induce ((↑T : Set V))ᶜ).Reachable ⟨a, by simp [ha]⟩ u
  · -- Reaching both u and v would contradict their separation.
    have hav : ¬ (G.induce ((↑T : Set V))ᶜ).Reachable ⟨a, by simp [ha]⟩ v := by
      intro hav
      exact huv (hau.symm.trans hav)
    -- The subtype membership ensures v.val is outside T.
    have hv_not : v.val ∉ T := by
      have hp := v.property
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hp
      exact hp
    refine ⟨v.val, hv_not, ?_⟩
    -- Show v.val is outside the component of a.
    intro hmem
    apply hav
    -- Use the equivalence between component equality and reachability.
    have hReach := (componentOf_eq_iff_reachable G T ha hv_not).mp
      (componentOf_eq_of_mem G T ha hv_not hmem).symm
    -- hReach : Reachable ⟨a,_⟩ ⟨v.val, _⟩
    -- Identify the endpoint subtype in the reachability statement.
    have : (⟨v.val, by simp [hv_not]⟩ : (((↑T : Set V))ᶜ : Set V)) = v := by
      apply Subtype.ext; rfl
    rw [this] at hReach
    exact hReach
  · -- ¬ Reachable a u.
    have hu_not : u.val ∉ T := by
      have hp := u.property
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hp
      exact hp
    refine ⟨u.val, hu_not, ?_⟩
    intro hmem
    apply hau
    have hReach := (componentOf_eq_iff_reachable G T ha hu_not).mp
      (componentOf_eq_of_mem G T ha hu_not hmem).symm
    have : (⟨u.val, by simp [hu_not]⟩ : (((↑T : Set V))ᶜ : Set V)) = u := by
      apply Subtype.ext; rfl
    rw [this] at hReach
    exact hReach

/-- A component is a proper subset of the vertices outside `T` when another
remaining vertex `b` lies outside it. In particular its size is at most
`|V \ T| - 1`. -/
theorem componentSize_lt_compl_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) {a : V} (ha : a ∉ T) {b : V} (hb : b ∉ T)
    (hbnotin : b ∉ componentOf G T a ha) :
    componentSize G T a ha ≤ (Finset.univ \ T).card - 1 := by
  classical
  unfold componentSize componentFinsetOf
  -- (componentOf G T a ha).toFinset ⊆ (Finset.univ \ T).erase b.
  have hsub : (componentOf G T a ha).toFinset ⊆ (Finset.univ \ T).erase b := by
    intro w hw
    rw [Set.mem_toFinset] at hw
    rw [Finset.mem_erase, Finset.mem_sdiff]
    refine ⟨?_, Finset.mem_univ _, componentOf_disjoint G T a ha w hw⟩
    intro hwb; subst hwb; exact hbnotin hw
  have hcard_le : ((componentOf G T a ha).toFinset).card ≤
      ((Finset.univ \ T).erase b).card :=
    Finset.card_le_card hsub
  -- ((Finset.univ \ T).erase b).card = (Finset.univ \ T).card - 1.
  have hb_in : b ∈ Finset.univ \ T := by
    rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hb⟩
  rw [Finset.card_erase_of_mem hb_in] at hcard_le
  exact hcard_le

end ComponentSplit

/-! ### Minimum-component argument for Diestel Lemma 3.2.1

Assume every edge contraction fails to be 3-connected. Each edge then has
a separator witness triple. Choose a witness triple and one component of
its complement with minimum size. The third separator vertex has a neighbor
in that component. Contracting this new edge yields another separator triple;
a suitable component of its complement lies strictly inside the first one,
contradicting minimality. The supporting lemmas and the final construction
are given below. -/

section MinWitness

variable [Fintype V] [DecidableEq V]

/-- A valid quadruple `(x,y,z,a)` consists of an edge `xy`, a third vertex
`z ≠ x,y` such that `{x,y,z}` separates `G`, and a vertex `a` outside that triple. -/
def IsValidWitness (G : SimpleGraph V) [DecidableRel G.Adj] (q : V × V × V × V) : Prop :=
  G.Adj q.1 q.2.1 ∧ q.2.2.1 ∉ ({q.1, q.2.1} : Finset V) ∧
  q.2.2.2 ∉ ({q.1, q.2.1, q.2.2.1} : Finset V) ∧
  ¬ (G.induce ((↑({q.1, q.2.1, q.2.2.1} : Finset V) : Set V))ᶜ).Connected

/-- The witness cost is the component size for a valid quadruple and
`|V| + 1` otherwise. This definition uses classical decidability. -/
noncomputable def witnessCost (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : V × V × V × V) : ℕ := by
  classical
  exact if h : IsValidWitness G q then
    componentSize G ({q.1, q.2.1, q.2.2.1} : Finset V) q.2.2.2 h.2.2.1
  else
    Fintype.card V + 1

/-- For a valid quadruple, `witnessCost` equals the specified component size. -/
theorem witnessCost_of_valid (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : V × V × V × V) (h : IsValidWitness G q) :
    witnessCost G q =
      componentSize G ({q.1, q.2.1, q.2.2.1} : Finset V) q.2.2.2 h.2.2.1 := by
  classical
  unfold witnessCost
  rw [dif_pos h]

/-- For an invalid quadruple, `witnessCost` is `|V| + 1`. -/
theorem witnessCost_of_invalid (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : V × V × V × V) (h : ¬ IsValidWitness G q) :
    witnessCost G q = Fintype.card V + 1 := by
  classical
  unfold witnessCost
  rw [dif_neg h]

/-- If a valid quadruple exists, a minimum-cost quadruple exists in the
finite universe. Its cost is below `|V| + 1`, so the minimizer is also valid. -/
theorem exists_min_validWitness (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hex : ∃ q : V × V × V × V, IsValidWitness G q) :
    ∃ q : V × V × V × V, IsValidWitness G q ∧
      ∀ q' : V × V × V × V, IsValidWitness G q' → witnessCost G q ≤ witnessCost G q' := by
  classical
  -- The finite universe is nonempty because V is nonempty.
  have hUniv_ne : (Finset.univ : Finset (V × V × V × V)).Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨(v, v, v, v), Finset.mem_univ _⟩
  obtain ⟨qmin, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (V × V × V × V)) (witnessCost G) hUniv_ne
  -- hmin : ∀ q' ∈ Finset.univ, witnessCost G qmin ≤ witnessCost G q'
  -- Show the minimizing quadruple is valid.
  -- Compare its cost with the cost of a known valid quadruple.
  obtain ⟨q0, hq0_valid⟩ := hex
  have hqmin_le : witnessCost G qmin ≤ witnessCost G q0 := hmin q0 (Finset.mem_univ _)
  rw [witnessCost_of_valid G q0 hq0_valid] at hqmin_le
  -- Every represented component has size at most |V|.
  have hSize_le : componentSize G ({q0.1, q0.2.1, q0.2.2.1} : Finset V) q0.2.2.2 hq0_valid.2.2.1
      ≤ Fintype.card V := by
    unfold componentSize componentFinsetOf
    calc ((componentOf G _ _ _).toFinset).card
        ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  have hqmin_lt : witnessCost G qmin < Fintype.card V + 1 := by omega
  -- An invalid minimizer would have cost |V| + 1, contradicting this bound.
  have hqmin_valid : IsValidWitness G qmin := by
    by_contra hnv
    rw [witnessCost_of_invalid G qmin hnv] at hqmin_lt
    omega
  refine ⟨qmin, hqmin_valid, ?_⟩
  intro q' hq'_valid
  exact hmin q' (Finset.mem_univ _)

end MinWitness

/-! ### Component lemmas for the final contradiction

First, adjacency within an induced component identifies the endpoint components. -/

section ComponentAdj

variable [Fintype V] [DecidableEq V]

/-- An edge of `G - T` connects vertices in the same component. -/
theorem componentOf_eq_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) {a b : V} (ha : a ∉ T) (hb : b ∉ T)
    (hadj : G.Adj a b) :
    componentOf G T a ha = componentOf G T b hb := by
  classical
  rw [componentOf_eq_iff_reachable]
  -- Construct reachability in the induced complement of T.
  -- The original edge remains in the induced graph because both endpoints avoid T.
  apply SimpleGraph.Adj.reachable
  exact hadj

/-- A neighbor outside `T` of a vertex outside `T` belongs to the same
component of `G - T`. -/
theorem mem_componentOf_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) {a b : V} (ha : a ∉ T) (hb : b ∉ T)
    (hadj : G.Adj a b) :
    b ∈ componentOf G T a ha := by
  classical
  have heq := componentOf_eq_of_adj G T hb ha hadj.symm
  rw [← heq]
  exact mem_componentOf G T b hb

end ComponentAdj

/-! ### A separator vertex has a neighbor in a complementary component

Let `T = {x,y,z}` and let `C` be a component of `G - T`. By 3-connectivity,
`G - {x,y}` is connected. A walk from a vertex of `C` to `z` has a first edge
leaving `C`. Its endpoint outside `C` cannot avoid `T`, since adjacency would
then keep it in the same component of `G - T`. It also avoids `x,y`, so it
must be `z`. Thus `z` has a neighbor in `C`. -/

section NeighborInComponent

variable [Fintype V] [DecidableEq V]

/-- A walk in `G - {x,y}` starting in a set `C` and ending outside `C`
has an edge leaving `C`; its outside endpoint still avoids `x,y`.
The proof is by induction on the walk. -/
theorem exists_exit_edge_along_walk
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V)
    (C : Set V) :
    ∀ {a' b' : (((↑({x, y} : Finset V) : Set V))ᶜ : Set V)}
      (_p : (G.induce (((↑({x, y} : Finset V) : Set V))ᶜ : Set V)).Walk a' b')
      (_ha'C : (a' : V) ∈ C) (_hb'C : (b' : V) ∉ C),
      ∃ u w : V, G.Adj u w ∧ u ∈ C ∧ w ∉ C ∧
        w ∉ ({x, y} : Finset V) := by
  intro a' b' p
  induction p with
  | nil =>
    intro ha'C hb'C
    exact (hb'C ha'C).elim
  | @cons a'' c'' b'' hadj p' ih =>
    intro ha''C hb''C
    -- The first induced edge gives an edge in G.
    have hadjG : G.Adj a''.val c''.val := by
      rw [induce_adj] at hadj; exact hadj
    -- Subtype membership ensures the next vertex avoids x,y.
    have hc''_not_xy : c''.val ∉ ({x, y} : Finset V) := by
      have hp := c''.property
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hp
      exact hp
    by_cases hcC : (c'' : V) ∈ C
    · -- If the next vertex lies in C, apply induction to the remaining walk.
      exact ih hcC hb''C
    · -- Otherwise the first edge already leaves C.
      exact ⟨a''.val, c''.val, hadjG, ha''C, hcC, hc''_not_xy⟩

/-- For a 3-connected graph, let `T = {x,y,z}` with `x ≠ y` and `z ∉ {x,y}`.
Every component of `G - T` contains a neighbor of `z`.

The role of `z` as the third separator vertex is explicit. Connectedness of
`G - {x,y}` supplies a walk to `z`; the first edge leaving the chosen component
must end at `z`, since any endpoint outside `T` would remain in that component. -/
theorem each_separator_vertex_has_neighbor_in_C
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsKConnected 3)
    {x y z a : V} (hxy : x ≠ y) (hzxy : z ∉ ({x, y} : Finset V))
    (ha : a ∉ ({x, y, z} : Finset V))
    (hSep : ¬ (G.induce ((↑({x, y, z} : Finset V) : Set V))ᶜ).Connected) :
    ∃ v : V, v ∈ componentOf G ({x, y, z} : Finset V) a ha ∧ G.Adj z v := by
  classical
  haveI : Nontrivial V := ⟨x, y, hxy⟩
  -- Record membership of z in T and its distinctness from x,y.
  have hzT : z ∈ ({x, y, z} : Finset V) := by simp
  have hzx : z ≠ x := by
    intro hzx; subst hzx; exact hzxy (by simp)
  have hzy : z ≠ y := by
    intro hzy; subst hzy; exact hzxy (by simp)
  -- Let C be the component of a in G - T.
  set T : Finset V := ({x, y, z} : Finset V) with hT_def
  set C : Set V := componentOf G T a ha with hC_def
  -- The starting vertex a belongs to C.
  have haC : a ∈ C := mem_componentOf G T a ha
  -- The vertex z does not belong to C because z lies in T.
  have hzNotC : z ∉ C := by
    intro hzC; exact componentOf_disjoint G T a ha z hzC hzT
  -- Deleting x,y preserves connectedness by 3-connectivity.
  have hvc : G.IsVertexConnected 3 := h3.isVertexConnected
  have hxy_card : ({x, y} : Finset V).card < 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    omega
  have hConn := hvc.2 ({x, y} : Finset V) hxy_card
  -- Convert the finset deletion to the set complement.
  have hConn' : (G.induce ((↑({x, y} : Finset V) : Set V))ᶜ).Connected := by
    rw [set_compl_finset_eq_univ_sdiff]; exact hConn
  -- Both a and z avoid x,y.
  have ha_xy : a ∉ ({x, y} : Finset V) := by
    intro h
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    apply ha
    rcases h with rfl | rfl
    · rw [hT_def]; simp
    · rw [hT_def]; simp
  have hz_xy : z ∉ ({x, y} : Finset V) := hzxy
  -- Obtain reachability from a to z in G - {x,y}.
  have ha_set : a ∈ ((↑({x, y} : Finset V) : Set V))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at ha_xy
    exact ha_xy
  have hz_set : z ∈ ((↑({x, y} : Finset V) : Set V))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hzx, hzy⟩
  have hReach := hConn'.preconnected ⟨a, ha_set⟩ ⟨z, hz_set⟩
  obtain ⟨p⟩ := hReach
  -- Choose the first edge of this walk leaving C.
  obtain ⟨u, w, hadj, huC, hwNotC, hw_not_xy⟩ :=
    exists_exit_edge_along_walk G x y C p haC hzNotC
  -- Split on whether its outside endpoint w belongs to T.
  by_cases hwT : w ∈ T
  · -- If w lies in T but avoids x,y, then w = z.
    have hwz : w = z := by
      simp [hT_def, Finset.mem_insert, Finset.mem_singleton] at hwT
      rcases hwT with rfl | rfl | h
      · exact (hw_not_xy (by simp)).elim
      · exact (hw_not_xy (by simp)).elim
      · exact h
    subst hwz
    refine ⟨u, huC, hadj.symm⟩
  · -- If w avoids T, its adjacency to u keeps it in the component of u in G - T.
    -- Since u lies in C, it avoids T.
    have huNotT : u ∉ T := componentOf_disjoint G T a ha u huC
    -- The component of u equals the component of a, namely C.
    have hCuEq : componentOf G T u huNotT = C := by
      rw [hC_def]
      exact componentOf_eq_of_mem G T ha huNotT huC
    -- The edge from u to w puts w in that same component.
    have hwInCu : w ∈ componentOf G T u huNotT :=
      mem_componentOf_of_adj G T huNotT hwT hadj
    rw [hCuEq] at hwInCu
    exact (hwNotC hwInCu).elim

end NeighborInComponent

/-! ### Component inclusion when a component avoids another separator

Let `D` be a component of `G - T2` disjoint from `T1`. Every walk within `D`
also avoids `T1`. If `D` meets a component `C` of `G - T1`, reachability therefore
gives `D ⊆ C`. In the final argument, a vertex of `C ∩ T2` witnesses that this
inclusion is strict. -/

section ComponentSubset

variable [Fintype V] [DecidableEq V]

/-- For vertices `b,c ∉ T`, membership of `c` in the component of `b`
is equivalent to reachability from `b` to `c` in `G - T`. -/
theorem mem_componentOf_iff_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) {b c : V} (hb : b ∉ T) (hc : c ∉ T) :
    c ∈ componentOf G T b hb ↔
    (G.induce ((↑T : Set V))ᶜ).Reachable
      ⟨b, by simp [hb]⟩ ⟨c, by simp [hc]⟩ := by
  classical
  constructor
  · intro hmem
    -- Membership identifies the two represented components.
    -- Hence b and c are reachable.
    have hcb := componentOf_eq_of_mem G T hb hc hmem
    -- hcb : componentOf G T c hc = componentOf G T b hb
    -- The goal is reachability between the specified subtype endpoints.
    rw [componentOf_eq_iff_reachable] at hcb
    exact hcb.symm
  · intro hR
    -- Reachability identifies the components and gives the required membership.
    have hEq : componentOf G T b hb = componentOf G T c hc :=
      (componentOf_eq_iff_reachable G T hb hc).mpr hR
    rw [hEq]
    exact mem_componentOf G T c hc

/-- For sets `T1,T2`, suppose the component `D` of `d` in `G - T2`
avoids `T1` and contains a vertex in the component `C` of `a` in `G - T1`.
Then `D ⊆ C`: walks within `D` avoid `T1` and hence also lie in `G - T1`.
This is the component-inclusion step in Diestel's argument, p. 46. -/
theorem componentOf_subset_componentOf_of_disjoint_T1
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 : Finset V) {a d : V}
    (ha : a ∉ T1) (hd2 : d ∉ T2)
    (hD_disj_T1 : ∀ x ∈ componentOf G T2 d hd2, x ∉ T1)
    (hd_in_C : d ∈ componentOf G T1 a ha) :
    componentOf G T2 d hd2 ⊆ componentOf G T1 a ha := by
  classical
  -- The vertex d avoids T1 because d belongs to D and D avoids T1.
  have hd1 : d ∉ T1 := hD_disj_T1 d (mem_componentOf G T2 d hd2)
  -- The components of d and a in G - T1 agree because d lies in C.
  have hCd_eq : componentOf G T1 d hd1 = componentOf G T1 a ha :=
    componentOf_eq_of_mem G T1 ha hd1 hd_in_C
  intro c hc
  -- c ∈ D = componentOf G T2 d
  -- Show c belongs to the component of a, equivalently the component of d.
  rw [← hCd_eq]
  -- The vertex c avoids T1 because D avoids T1.
  have hc1 : c ∉ T1 := hD_disj_T1 c hc
  -- The vertex c avoids T2 because it belongs to a component of G - T2.
  have hc2 : c ∉ T2 := componentOf_disjoint G T2 d hd2 c hc
  -- Regard d as a vertex of the induced complement of T2.
  have hd_set2 : d ∈ ((↑T2 : Set V))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.mem_coe]; exact hd2
  -- Regard c as a vertex of the induced complement of T2.
  have hc_set2 : c ∈ ((↑T2 : Set V))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.mem_coe]; exact hc2
  -- Component membership supplies a walk from d to c in G - T2.
  have hReach2 : (G.induce ((↑T2 : Set V))ᶜ).Reachable
      ⟨d, hd_set2⟩ ⟨c, hc_set2⟩ :=
    (mem_componentOf_iff_reachable G T2 hd2 hc2).mp hc
  -- Both endpoints also lie in the complement of T1.
  have hd_set1 : d ∈ ((↑T1 : Set V))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.mem_coe]; exact hd1
  have hc_set1 : c ∈ ((↑T1 : Set V))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.mem_coe]; exact hc1
  -- Show c belongs to the component of d in G - T1.
  -- It suffices to establish reachability in the induced complement of T1.
  suffices hReach1 : (G.induce ((↑T1 : Set V))ᶜ).Reachable
      ⟨d, hd_set1⟩ ⟨c, hc_set1⟩ from
    (mem_componentOf_iff_reachable G T1 hd1 hc1).mpr hReach1
  -- Extract a walk Q' in the induced complement of T2.
  refine hReach2.elim (fun Q' => ?_)
  -- Q' : (G.induce (↑T2)ᶜ).Walk ⟨d, _⟩ ⟨c, _⟩
  -- Map Q' into G using Embedding.induce.
  set Q : G.Walk d c := Q'.map (Embedding.induce ((↑T2 : Set V))ᶜ).toHom
  -- Show every vertex in Q.support avoids T1.
  -- First show each vertex of the walk belongs to the component D.
  -- The entire induced walk lies in the component of d in G - T2.
  have hQ_supp : ∀ x ∈ Q.support, x ∈ componentOf G T2 d hd2 := by
    intro x hx
    -- Use Walk.support_map to identify the support of the mapped walk.
    have hsupp_eq : Q.support = List.map Subtype.val Q'.support := by
      have := SimpleGraph.Walk.support_map
        (Embedding.induce ((↑T2 : Set V))ᶜ).toHom Q'
      simpa using this
    rw [hsupp_eq] at hx
    rw [List.mem_map] at hx
    obtain ⟨⟨x', hx'⟩, hx'_in, hx'_eq⟩ := hx
    -- hx' : x' ∈ ((↑T2)ᶜ : Set V), hx'_eq : x' = x
    subst hx'_eq
    -- Show the intermediate vertex belongs to the component of d.
    -- Every vertex on the walk from d to c belongs to that component.
    -- The prefix given by takeUntil witnesses reachability from d.
    have hx'_notT2 : x' ∉ T2 := by
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hx'
      exact hx'
    -- Establish component membership of the intermediate vertex.
    -- Use takeUntil for reachability in the induced complement of T2.
    have hReachDx : (G.induce ((↑T2 : Set V))ᶜ).Reachable
        ⟨d, hd_set2⟩ ⟨x', hx'⟩ :=
      ⟨Q'.takeUntil ⟨x', hx'⟩ hx'_in⟩
    exact (mem_componentOf_iff_reachable G T2 hd2 hx'_notT2).mpr hReachDx
  -- Thus every vertex in Q.support avoids T1.
  have hQ_avoidT1 : ∀ x ∈ Q.support, x ∈ ((↑T1 : Set V))ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Finset.mem_coe]
    exact hD_disj_T1 x (hQ_supp x hx)
  -- Walk.induce now gives a walk in the induced complement of T1.
  refine ⟨SimpleGraph.Walk.induce _ Q hQ_avoidT1⟩

/-- If the first component `C` also contains a vertex `v ∈ T2`, then
`componentSize G T2 d < componentSize G T1 a`. The component inclusion gives
`D ⊆ C`, and `v ∈ C \ D` makes it strict. -/
theorem componentSize_lt_of_disjoint_T1_and_witness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T1 T2 : Finset V) {a d : V}
    (ha : a ∉ T1) (hd2 : d ∉ T2)
    (hD_disj_T1 : ∀ x ∈ componentOf G T2 d hd2, x ∉ T1)
    (hd_in_C : d ∈ componentOf G T1 a ha)
    {v : V} (hv_in_C : v ∈ componentOf G T1 a ha) (hv_T2 : v ∈ T2) :
    componentSize G T2 d hd2 < componentSize G T1 a ha := by
  classical
  -- Use the component inclusion D ⊆ C.
  have hsub : componentOf G T2 d hd2 ⊆ componentOf G T1 a ha :=
    componentOf_subset_componentOf_of_disjoint_T1 G T1 T2 ha hd2 hD_disj_T1 hd_in_C
  -- The vertex v is outside D because v belongs to T2.
  have hv_notD : v ∉ componentOf G T2 d hd2 := by
    intro hvD
    exact componentOf_disjoint G T2 d hd2 v hvD hv_T2
  -- The finset inclusion is strict, witnessed by v in C but outside D.
  -- Prove strict inclusion of the represented component finsets.
  have hsub_fin : (componentOf G T2 d hd2).toFinset ⊆
      (componentOf G T1 a ha).toFinset := by
    intro x hx
    rw [Set.mem_toFinset] at hx ⊢
    exact hsub hx
  -- The vertex v belongs to the first component finset but not the second.
  have hv_in_finC : v ∈ (componentOf G T1 a ha).toFinset := by
    rw [Set.mem_toFinset]; exact hv_in_C
  have hv_notin_finD : v ∉ (componentOf G T2 d hd2).toFinset := by
    rw [Set.mem_toFinset]; exact hv_notD
  -- Strict inclusion → strict cardinality.
  have hssub : (componentOf G T2 d hd2).toFinset ⊂
      (componentOf G T1 a ha).toFinset :=
    (Finset.ssubset_iff_of_subset hsub_fin).mpr ⟨v, hv_in_finC, hv_notin_finD⟩
  -- Unfold componentSize to identify the relevant finset cardinalities.
  change (componentFinsetOf G T2 d hd2).card < (componentFinsetOf G T1 a ha).card
  unfold componentFinsetOf
  exact Finset.card_lt_card hssub

end ComponentSubset

/-! ### Contractible-edge theorem (Diestel Lemma 3.2.1)

Every 3-connected graph not isomorphic to `K4` has an edge whose contraction
is 3-connected. Assume otherwise and choose a valid quadruple `(x,y,z,a)`
with minimum complementary component `C`.

The vertex `z` has a neighbor `v ∈ C`. The assumed failure of 3-connectivity
for the contraction of `zv` yields another separator `T2 = {z,v,w}`. Choose
`s ∈ {x,y}` outside `T2`. Any other element of `{x,y}` outside `T2` remains
adjacent to `s`, so both lie in its component of `G - T2`. A different
component `D` therefore avoids `{x,y,z}`.

Apply the separator-neighbor lemma to obtain a neighbor `d ∈ D` of `v`.
Because `D` avoids the first separator, this edge also puts `d` in `C`.
The component-inclusion lemma gives `D ⊆ C`; the vertex `v ∈ C ∩ T2`
makes the inclusion strict. The quadruple for `T2,D` then contradicts
minimality of the original component. -/

section MainTheorem

variable [Fintype V] [DecidableEq V]

/-- Classical decidable equality on contraction classes, needed by the
finite-set formulation of vertex connectivity. -/
noncomputable instance instDecidableEqContrVertex (u v : V) :
    DecidableEq (ContrVertex u v) :=
  Classical.decEq _

/-- Classical decidable adjacency on the contracted graph, needed to
state its vertex connectivity. -/
noncomputable instance instDecidableRelContrGraphAdj
    (G : SimpleGraph V) (u v : V) :
    DecidableRel (contrGraph G u v).Adj :=
  Classical.decRel _

/-- If `G - T` is disconnected and `s ∉ T`, some remaining vertex `b`
lies outside the component of `s`. -/
theorem disconnected_split_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) {s : V} (hs : s ∉ T)
    (hSep : ¬ (G.induce ((↑T : Set V))ᶜ).Connected) :
    ∃ b : V, ∃ hb : b ∉ T, b ∉ componentOf G T s hs := by
  classical
  -- Treat s as a vertex of the complement of T.
  haveI : Nonempty (((↑T : Set V))ᶜ : Set V) := ⟨⟨s, by simp [hs]⟩⟩
  -- Nonemptiness turns failure of Connected into failure of Preconnected.
  have hNotPre : ¬ (G.induce ((↑T : Set V))ᶜ).Preconnected := by
    intro hPre
    apply hSep
    exact ⟨hPre⟩
  -- Failure of Preconnected gives two vertices that are not reachable.
  unfold SimpleGraph.Preconnected at hNotPre
  push_neg at hNotPre
  obtain ⟨u, v, huv⟩ := hNotPre
  -- Split on whether s reaches u.
  by_cases hsu : (G.induce ((↑T : Set V))ᶜ).Reachable
      ⟨s, by simp [hs]⟩ u
  · -- If s reaches u, it cannot also reach v.
    have hsv : ¬ (G.induce ((↑T : Set V))ᶜ).Reachable
        ⟨s, by simp [hs]⟩ v := by
      intro hsv
      exact huv (hsu.symm.trans hsv)
    have hv_not : v.val ∉ T := by
      have hp := v.property
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hp
      exact hp
    refine ⟨v.val, hv_not, ?_⟩
    intro hmem
    apply hsv
    have hReach := (componentOf_eq_iff_reachable G T hs hv_not).mp
      (componentOf_eq_of_mem G T hs hv_not hmem).symm
    have heq : (⟨v.val, by simp [hv_not]⟩ : (((↑T : Set V))ᶜ : Set V)) = v := by
      apply Subtype.ext; rfl
    rw [heq] at hReach
    exact hReach
  · -- ¬ Reachable s u.
    have hu_not : u.val ∉ T := by
      have hp := u.property
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hp
      exact hp
    refine ⟨u.val, hu_not, ?_⟩
    intro hmem
    apply hsu
    have hReach := (componentOf_eq_iff_reachable G T hs hu_not).mp
      (componentOf_eq_of_mem G T hs hu_not hmem).symm
    have heq : (⟨u.val, by simp [hu_not]⟩ : (((↑T : Set V))ᶜ : Set V)) = u := by
      apply Subtype.ext; rfl
    rw [heq] at hReach
    exact hReach

/-- **Diestel Lemma 3.2.1:** every 3-connected graph not isomorphic to `K4`
has an edge whose contraction remains 3-connected.
The minimum-component argument is described above. -/
theorem IsKConnected.three_exists_contractible_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsKConnected 3)
    (hne : ¬ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 4)))) :
    ∃ u v : V, ∃ _huv : G.Adj u v,
      (contrGraph G u v).IsKConnected 3 := by
  classical
  -- Connectivity and exclusion of K4 give at least five vertices.
  have hV5 : 5 ≤ Fintype.card V :=
    isKConnected_three_not_K4_card_ge_five G h3 hne
  haveI hntV : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial]; omega
  haveI hneV : Nonempty V := hntV.to_nonempty
  -- Assume every edge contraction fails to be 3-connected.
  by_contra hAll
  push_neg at hAll
  -- The contracted vertex count is |V| - 1, hence at least four.
  have hContrCard : ∀ x y : V, x ≠ y →
      4 ≤ Fintype.card (ContrVertex x y) := fun x y hxy => by
    rw [contrVertex_card_eq hxy]; omega
  -- For every edge xy, obtain a third vertex t making {x,y,t} a separator.
  have hWitness : ∀ x y : V, G.Adj x y →
      ∃ t : V, t ≠ x ∧ t ≠ y ∧
        ¬ (G.induce ((↑({x, y, t} : Finset V) : Set V))ᶜ).Connected := by
    intro x y hxy
    have hxny : x ≠ y := G.ne_of_adj hxy
    have hNot : ¬ (contrGraph G x y).IsKConnected 3 := hAll x y hxy
    have hCardC := hContrCard x y hxny
    obtain ⟨S, hScard, hSep⟩ :=
      not_isKConnected_three_extract (contrGraph G x y) hCardC hNot
    exact exists_witness_separator G hxny h3 S hScard hSep
  -- Construct an initial valid quadruple.
  -- Choose an initial vertex a0.
  obtain ⟨a0⟩ : Nonempty V := hneV
  -- Its positive degree supplies a neighbor.
  have hdeg0 : 3 ≤ G.degree a0 := isKConnected_le_degree G h3 a0
  have hNeNbr : (G.neighborFinset a0).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]; omega
  obtain ⟨b0, hb0_mem⟩ := hNeNbr
  rw [G.mem_neighborFinset] at hb0_mem
  have hadj0 : G.Adj a0 b0 := hb0_mem
  have hab0 : a0 ≠ b0 := G.ne_of_adj hadj0
  -- Use the edge a0–b0 and its separator witness c0.
  obtain ⟨c0, hc0a, hc0b, hSep0⟩ := hWitness a0 b0 hadj0
  -- The separator has three vertices, leaving at least two vertices outside it.
  have hac0 : a0 ≠ c0 := fun h => hc0a h.symm
  have hbc0 : b0 ≠ c0 := fun h => hc0b h.symm
  have hT0_card : ({a0, b0, c0} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem
        (by simp [hab0, hac0]),
      Finset.card_insert_of_notMem
        (by simp [hbc0]),
      Finset.card_singleton]
  have hCompl0 : 2 ≤ (Finset.univ \ ({a0, b0, c0} : Finset V)).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hT0_card]
    omega
  obtain ⟨d0, hd0_notT, _, _, _⟩ :=
    disconnected_split G ({a0, b0, c0} : Finset V) hCompl0 hSep0
  -- The quadruple (a0,b0,c0,d0) is valid.
  have hValid0 : IsValidWitness G (a0, b0, c0, d0) := by
    refine ⟨hadj0, ?_, hd0_notT, hSep0⟩
    -- c0 ∉ {a0, b0}.
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨fun h => hac0 h.symm, fun h => hbc0 h.symm⟩
  -- Choose a minimum-cost valid quadruple.
  obtain ⟨q, hq_valid, hq_min⟩ :=
    exists_min_validWitness G ⟨_, hValid0⟩
  -- Unpack the quadruple into (a1,b1,c1,d1).
  obtain ⟨a1, b1, c1, d1⟩ := q
  obtain ⟨hAdj1, hSep_witness, hD_notT, hSepRaw⟩ := hq_valid
  -- Record the edge a1–b1 and the distinct separator witness c1.
  -- Refer to the unpacked tuple from this point onward.
  change G.Adj a1 b1 at hAdj1
  change c1 ∉ ({a1, b1} : Finset V) at hSep_witness
  change d1 ∉ ({a1, b1, c1} : Finset V) at hD_notT
  change ¬ (G.induce ((↑({a1, b1, c1} : Finset V) : Set V))ᶜ).Connected at hSepRaw
  -- T1 = {a1, b1, c1}.
  -- The separator-neighbor lemma gives a neighbor v of c1 in C1.
  have hab1 : a1 ≠ b1 := G.ne_of_adj hAdj1
  obtain ⟨v, hv_C1, hcv_adj⟩ :=
    each_separator_vertex_has_neighbor_in_C G h3 hab1 hSep_witness hD_notT hSepRaw
  -- v ∉ T1.
  have hv_notT1 : v ∉ ({a1, b1, c1} : Finset V) :=
    componentOf_disjoint G _ d1 hD_notT v hv_C1
  have hv_ne_a1 : v ≠ a1 := by intro h; subst h; exact hv_notT1 (by simp)
  have hv_ne_b1 : v ≠ b1 := by intro h; subst h; exact hv_notT1 (by simp)
  have hv_ne_c1 : v ≠ c1 := by intro h; subst h; exact hv_notT1 (by simp)
  have hc1_ne_v : c1 ≠ v := fun h => hv_ne_c1 h.symm
  -- Apply the contrary assumption to the edge c1–v.
  obtain ⟨w, hw_c1, hw_v, hSep2⟩ := hWitness c1 v hcv_adj
  -- The vertices a1,b1 differ from c1 and v.
  have ha1_ne_c1 : a1 ≠ c1 := by
    intro h
    have : c1 ∈ ({a1, b1} : Finset V) := by rw [← h]; simp
    exact hSep_witness this
  have hb1_ne_c1 : b1 ≠ c1 := by
    intro h
    have : c1 ∈ ({a1, b1} : Finset V) := by rw [← h]; simp
    exact hSep_witness this
  have ha1_ne_v : a1 ≠ v := fun h => hv_ne_a1 h.symm
  have hb1_ne_v : b1 ≠ v := fun h => hv_ne_b1 h.symm
  -- Choose s in {a1,b1} outside T2 = {c1,v,w}.
  have hexS : ∃ s : V, ∃ other : V,
      ({s, other} : Finset V) = ({a1, b1} : Finset V) ∧
      s ∉ ({c1, v, w} : Finset V) ∧ G.Adj s other := by
    by_cases haw : a1 = w
    · -- If a1 = w, choose s = b1 and other = a1.
      refine ⟨b1, a1, ?_, ?_, hAdj1.symm⟩
      · ext z; simp; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        refine ⟨hb1_ne_c1, hb1_ne_v, ?_⟩
        intro h
        -- If b1 also equaled w, then a1 = b1, a contradiction.
        have : a1 = b1 := haw.trans h.symm
        exact hab1 this
    · -- If a1 ≠ w, choose s = a1 and other = b1.
      refine ⟨a1, b1, by rfl, ?_, hAdj1⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨ha1_ne_c1, ha1_ne_v, haw⟩
  obtain ⟨s, other, hso_eq, hs_notT2, hs_other_adj⟩ := hexS
  -- Choose b outside T2 and outside the component of s.
  obtain ⟨b, hb_notT2, hb_notComp_s⟩ :=
    disconnected_split_at G ({c1, v, w} : Finset V) hs_notT2 hSep2
  -- 8. other ∉ componentOf G T2 b.
  have hOther_notD : other ∉ componentOf G ({c1, v, w} : Finset V) b hb_notT2 := by
    intro h_other_D
    have h_other_notT2 : other ∉ ({c1, v, w} : Finset V) :=
      componentOf_disjoint G _ b hb_notT2 other h_other_D
    -- Membership would identify the components of b and other.
    have h_b_other_eq :
        componentOf G ({c1, v, w} : Finset V) other h_other_notT2 =
        componentOf G ({c1, v, w} : Finset V) b hb_notT2 :=
      componentOf_eq_of_mem G _ hb_notT2 h_other_notT2 h_other_D
    -- The edge from s to other identifies their components.
    have h_s_other_eq :
        componentOf G ({c1, v, w} : Finset V) s hs_notT2 =
        componentOf G ({c1, v, w} : Finset V) other h_other_notT2 :=
      componentOf_eq_of_adj G _ hs_notT2 h_other_notT2 hs_other_adj
    -- componentOf b = componentOf s.
    have h_b_s_eq :
        componentOf G ({c1, v, w} : Finset V) b hb_notT2 =
        componentOf G ({c1, v, w} : Finset V) s hs_notT2 := by
      rw [← h_b_other_eq, ← h_s_other_eq]
    -- This puts b in the component of s, contradicting its choice.
    have hb_in_comp : b ∈ componentOf G ({c1, v, w} : Finset V) b hb_notT2 :=
      mem_componentOf G _ b hb_notT2
    rw [h_b_s_eq] at hb_in_comp
    exact hb_notComp_s hb_in_comp
  -- s ∉ componentOf b.
  have hs_notD : s ∉ componentOf G ({c1, v, w} : Finset V) b hb_notT2 := by
    intro hs_D
    -- Membership would identify the components of b and s.
    have h_b_s_eq :
        componentOf G ({c1, v, w} : Finset V) s hs_notT2 =
        componentOf G ({c1, v, w} : Finset V) b hb_notT2 :=
      componentOf_eq_of_mem G _ hb_notT2 hs_notT2 hs_D
    have hb_in_comp : b ∈ componentOf G ({c1, v, w} : Finset V) b hb_notT2 :=
      mem_componentOf G _ b hb_notT2
    rw [← h_b_s_eq] at hb_in_comp
    exact hb_notComp_s hb_in_comp
  -- Neither a1 nor b1 belongs to D, since they are s and other.
  have ha1_notD : a1 ∉ componentOf G ({c1, v, w} : Finset V) b hb_notT2 := by
    have ha1_in_so : a1 ∈ ({s, other} : Finset V) := by rw [hso_eq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha1_in_so
    rcases ha1_in_so with rfl | rfl
    · exact hs_notD
    · exact hOther_notD
  have hb1_notD : b1 ∉ componentOf G ({c1, v, w} : Finset V) b hb_notT2 := by
    have hb1_in_so : b1 ∈ ({s, other} : Finset V) := by rw [hso_eq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb1_in_so
    rcases hb1_in_so with rfl | rfl
    · exact hs_notD
    · exact hOther_notD
  -- 9. D ∩ T1 = ∅.
  -- The vertex c1 is outside D because c1 belongs to T2.
  have hc1_notD : c1 ∉ componentOf G ({c1, v, w} : Finset V) b hb_notT2 := by
    intro hc1D
    have hc1_in_T2 : c1 ∈ ({c1, v, w} : Finset V) := by simp
    exact componentOf_disjoint G _ b hb_notT2 c1 hc1D hc1_in_T2
  have hD_disj_T1 : ∀ x ∈ componentOf G ({c1, v, w} : Finset V) b hb_notT2,
      x ∉ ({a1, b1, c1} : Finset V) := by
    intro x hxD hxT1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT1
    rcases hxT1 with rfl | rfl | rfl
    · exact ha1_notD hxD
    · exact hb1_notD hxD
    · exact hc1_notD hxD
  -- Apply the separator-neighbor lemma with v as the third separator vertex.
  -- The lemma requires a triple {x,y,z} with z outside {x,y}.
  -- Use x = c1, y = w, z = v, then permute the separator triple.
  have hT2_perm : ({c1, v, w} : Finset V) = ({c1, w, v} : Finset V) := by
    ext z; simp; tauto
  have hc1_ne_w : c1 ≠ w := fun h => hw_c1 h.symm
  have hv_notin_c1w : v ∉ ({c1, w} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hv_ne_c1, fun h => hw_v h.symm⟩
  have hb_not_T2_perm : b ∉ ({c1, w, v} : Finset V) := by
    rw [← hT2_perm]; exact hb_notT2
  have hSep2_perm : ¬ (G.induce ((↑({c1, w, v} : Finset V) : Set V))ᶜ).Connected := by
    rw [← hT2_perm]; exact hSep2
  obtain ⟨d, hd_inComp_perm, hvd_adj⟩ :=
    each_separator_vertex_has_neighbor_in_C G h3 hc1_ne_w hv_notin_c1w
      hb_not_T2_perm hSep2_perm
  -- hd_inComp_perm : d ∈ componentOf G {c1, w, v} b _.
  have hd_notT2_perm : d ∉ ({c1, w, v} : Finset V) :=
    componentOf_disjoint G _ b hb_not_T2_perm d hd_inComp_perm
  have hd_notT2 : d ∉ ({c1, v, w} : Finset V) := by
    rw [hT2_perm]; exact hd_notT2_perm
  -- Transfer the component membership to the original ordering of T2.
  have hd_inD : d ∈ componentOf G ({c1, v, w} : Finset V) b hb_notT2 := by
    -- Use the reachability characterization of component membership.
    -- The induced complements agree because the two separator sets are equal.
    rw [mem_componentOf_iff_reachable G _ hb_notT2 hd_notT2]
    rw [mem_componentOf_iff_reachable G _ hb_not_T2_perm hd_notT2_perm]
      at hd_inComp_perm
    -- Identify the two separator sets.
    have hSet_eq : ((↑({c1, v, w} : Finset V) : Set V))ᶜ =
        ((↑({c1, w, v} : Finset V) : Set V))ᶜ := by rw [hT2_perm]
    -- Transport reachability across the equality of the induced complements.
    -- Use convert to align the types.
    convert hd_inComp_perm using 4 <;> rw [hT2_perm]
  -- 11. d ∉ T1.
  have hd_notT1 : d ∉ ({a1, b1, c1} : Finset V) := hD_disj_T1 d hd_inD
  -- 12. d ∈ C1.
  have hd_inC1 : d ∈ componentOf G ({a1, b1, c1} : Finset V) d1 hD_notT := by
    have heqV : componentOf G ({a1, b1, c1} : Finset V) v hv_notT1 =
        componentOf G ({a1, b1, c1} : Finset V) d1 hD_notT :=
      componentOf_eq_of_mem G _ hD_notT hv_notT1 hv_C1
    rw [← heqV]
    -- The edge d–v places d in the component of v in G - T1.
    have hdv_adj : G.Adj d v := hvd_adj.symm
    exact mem_componentOf_of_adj G _ hv_notT1 hd_notT1 hdv_adj.symm
  -- 13. v ∈ T2.
  have hv_T2 : v ∈ ({c1, v, w} : Finset V) := by simp
  -- The strict component-inclusion lemma gives |D| < |C1|.
  -- The strict-inclusion lemma requires a component representative
  -- that also lies in C1. The vertex d belongs to both D and C1.
  -- Thus d can replace b as the representative of the same component D.
  have hCompEq :
      componentOf G ({c1, v, w} : Finset V) d hd_notT2 =
      componentOf G ({c1, v, w} : Finset V) b hb_notT2 :=
    componentOf_eq_of_mem G _ hb_notT2 hd_notT2 hd_inD
  have hD_disj_T1_d : ∀ x ∈ componentOf G ({c1, v, w} : Finset V) d hd_notT2,
      x ∉ ({a1, b1, c1} : Finset V) := by
    intro x hxD; rw [hCompEq] at hxD; exact hD_disj_T1 x hxD
  have hSize_lt_d :
      componentSize G ({c1, v, w} : Finset V) d hd_notT2 <
      componentSize G ({a1, b1, c1} : Finset V) d1 hD_notT :=
    componentSize_lt_of_disjoint_T1_and_witness G
      ({a1, b1, c1} : Finset V) ({c1, v, w} : Finset V)
      hD_notT hd_notT2 hD_disj_T1_d hd_inC1 hv_C1 hv_T2
  -- Equal represented components have equal component sizes.
  have hSize_eq :
      componentSize G ({c1, v, w} : Finset V) d hd_notT2 =
      componentSize G ({c1, v, w} : Finset V) b hb_notT2 := by
    unfold componentSize componentFinsetOf
    rw [hCompEq]
  have hSize_lt :
      componentSize G ({c1, v, w} : Finset V) b hb_notT2 <
      componentSize G ({a1, b1, c1} : Finset V) d1 hD_notT := by
    rw [← hSize_eq]; exact hSize_lt_d
  -- The valid quadruple (c1,v,w,b) has smaller cost than (a1,b1,c1,d1).
  have hValidNew : IsValidWitness G (c1, v, w, b) := by
    refine ⟨hcv_adj, ?_, hb_notT2, hSep2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hw_c1, hw_v⟩
  have hCost_new : witnessCost G (c1, v, w, b) =
      componentSize G ({c1, v, w} : Finset V) b hValidNew.2.2.1 :=
    witnessCost_of_valid G _ hValidNew
  -- Evaluate the cost of the original quadruple (a1,b1,c1,d1).
  have hValidOld : IsValidWitness G (a1, b1, c1, d1) :=
    ⟨hAdj1, hSep_witness, hD_notT, hSepRaw⟩
  have hCost_old : witnessCost G (a1, b1, c1, d1) =
      componentSize G ({a1, b1, c1} : Finset V) d1 hValidOld.2.2.1 :=
    witnessCost_of_valid G _ hValidOld
  have hLt' : witnessCost G (c1, v, w, b) < witnessCost G (a1, b1, c1, d1) := by
    rw [hCost_new, hCost_old]
    exact hSize_lt
  exact absurd (hq_min (c1, v, w, b) hValidNew) (by omega)

end MainTheorem

end EdgeContraction

end SimpleGraph
