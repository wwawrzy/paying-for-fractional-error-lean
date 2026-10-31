/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Planar.Basic
import GraphTheory.SimpleGraph.Planar.RotationSystem
import GraphTheory.SimpleGraph.Block.TwoConnected
import GraphTheory.SimpleGraph.BlockTree.Formula
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic

/-!
# Planar girth density bound (Diestel Corollary 4.2.10)

For a connected, non-acyclic planar graph with girth at least `g ≥ 3`:

    |E| · (g - 2) ≤ g · (|V| - 2)

The proof assembles Diestel's block decomposition (§3.1, §4.2). A 2-connected
block satisfies the bound through an Euler rotation system with cyclic faces.
Bridge blocks are handled separately; their contribution is absorbed using
the block-tree identity `Σ_v cutVertexMultiplicity = |blocks| - 1` and the
existence of a nontrivial block in a non-acyclic graph.

The predicate `HasMinGirth` and the explicit topological axiom
`hasPlanarRotationSystem` are defined here so that the density theorem and
its girth consequences have no circular imports. The axiom supplies the
planar rotation system and cyclic faces; its topological proof is not
formalized in this package.

The dependencies of `edgeFinset_card_girth_bound` include
`propext`, `Classical.choice`, `Quot.sound`, and
`IsPlanar.hasPlanarRotationSystem`. The combinatorial density inequality
itself is proved rather than postulated.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}

/-! ### Girth predicate -/

/-- `HasMinGirth G g` means the shortest cycle in `G` has length at least `g`.
Equivalently, `G` contains no cycle of length less than `g`.

Defined as `(g : ℕ∞) ≤ G.egirth` using Mathlib's extended girth. -/
def HasMinGirth (G : SimpleGraph V) (g : Nat) : Prop :=
  @LE.le ENat _ (g : ENat) G.egirth

/-- Girth is monotone downward: if `G` has girth at least `g` and `g' ≤ g`,
then `G` has girth at least `g'`. -/
theorem HasMinGirth.mono {G : SimpleGraph V} {g g' : Nat}
    (h : G.HasMinGirth g) (hle : g' ≤ g) : G.HasMinGirth g' := by
  unfold HasMinGirth at *
  exact le_trans (Nat.cast_le.mpr hle) h

/-- Girth is inherited by induced subgraphs: removing vertices cannot
create shorter cycles. -/
theorem HasMinGirth.induce {G : SimpleGraph V} {g : Nat}
    (h : G.HasMinGirth g) (s : Set V) : (G.induce s).HasMinGirth g := by
  unfold HasMinGirth at *
  rw [le_egirth] at h
  rw [le_egirth]
  intro a w hw
  let f : (G.induce s).Hom G := {
    toFun := fun x => x.val
    map_rel' := fun {a b} hab => by
      rw [SimpleGraph.induce, SimpleGraph.comap_adj] at hab
      exact hab
  }
  have hinj : Function.Injective f := Subtype.val_injective
  have hw' : (w.map f).IsCycle := hw.map hinj
  have hlen := h _ (w.map f) hw'
  rw [Walk.length_map] at hlen
  exact hlen

/-! ### Explicit planar rotation-system axiom (Diestel Proposition 4.2.5) -/

/-- **Explicit topological axiom:** every **2-connected** planar graph admits
a rotation system satisfying Euler's formula (`IsPlanarEmbedding`) and having
cyclic face boundaries (`HasCyclicFaces`).

Diestel Proposition 4.2.5 states that every face of a 2-connected plane graph
is bounded by a cycle. The 2-connectedness hypothesis (`IsKConnected 2`) is
essential: a face incident with a bridge need not be bounded by a cycle.

A full proof requires planar embedding topology and the Heffter-Edmonds theorem;
that proof is outside the scope of this formalization. This declaration remains
an axiom, rather than a proved topological bridge. -/
axiom IsPlanar.hasPlanarRotationSystem {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hplanar : IsPlanar G) (h2conn : G.IsKConnected 2) :
    ∃ (r : G.RotationSystem),
      r.IsPlanarEmbedding ∧ r.HasCyclicFaces

/-! ### Private bounds for individual blocks -/

section Bricks

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  [Fintype G.edgeSet]

/-- The girth-dependent bound for a 2-connected block, using `hasPlanarRotationSystem`. -/
private theorem aux_two_conn_girth_bound [inst : Fintype G.edgeSet]
    {g : ℕ} (hplanar : IsPlanar G) (hgirth : G.HasMinGirth g)
    (h2conn : G.IsKConnected 2) (hg : 3 ≤ g) (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card * (g - 2) ≤ g * (Fintype.card V - 2) := by
  have hinst : inst = G.fintypeEdgeSet := Subsingleton.elim _ _
  subst hinst
  obtain ⟨r, hPE, hCF⟩ := hplanar.hasPlanarRotationSystem h2conn
  have hmg : MinGirth G g := by
    have h := hgirth
    unfold HasMinGirth at h
    rw [le_egirth] at h
    intro u p hp
    have h2 := h u p hp
    exact_mod_cast h2
  exact r.edge_bound_from_euler_girth hPE g hmg hg hCF hcard

open Classical in
/-- Map an edge `e ∈ edgesInBlock b` to an edge of the induced graph `G.induce V_b`. -/
private noncomputable def aux_toInduce (b : G.Block)
    (e : Sym2 V) (he : e ∈ G.edgesInBlock b) :
    Sym2 (↑(↑(G.blockVertices b) : Set V)) :=
  e.attachWith (P := fun v => v ∈ (↑(G.blockVertices b) : Set V)) (by
    intro v hv
    change v ∈ G.blockVertices b
    rw [G.mem_blockVertices_iff]
    exact ⟨e, he, hv⟩)

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
private theorem aux_toInduce_map_subtypeVal (b : G.Block)
    (e : Sym2 V) (he : e ∈ G.edgesInBlock b) :
    Sym2.map (Subtype.val : ↑(↑(G.blockVertices b) : Set V) → V)
        (G.aux_toInduce b e he) = e := by
  unfold aux_toInduce
  exact Sym2.attachWith_map_subtypeVal _

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
private theorem aux_toInduce_injective (b : G.Block) :
    ∀ {e₁ e₂ : Sym2 V} (h₁ : e₁ ∈ G.edgesInBlock b) (h₂ : e₂ ∈ G.edgesInBlock b),
      G.aux_toInduce b e₁ h₁ = G.aux_toInduce b e₂ h₂ → e₁ = e₂ := by
  intro e₁ e₂ h₁ h₂ heq
  have hmap₁ := G.aux_toInduce_map_subtypeVal b e₁ h₁
  have hmap₂ := G.aux_toInduce_map_subtypeVal b e₂ h₂
  rw [← hmap₁, ← hmap₂, heq]

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
private theorem aux_toInduce_isEdge (b : G.Block)
    (e : Sym2 V) (he : e ∈ G.edgesInBlock b) :
    G.aux_toInduce b e he ∈
      (G.induce (↑(G.blockVertices b) : Set V)).edgeSet := by
  have he_G : e ∈ G.edgeSet := by
    have hsub : G.edgesInBlock b ⊆ G.edgeFinset := by
      unfold edgesInBlock
      exact Finset.filter_subset _ _
    have : e ∈ G.edgeFinset := hsub he
    rw [← mem_edgeFinset]; exact this
  induction e with
  | h u v =>
    rw [mem_edgeSet] at he_G
    change s(_, _) ∈ (G.induce (↑(G.blockVertices b) : Set V)).edgeSet
    rw [mem_edgeSet, induce_adj]
    exact he_G

/-- The girth-dependent edge bound for a nontrivial block (at least three
vertices). Its only additional axiom is `hasPlanarRotationSystem`. -/
private theorem aux_edgesInBlock_girth_bound
    {g : ℕ} (hplanar : G.IsPlanar) (hgirth : G.HasMinGirth g) (b : G.Block)
    (hg : 3 ≤ g) (hntriv : 3 ≤ (G.blockVertices b).card) :
    (G.edgesInBlock b).card * (g - 2) ≤ g * ((G.blockVertices b).card - 2) := by
  classical
  have hH : (G.induce (↑(G.blockVertices b) : Set V)).IsPlanar := hplanar.induce _
  have hHg : (G.induce (↑(G.blockVertices b) : Set V)).HasMinGirth g :=
    hgirth.induce _
  have hcard_eq :
      Fintype.card (↑(↑(G.blockVertices b) : Set V)) = (G.blockVertices b).card := by
    convert Fintype.card_coe (G.blockVertices b) using 1
  have hcard3 : 3 ≤ Fintype.card (↑(↑(G.blockVertices b) : Set V)) := hcard_eq ▸ hntriv
  have h2conn : (G.induce (↑(G.blockVertices b) : Set V)).IsKConnected 2 :=
    G.induce_blockVertices_isKConnected_two b hntriv
  have hH_bound :
      (G.induce (↑(G.blockVertices b) : Set V)).edgeFinset.card * (g - 2) ≤
        g * (Fintype.card (↑(↑(G.blockVertices b) : Set V)) - 2) :=
    aux_two_conn_girth_bound _ hH hHg h2conn hg hcard3
  haveI : Nonempty (Sym2 (↑(↑(G.blockVertices b) : Set V))) := by
    rcases Finset.card_pos.mp (by omega : 0 < (G.blockVertices b).card) with ⟨v, hv⟩
    have hv' : v ∈ (↑(G.blockVertices b) : Set V) := hv
    exact ⟨s(⟨v, hv'⟩, ⟨v, hv'⟩)⟩
  have hcard_inj :
      (G.edgesInBlock b).card ≤
        (G.induce (↑(G.blockVertices b) : Set V)).edgeFinset.card := by
    refine Finset.card_le_card_of_injOn
      (fun e =>
        if h : e ∈ G.edgesInBlock b then
          G.aux_toInduce b e h
        else
          Classical.arbitrary _) ?mapsTo ?injOn
    case mapsTo =>
      intro e he
      beta_reduce
      rw [show (if h : e ∈ G.edgesInBlock b then
          G.aux_toInduce b e h
        else Classical.arbitrary _) = G.aux_toInduce b e he from
        dif_pos he, Finset.mem_coe, mem_edgeFinset]
      exact G.aux_toInduce_isEdge b e he
    case injOn =>
      intro e₁ h₁ e₂ h₂ heq
      beta_reduce at heq
      rw [show (if h : e₁ ∈ G.edgesInBlock b then
          G.aux_toInduce b e₁ h
        else Classical.arbitrary _) = G.aux_toInduce b e₁ h₁ from
        dif_pos h₁,
        show (if h : e₂ ∈ G.edgesInBlock b then
          G.aux_toInduce b e₂ h
        else Classical.arbitrary _) = G.aux_toInduce b e₂ h₂ from
        dif_pos h₂] at heq
      exact G.aux_toInduce_injective b h₁ h₂ heq
  calc (G.edgesInBlock b).card * (g - 2)
      ≤ (G.induce (↑(G.blockVertices b) : Set V)).edgeFinset.card * (g - 2) := by
        gcongr
    _ ≤ g * (Fintype.card (↑(↑(G.blockVertices b) : Set V)) - 2) := hH_bound
    _ = g * ((G.blockVertices b).card - 2) := by rw [hcard_eq]

open Classical in
omit [DecidableRel G.Adj] in
/-- `nontrivBlockVertices = univ` for a connected graph with at least two vertices. -/
private theorem aux_nontriv_eq_univ
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V) :
    G.nontrivBlockVertices = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  intro v
  unfold nontrivBlockVertices
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨u, huv⟩ : ∃ u, G.Adj v u := by
    have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨w, hw⟩ : ∃ w : V, w ≠ v := by
      obtain ⟨a, b, hab⟩ := hnt
      rcases eq_or_ne a v with rfl | ha
      · exact ⟨b, hab.symm⟩
      · exact ⟨a, ha⟩
    obtain ⟨p⟩ := hconn.preconnected v w
    have hnnil : ¬ p.Nil := fun hnil => hw hnil.eq.symm
    rw [SimpleGraph.Walk.not_nil_iff] at hnnil
    obtain ⟨u, h, q, _⟩ := hnnil
    exact ⟨u, h⟩
  have he : s(v, u) ∈ G.edgeFinset := by rw [mem_edgeFinset]; exact huv
  set b := G.blockOf s(v, u) with hb
  have hb_blocks : b ∈ G.blocks := Finset.mem_image.mpr ⟨s(v, u), he, rfl⟩
  have he_block : s(v, u) ∈ G.edgesInBlock b := by
    unfold edgesInBlock; rw [Finset.mem_filter]; exact ⟨he, rfl⟩
  have hv_block : v ∈ G.blockVertices b := by
    rw [G.mem_blockVertices_iff]; exact ⟨s(v, u), he_block, Sym2.mem_mk_left v u⟩
  have hmem : b ∈ G.blocksAt v := G.mem_blocksAt_iff.mpr ⟨hb_blocks, hv_block⟩
  exact Finset.card_pos.mpr ⟨b, hmem⟩

end Bricks

/-! ### Assembly of the planar girth density bound -/

/-- **General planar girth density bound** (Diestel Corollary 4.2.10).
For a connected non-acyclic planar graph with girth at least `g`, where `g ≥ 3`:

    |E| * (g - 2) ≤ g * (|V| - 2)

The combinatorial bound is proved using Diestel's block decomposition: the
2-connected block bound, separate handling of bridges, and the block-tree
formula `Σ cutVertexMultiplicity = |blocks| - 1`. The explicit topological
axiom `hasPlanarRotationSystem` remains a dependency. -/
theorem IsPlanar.edgeFinset_card_girth_bound {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    {g : ℕ} (hplanar : IsPlanar G) (hgirth : G.HasMinGirth g)
    (hconn : G.Connected) (hcycle : ¬G.IsAcyclic)
    (hg : 3 ≤ g) (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card * (g - 2) ≤ g * (Fintype.card V - 2) := by
  classical
  obtain ⟨bstar, hbstar, hbstar3⟩ := exists_nontrivial_block_of_not_isAcyclic G hcycle
  have hblne : G.blocks.Nonempty := ⟨bstar, hbstar⟩
  have hE := G.card_edgeFinset_eq_sum_blocks
  have hnt : G.nontrivBlockVertices = Finset.univ :=
    aux_nontriv_eq_univ G hconn (by omega)
  have hSV := G.sum_card_blockVertices_eq_card_nontriv_add_sum_mult
  rw [hnt, Finset.card_univ] at hSV
  have hform := sum_cutVertexMultiplicity_eq G hconn hblne
  rw [hform] at hSV
  have hb1 : 1 ≤ G.blocks.card := Finset.card_pos.mpr hblne
  have hper : ∀ b ∈ G.blocks,
      (G.edgesInBlock b).card * (g - 2) ≤
        g * ((G.blockVertices b).card - 2) +
        (g - 2) * (if (G.blockVertices b).card ≤ 2 then 1 else 0) := by
    intro b hb
    by_cases hbig : 3 ≤ (G.blockVertices b).card
    · have hbr := aux_edgesInBlock_girth_bound G hplanar hgirth b hg hbig
      rw [if_neg (by omega)]
      simpa using hbr
    · have h2 : (G.blockVertices b).card ≤ 2 := by omega
      have hle1 := card_edgesInBlock_le_one_of_card_le_two G b h2
      have h2v := two_le_card_blockVertices G hb
      have hv2 : (G.blockVertices b).card = 2 := by omega
      rw [if_pos h2, hv2]
      simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
      simpa using Nat.mul_le_mul_right (g - 2) hle1
  have hsum := Finset.sum_le_sum hper
  rw [← Finset.sum_mul, ← hE] at hsum
  have hRHS : (∑ b ∈ G.blocks, (g * ((G.blockVertices b).card - 2) +
                (g - 2) * (if (G.blockVertices b).card ≤ 2 then 1 else 0))) =
      g * (∑ b ∈ G.blocks, ((G.blockVertices b).card - 2)) +
        (g - 2) * (G.blocks.filter (fun b => (G.blockVertices b).card ≤ 2)).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.card_filter]
  rw [hRHS] at hsum
  set S2 := ∑ b ∈ G.blocks, ((G.blockVertices b).card - 2) with hS2def
  set nBr := (G.blocks.filter (fun b => (G.blockVertices b).card ≤ 2)).card with hnBrdef
  set nBl := G.blocks.card with hnBldef
  have hS2 : S2 + 2 * nBl = ∑ b ∈ G.blocks, (G.blockVertices b).card := by
    have h2c : 2 * nBl = ∑ _b ∈ G.blocks, 2 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hS2def, h2c, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have := two_le_card_blockVertices G hb
    omega
  have hS2eq : S2 + nBl + 1 = Fintype.card V := by
    rw [hSV] at hS2; omega
  have hbr_le : nBr + 1 ≤ nBl := by
    have hsubset : G.blocks.filter (fun b => (G.blockVertices b).card ≤ 2) ⊆ G.blocks :=
      Finset.filter_subset _ _
    have hbnotin : bstar ∉ G.blocks.filter (fun b => (G.blockVertices b).card ≤ 2) := by
      rw [Finset.mem_filter]; rintro ⟨_, h⟩; omega
    have hssub : G.blocks.filter (fun b => (G.blockVertices b).card ≤ 2) ⊂ G.blocks :=
      Finset.ssubset_iff_of_subset hsubset |>.mpr ⟨bstar, hbstar, hbnotin⟩
    have := Finset.card_lt_card hssub
    omega
  have key : (g - 2) * nBr ≤ g * (nBl - 1) := by
    calc (g - 2) * nBr ≤ (g - 2) * (nBl - 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ g * (nBl - 1) := Nat.mul_le_mul_right _ (by omega)
  calc G.edgeFinset.card * (g - 2)
      ≤ g * S2 + (g - 2) * nBr := hsum
    _ ≤ g * S2 + g * (nBl - 1) := by gcongr
    _ = g * (S2 + (nBl - 1)) := by rw [Nat.mul_add]
    _ = g * (Fintype.card V - 2) := by
          rw [show S2 + (nBl - 1) = Fintype.card V - 2 from by omega]

end SimpleGraph
