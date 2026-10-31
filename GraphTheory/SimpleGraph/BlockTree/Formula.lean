/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Block.NontrivConnected
import GraphTheory.SimpleGraph.BlockTree.Acyclic

/-! # Counting formulas from the block-cut tree

For a finite connected graph with at least one block,
`Σ_v cutVertexMultiplicity v = |blocks| - 1`.

The core block-cut graph is a tree by preconnectedness and acyclicity.
Its vertex count is `|blocks| + |cutVertices|`, and its edge count is
`Σ_{v cut} |blocksAt v|` by the incidence bijection. Applying the tree identity
`|E| + 1 = |V|` yields the formula.

Additional lemmas bound a block with at most two vertices by one edge and
show that a non-acyclic graph has a block containing at least three vertices.
These are used to assemble density bounds from individual blocks.

The arguments are combinatorial and use only `propext`, `Classical.choice`,
and `Quot.sound`, without `hasPlanarRotationSystem` or additional axioms.

Reference: Diestel, Graph Theory, 5th edition, §3.1, p. 44. -/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph
open Classical

variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

instance instFiniteBlock : Finite G.Block := by
  unfold SimpleGraph.Block; infer_instance

noncomputable instance instFintypeBlock : Fintype G.Block := Fintype.ofFinite _

/-- The block-cut graph induced on its core vertices. -/
noncomputable def BTcore : SimpleGraph ↥(BlockTree.coreVertices G) :=
  (G.BlockTree).induce (BlockTree.coreVertices G)

/-! ## Counting vertices of the block-cut tree -/

/-- The core as a finset: block entries together with cut-vertex entries. -/
noncomputable def coreFinset : Finset (G.Block ⊕ V) :=
  G.blocks.image Sum.inl ∪ G.cutVertices.image Sum.inr

theorem coreVertices_eq_coe : BlockTree.coreVertices G = ↑(coreFinset G) := by
  classical
  ext x
  simp only [coreFinset, Finset.coe_union, Finset.coe_image, Set.mem_union,
    Set.mem_image, Finset.mem_coe]
  cases x with
  | inl b =>
      rw [BlockTree.mem_coreVertices_inl_iff]
      constructor
      · intro hb; exact Or.inl ⟨b, hb, rfl⟩
      · rintro (⟨b', hb', heq⟩ | ⟨v, _, heq⟩)
        · cases heq; exact hb'
        · exact (Sum.inr_ne_inl heq).elim
  | inr v =>
      rw [BlockTree.mem_coreVertices_inr_iff, ← G.mem_cutVertices_iff]
      constructor
      · intro hv; exact Or.inr ⟨v, hv, rfl⟩
      · rintro (⟨b, _, heq⟩ | ⟨v', hv', heq⟩)
        · exact (Sum.inl_ne_inr heq).elim
        · cases heq; exact hv'

/-- The core has `|blocks| + |cutVertices|` vertices. -/
theorem card_coreVertices [Fintype ↥(BlockTree.coreVertices G)] :
    Fintype.card ↥(BlockTree.coreVertices G) = G.blocks.card + G.cutVertices.card := by
  classical
  have he : (BlockTree.coreVertices G).toFinset = coreFinset G := by
    ext x; rw [Set.mem_toFinset, coreVertices_eq_coe]; simp
  have hcard := congrArg Finset.card he
  rw [Set.toFinset_card] at hcard
  rw [hcard]
  unfold coreFinset
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]
  rw [Finset.disjoint_left]
  rintro x hx hx2
  simp only [Finset.mem_image] at hx hx2
  obtain ⟨b, _, rfl⟩ := hx
  obtain ⟨v, _, heq⟩ := hx2
  exact Sum.inl_ne_inr heq.symm

/-! ## Counting edges of the block-cut tree -/

/-- Cut-vertex/block incidences in the block-cut tree. -/
noncomputable def btIncidences : Finset (V × G.Block) :=
  G.cutVertices.biUnion (fun v => (G.blocksAt v).image (fun b => (v, b)))

theorem mem_btIncidences_iff {p : V × G.Block} :
    p ∈ btIncidences G ↔ p.1 ∈ G.cutVertices ∧ p.2 ∈ G.blocksAt p.1 := by
  classical
  unfold btIncidences
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, b, hb, rfl⟩
    exact ⟨hv, hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.1, h1, p.2, h2, rfl⟩

theorem card_btIncidences :
    (btIncidences G).card = ∑ v ∈ G.cutVertices, (G.blocksAt v).card := by
  classical
  unfold btIncidences
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.card_image_of_injective]
    intro b b' hbb'
    simpa using hbb'
  · intro v _ v' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨b, _, rfl⟩ := hp
    obtain ⟨b', _, heq⟩ := hp'
    exact hne (congrArg Prod.fst heq).symm

/-- The edge/incidence bijection gives `|E| = Σ_{v cut} |blocksAt v|`. -/
theorem card_edgeFinset_BTcore [Fintype (BTcore G).edgeSet] :
    (BTcore G).edgeFinset.card =
      ∑ v ∈ G.cutVertices, (G.blocksAt v).card := by
  classical
  rw [← card_btIncidences G]
  symm
  apply Finset.card_bij
    (i := fun p hp =>
      s(⟨Sum.inr p.1,
          BlockTree.inr_mem_coreVertices G
            ((G.mem_cutVertices_iff).mp ((mem_btIncidences_iff G).mp hp).1)⟩,
        ⟨Sum.inl p.2,
          BlockTree.inl_mem_coreVertices G
            ((G.mem_blocksAt_iff).mp ((mem_btIncidences_iff G).mp hp).2).1⟩))
  · -- mapsTo
    intro p hp
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    have hp' := (mem_btIncidences_iff G).mp hp
    have hvc : G.IsCutVertex p.1 := (G.mem_cutVertices_iff).mp hp'.1
    have hvb : p.1 ∈ G.blockVertices p.2 := ((G.mem_blocksAt_iff).mp hp'.2).2
    show (BTcore G).Adj _ _
    unfold BTcore
    rw [SimpleGraph.induce_adj]
    exact (BlockTree.adj_inr_inl_iff G p.1 p.2).mpr ⟨hvc, hvb⟩
  · -- injective
    intro p hp q hq heq
    simp only [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv := Sum.inr_injective (Subtype.ext_iff.mp h1)
      have hb := Sum.inl_injective (Subtype.ext_iff.mp h2)
      exact Prod.ext hv hb
    · exact absurd (Subtype.ext_iff.mp h1) Sum.inr_ne_inl
  · -- surjective
    intro e he
    induction e with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hadj : (BTcore G).Adj x y := he
      unfold BTcore at hadj
      rw [SimpleGraph.induce_adj, BlockTree.adj_iff] at hadj
      rcases hadj with ⟨b, v, hxv, hyv, hvc, hvb⟩ | ⟨b, v, hxv, hyv, hvc, hvb⟩
      · refine ⟨(v, b), (mem_btIncidences_iff G).mpr ⟨(G.mem_cutVertices_iff).mpr hvc, ?_⟩, ?_⟩
        · rw [G.mem_blocksAt_iff]
          exact ⟨(BlockTree.mem_coreVertices_inl_iff G).mp (hxv ▸ x.2), hvb⟩
        · dsimp only
          rw [Sym2.eq_iff]
          exact Or.inr ⟨Subtype.ext hyv.symm, Subtype.ext hxv.symm⟩
      · refine ⟨(v, b), (mem_btIncidences_iff G).mpr ⟨(G.mem_cutVertices_iff).mpr hvc, ?_⟩, ?_⟩
        · rw [G.mem_blocksAt_iff]
          exact ⟨(BlockTree.mem_coreVertices_inl_iff G).mp (hyv ▸ y.2), hvb⟩
        · dsimp only
          rw [Sym2.eq_iff]
          exact Or.inl ⟨Subtype.ext hxv.symm, Subtype.ext hyv.symm⟩

/-! ## The core block-cut graph is a tree -/

/-- For connected G with at least one block, the core block-cut graph is a tree. -/
theorem BTcore_isTree (hG : G.Connected) (hne : G.blocks.Nonempty)
    [Nonempty ↥(BlockTree.coreVertices G)] :
    (BTcore G).IsTree := by
  classical
  refine ⟨?_, BlockTree.isAcyclic G⟩
  rw [connected_iff]
  exact ⟨BlockTree.preconnected G hG, inferInstance⟩

/-! ## The block-tree counting identity -/

/-- For a connected graph with at least one block,
`Σ_v cutVertexMultiplicity v = |blocks| - 1`. -/
theorem sum_cutVertexMultiplicity_eq (hG : G.Connected) (hne : G.blocks.Nonempty) :
    ∑ v : V, G.cutVertexMultiplicity v = G.blocks.card - 1 := by
  classical
  haveI iFV : Fintype ↥(BlockTree.coreVertices G) := Fintype.ofFinite _
  haveI iFE : Fintype (BTcore G).edgeSet := Fintype.ofFinite _
  have hcore_ne : (BlockTree.coreVertices G).Nonempty := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨Sum.inl b, BlockTree.inl_mem_coreVertices G hb⟩
  haveI : Nonempty ↥(BlockTree.coreVertices G) := hcore_ne.to_subtype
  have hVE : (BTcore G).edgeFinset.card + 1 =
      Fintype.card ↥(BlockTree.coreVertices G) :=
    (BTcore_isTree G hG hne).card_edgeFinset
  rw [card_coreVertices G, card_edgeFinset_BTcore G] at hVE
  have hb1 : 1 ≤ G.blocks.card := Finset.card_pos.mpr hne
  have hrestrict : ∑ v : V, G.cutVertexMultiplicity v =
      ∑ v ∈ G.cutVertices, G.cutVertexMultiplicity v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [G.mem_cutVertices_iff] at hv
    unfold cutVertexMultiplicity
    unfold IsCutVertex at hv
    omega
  have hmult : ∑ v ∈ G.cutVertices, G.cutVertexMultiplicity v + G.cutVertices.card =
      ∑ v ∈ G.cutVertices, (G.blocksAt v).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [G.mem_cutVertices_iff] at hv
    unfold cutVertexMultiplicity
    unfold IsCutVertex at hv
    omega
  rw [hrestrict]
  omega

/-- For a connected graph with at least two vertices, the sum of block
vertex counts is `|V(G)| + (|blocks| - 1)`. The cardinality hypothesis excludes
the one-vertex edgeless graph, where truncated subtraction would make the
displayed identity false. -/
theorem card_add_card_blocks_sub_one_eq_sum_card_blockVertices
    (hG : G.Connected) (hV : 2 ≤ Fintype.card V) :
    Fintype.card V + (G.blocks.card - 1) =
      ∑ b ∈ G.blocks, (G.blockVertices b).card := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hnontriv : G.nontrivBlockVertices = Finset.univ :=
    nontrivBlockVertices_eq_univ_of_connected (G := G) hG hV
  have hblocks : G.blocks.Nonempty := by
    have hnontriv_ne : G.nontrivBlockVertices.Nonempty := by
      rw [hnontriv]
      exact Finset.univ_nonempty
    obtain ⟨v, hv⟩ := hnontriv_ne
    have hcard : 1 ≤ (G.blocksAt v).card := (Finset.mem_filter.mp hv).2
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (G.blocksAt v).card)
    exact ⟨b, (G.mem_blocksAt_iff.mp hb).1⟩
  rw [G.sum_card_blockVertices_eq_card_nontriv_add_sum_mult, hnontriv,
    Finset.card_univ, sum_cutVertexMultiplicity_eq G hG hblocks]

/-! ## Bridge blocks and nontrivial blocks -/

/-- Both endpoints of a block edge belong to the block vertex set. -/
theorem edge_toFinset_subset_blockVertices {b : G.Block} {e : Sym2 V}
    (he : e ∈ G.edgesInBlock b) : e.toFinset ⊆ G.blockVertices b := by
  classical
  intro x hx
  rw [Sym2.mem_toFinset] at hx
  rw [mem_blockVertices_iff]
  exact ⟨e, he, hx⟩

/-- A block edge is not a diagonal pair, since the graph is simple. -/
theorem edgesInBlock_not_isDiag {b : G.Block} {e : Sym2 V}
    (he : e ∈ G.edgesInBlock b) : ¬ e.IsDiag := by
  classical
  have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
  rw [mem_edgeFinset] at heG
  induction e with
  | h a c =>
    rw [mem_edgeSet] at heG
    simp only [Sym2.mk_isDiag_iff]
    exact heG.ne

/-- A block with at most two vertices has at most one edge. -/
theorem card_edgesInBlock_le_one_of_card_le_two (b : G.Block)
    (h : (G.blockVertices b).card ≤ 2) : (G.edgesInBlock b).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro e1 he1 e2 he2
  have hsub1 : e1.toFinset ⊆ G.blockVertices b := edge_toFinset_subset_blockVertices G he1
  have hsub2 : e2.toFinset ⊆ G.blockVertices b := edge_toFinset_subset_blockVertices G he2
  have hc1 : e1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e1 (edgesInBlock_not_isDiag G he1)
  have hc2 : e2.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e2 (edgesInBlock_not_isDiag G he2)
  have heq1 : e1.toFinset = G.blockVertices b :=
    Finset.eq_of_subset_of_card_le hsub1 (by omega)
  have heq2 : e2.toFinset = G.blockVertices b :=
    Finset.eq_of_subset_of_card_le hsub2 (by omega)
  have htf : e1.toFinset = e2.toFinset := heq1.trans heq2.symm
  have hd1 := edgesInBlock_not_isDiag G he1
  have hd2 := edgesInBlock_not_isDiag G he2
  induction e1 with
  | h a b' =>
    induction e2 with
    | h c d =>
      simp only [Sym2.mk_isDiag_iff] at hd1 hd2
      have hmem : ∀ z, z ∈ ({a, b'} : Finset V) ↔ z ∈ ({c, d} : Finset V) := by
        intro z
        have := congrArg (z ∈ ·) htf
        simpa [Sym2.toFinset] using this
      rw [Sym2.eq_iff]
      have ha := (hmem a).mp (by simp)
      have hb := (hmem b').mp (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        first
          | (exfalso; exact hd1 rfl)
          | tauto

/-- An edge-containing block has at least two vertices. -/
theorem two_le_card_blockVertices {b : G.Block} (hb : b ∈ G.blocks) :
    2 ≤ (G.blockVertices b).card := by
  classical
  obtain ⟨e, he⟩ := (G.block_decomposition).1 b hb
  have hsub : e.toFinset ⊆ G.blockVertices b := edge_toFinset_subset_blockVertices G he
  have hc : e.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e (edgesInBlock_not_isDiag G he)
  have := Finset.card_le_card hsub
  omega

/-- A non-acyclic graph has an edge-containing block with at least three
vertices, obtained from a cycle. -/
theorem exists_nontrivial_block_of_not_isAcyclic (hcyc : ¬ G.IsAcyclic) :
    ∃ b ∈ G.blocks, 3 ≤ (G.blockVertices b).card := by
  classical
  simp only [IsAcyclic, not_forall, not_not] at hcyc
  obtain ⟨u, w, hw⟩ := hcyc
  have hlen : 3 ≤ w.length := hw.three_le_length
  have hnd : w.edges.Nodup := hw.edges_nodup
  have hne : w.edges ≠ [] := by
    intro h
    have : w.edges.length = 0 := by rw [h]; rfl
    rw [Walk.length_edges] at this; omega
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hne
  set b₀ := G.blockOf e₀ with hb₀
  have he₀G : e₀ ∈ G.edgeFinset := by
    rw [mem_edgeFinset]; exact w.edges_subset_edgeSet he₀
  have hb₀blocks : b₀ ∈ G.blocks := Finset.mem_image.mpr ⟨e₀, he₀G, rfl⟩
  have hsub : w.edges.toFinset ⊆ G.edgesInBlock b₀ := by
    intro e he
    rw [List.mem_toFinset] at he
    have hsb : G.SameBlock e e₀ := SameBlock.of_common_cycle G hw he he₀
    have hbe : G.blockOf e = b₀ := (G.blockOf_eq_iff).mpr hsb
    unfold edgesInBlock
    rw [Finset.mem_filter]
    refine ⟨?_, hbe⟩
    rw [mem_edgeFinset]; exact w.edges_subset_edgeSet he
  have hcard2 : 2 ≤ (G.edgesInBlock b₀).card := by
    have h1 : w.edges.toFinset.card ≤ (G.edgesInBlock b₀).card := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Walk.length_edges] at h1
    omega
  refine ⟨b₀, hb₀blocks, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have := card_edgesInBlock_le_one_of_card_le_two G b₀ (by omega)
  omega

end SimpleGraph
