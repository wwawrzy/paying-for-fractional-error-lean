/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Degree and density basics (Diestel §1.2)

We prove that for any finite simple graph `G`:

  `minDegree * |V| <= 2 * |E| <= maxDegree * |V|`

equivalently, the minimum degree is at most the average degree,
which is at most the maximum degree.

The proof uses the handshaking lemma (`sum_degrees_eq_twice_card_edges`)
together with the pointwise bounds `minDegree <= degree v <= maxDegree`.
-/

namespace SimpleGraph

section DegreeAndDensity

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/-- The minimum degree times the number of vertices is at most twice the number of edges. -/
theorem minDegree_mul_card_le_two_mul_card_edges :
    G.minDegree * Fintype.card V ≤ 2 * G.edgeFinset.card := by
  have h1 := G.sum_degrees_eq_twice_card_edges
  have h2 : Finset.univ.sum (fun _ => G.minDegree) ≤ Finset.univ.sum (fun v => G.degree v) :=
    Finset.sum_le_sum (fun v _ => G.minDegree_le_degree v)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
  linarith

/-- Twice the number of edges is at most the maximum degree times the number of vertices. -/
theorem two_mul_card_edges_le_maxDegree_mul_card :
    2 * G.edgeFinset.card ≤ G.maxDegree * Fintype.card V := by
  have h1 := G.sum_degrees_eq_twice_card_edges
  have h2 : Finset.univ.sum (fun v => G.degree v) ≤ Finset.univ.sum (fun _ => G.maxDegree) :=
    Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
  linarith

/-- Combined: `minDegree * |V| <= 2 * |E| <= maxDegree * |V|`. -/
theorem minDegree_mul_card_le_two_mul_card_edges_le_maxDegree_mul_card :
    G.minDegree * Fintype.card V ≤ 2 * G.edgeFinset.card ∧
    2 * G.edgeFinset.card ≤ G.maxDegree * Fintype.card V :=
  ⟨G.minDegree_mul_card_le_two_mul_card_edges,
   G.two_mul_card_edges_le_maxDegree_mul_card⟩

/-! ## Edge density and mean degree

Diestel distinguishes the **edge density**

`epsilon(G) = |E(G)| / |V(G)|`

from the **mean degree**

`d(G) = 2 |E(G)| / |V(G)|`.

The older MdsLean name `averageDegree` denoted `epsilon(G)`. We retain it as a
compatibility spelling, but expose the two mathematical quantities explicitly as
`edgeVertexDensity` and `meanDegree`.
-/

/-- Diestel's **edge density** `epsilon(G) = |E(G)| / |V(G)|`, as a rational number. -/
noncomputable def edgeVertexDensity : ℚ :=
  (G.edgeFinset.card : ℚ) / (Fintype.card V : ℚ)

/-- Legacy MdsLean spelling for `edgeVertexDensity`.

This definition is kept for compatibility with results written before MdsLean distinguished
Diestel's edge density `epsilon(G)` from his mean degree `d(G)`. -/
noncomputable def averageDegree : ℚ :=
  (G.edgeFinset.card : ℚ) / (Fintype.card V : ℚ)

/-- Diestel's **mean degree** `d(G) = 2 |E(G)| / |V(G)|`, as a rational number. -/
noncomputable def meanDegree : ℚ :=
  2 * (G.edgeFinset.card : ℚ) / (Fintype.card V : ℚ)

/-- Diestel §1.2: edge density is half the mean degree, `epsilon(G) = d(G) / 2`. -/
theorem edgeVertexDensity_eq_meanDegree_div_two :
    G.edgeVertexDensity = G.meanDegree / 2 := by
  unfold edgeVertexDensity meanDegree
  ring

/-- The minimum degree is at most the mean degree, `delta(G) <= d(G)`. -/
theorem minDegree_le_meanDegree (hV : 0 < Fintype.card V) :
    (G.minDegree : ℚ) ≤ G.meanDegree := by
  unfold meanDegree
  rw [le_div_iff₀ (by positivity : (0 : ℚ) < (Fintype.card V : ℚ))]
  exact_mod_cast G.minDegree_mul_card_le_two_mul_card_edges

/-- The mean degree is at most the maximum degree, `d(G) <= Delta(G)`. -/
theorem meanDegree_le_maxDegree (hV : 0 < Fintype.card V) :
    G.meanDegree ≤ (G.maxDegree : ℚ) := by
  unfold meanDegree
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < (Fintype.card V : ℚ))]
  exact_mod_cast G.two_mul_card_edges_le_maxDegree_mul_card

/-- Diestel §1.2: `delta(G) <= d(G) <= Delta(G)` for a nonempty finite graph. -/
theorem minDegree_le_meanDegree_le_maxDegree (hV : 0 < Fintype.card V) :
    (G.minDegree : ℚ) ≤ G.meanDegree ∧ G.meanDegree ≤ (G.maxDegree : ℚ) :=
  ⟨G.minDegree_le_meanDegree hV, G.meanDegree_le_maxDegree hV⟩

/-- `epsilon(G) >= delta(G)/2`, a direct corollary of the degree-sum inequality. -/
theorem edgeVertexDensity_ge_minDegree_div_two (hV : 0 < Fintype.card V) :
    (G.minDegree : ℚ) / 2 ≤ G.edgeVertexDensity := by
  unfold edgeVertexDensity
  have h := G.minDegree_mul_card_le_two_mul_card_edges
  rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < 2)
    (by positivity : (0 : ℚ) < (Fintype.card V : ℚ))]
  norm_cast
  linarith

/-- Compatibility form of `edgeVertexDensity_ge_minDegree_div_two`. -/
theorem averageDegree_ge_minDegree_div_two (hV : 0 < Fintype.card V) :
    (G.minDegree : ℚ) / 2 ≤ G.averageDegree := by
  simpa only [averageDegree, edgeVertexDensity] using
    G.edgeVertexDensity_ge_minDegree_div_two hV

/-- The Nat-valued form: delta(G) * |V| <= 2 * |E|.
    This is an alias for `minDegree_mul_card_le_two_mul_card_edges` restated
    as a lower bound on the number of edges. -/
theorem card_edges_ge_minDegree_mul_card_div_two :
    G.minDegree * Fintype.card V ≤ 2 * G.edgeFinset.card :=
  G.minDegree_mul_card_le_two_mul_card_edges

end DegreeAndDensity

/-! ## A densest subgraph (Diestel, Proposition 1.2.2) -/

section DensestSubgraph

variable {V W : Type*}

/-- Edge density is invariant under graph isomorphism. -/
theorem Iso.edgeVertexDensity_eq {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel H.Adj]
    (f : G ≃g H) : G.edgeVertexDensity = H.edgeVertexDensity := by
  unfold edgeVertexDensity
  rw [f.card_edgeFinset_eq, Fintype.card_congr f.toEquiv]

/-- A decision-procedure-independent formula for edge density. -/
theorem edgeVertexDensity_eq_natCard (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    G.edgeVertexDensity = (Nat.card G.edgeSet : ℚ) / (Nat.card V : ℚ) := by
  unfold edgeVertexDensity
  rw [G.edgeFinset_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]

/-- Deleting a vertex whose degree is at most the current edge density cannot
decrease edge density, provided that the graph has an edge. -/
private lemma edgeVertexDensity_le_induce_compl_singleton
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (v : V) (hE : 0 < G.edgeFinset.card)
    (hv : (G.degree v : ℚ) ≤ G.edgeVertexDensity) :
    G.edgeVertexDensity ≤ (G.induce ({v}ᶜ : Set V)).edgeVertexDensity := by
  have hne : G ≠ ⊥ := G.edgeFinset_nonempty.mp (Finset.card_pos.mp hE)
  obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hne
  have hcard : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    exact hab.ne (Fintype.card_le_one_iff.mp hle a b)
  have hdeg : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
  have hcard1 : 1 ≤ Fintype.card V := by omega
  unfold edgeVertexDensity at hv ⊢
  rw [G.card_edgeFinset_induce_compl_singleton,
    G.card_edgeFinset_deleteIncidenceSet,
    Fintype.card_compl_set, Set.card_singleton]
  push_cast [Nat.cast_sub hdeg, Nat.cast_sub hcard1] at hv ⊢
  have hn : (0 : ℚ) < Fintype.card V := by positivity
  have hn1 : (0 : ℚ) < Fintype.card V - 1 := by
    exact_mod_cast (by omega : 0 < Fintype.card V - 1)
  rw [le_div_iff₀ hn] at hv
  rw [div_le_div_iff₀ hn hn1]
  nlinarith

/-- Density of a Mathlib subgraph, computed on its own vertex set. The use of
`Nat.card` makes this auxiliary quantity independent of chosen finite and
decidability instances. -/
private noncomputable def subgraphEdgeVertexDensity {G : SimpleGraph V}
    (H : G.Subgraph) : ℚ :=
  (Nat.card H.coe.edgeSet : ℚ) / (Nat.card H.verts : ℚ)

private lemma subgraphEdgeVertexDensity_eq {G : SimpleGraph V}
    (H : G.Subgraph) [Fintype H.verts] [DecidableRel H.Adj] :
    subgraphEdgeVertexDensity H = H.coe.edgeVertexDensity := by
  rw [H.coe.edgeVertexDensity_eq_natCard]
  rfl

private lemma subgraphEdgeVertexDensity_top (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    subgraphEdgeVertexDensity (⊤ : G.Subgraph) = G.edgeVertexDensity := by
  classical
  let f := (⊤ : G.Subgraph).spanningCoeEquivCoeOfSpanning (fun _ => Set.mem_univ _)
  unfold subgraphEdgeVertexDensity
  rw [G.edgeVertexDensity_eq_natCard]
  have hedge := Nat.card_congr f.mapEdgeSet
  have hvert := Nat.card_congr f.toEquiv
  simp only [Subgraph.spanningCoe_top] at hedge hvert
  rw [← hedge, ← hvert]

/-- **Diestel, Proposition 1.2.2.** Every finite simple graph with at least one
edge has a subgraph `H` such that `δ(H) > ε(H) ≥ ε(G)`.

The witness is chosen with maximum edge density and, among all maximizers,
with the fewest vertices. If a minimum-degree vertex had degree at most the
density, deleting it would preserve density and contradict that second
minimality condition. -/
theorem exists_subgraph_minDegree_gt_edgeVertexDensity
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hE : 0 < G.edgeFinset.card) :
    ∃ (H : G.Subgraph) (_ : Fintype H.verts) (_ : DecidableRel H.Adj),
      G.edgeVertexDensity ≤ H.coe.edgeVertexDensity ∧
      H.coe.edgeVertexDensity < (H.coe.minDegree : ℚ) := by
  classical
  let density : G.Subgraph → ℚ := fun H => subgraphEdgeVertexDensity H
  obtain ⟨Hmax, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G.Subgraph) density Finset.univ_nonempty
  let maximizers : Finset G.Subgraph :=
    Finset.univ.filter fun H => density H = density Hmax
  have hmaximizers : maximizers.Nonempty := by
    refine ⟨Hmax, ?_⟩
    simp [maximizers]
  obtain ⟨H, hH, hmin⟩ :=
    Finset.exists_min_image maximizers (fun K => K.verts.ncard) hmaximizers
  have hHdensity : density H = density Hmax := (Finset.mem_filter.mp hH).2
  have hHmax (K : G.Subgraph) : density K ≤ density H := by
    rw [hHdensity]
    exact hmax K (Finset.mem_univ K)
  have hGle : G.edgeVertexDensity ≤ density H := by
    calc
      G.edgeVertexDensity = subgraphEdgeVertexDensity (⊤ : G.Subgraph) :=
        (subgraphEdgeVertexDensity_top G).symm
      _ ≤ density H := hHmax (⊤ : G.Subgraph)
  have hGpos : 0 < G.edgeVertexDensity := by
    unfold SimpleGraph.edgeVertexDensity
    have hV : 0 < Fintype.card V := by
      have hne : G ≠ ⊥ := G.edgeFinset_nonempty.mp (Finset.card_pos.mp hE)
      obtain ⟨a, -, -⟩ := ne_bot_iff_exists_adj.mp hne
      exact Fintype.card_pos_iff.mpr ⟨a⟩
    positivity
  have hHpos : 0 < density H := hGpos.trans_le hGle
  letI : Fintype H.verts := Fintype.ofFinite _
  letI : DecidableRel H.Adj := Classical.decRel _
  refine ⟨H, inferInstance, inferInstance, ?_, ?_⟩
  · calc
      G.edgeVertexDensity ≤ subgraphEdgeVertexDensity H := hGle
      _ = H.coe.edgeVertexDensity := subgraphEdgeVertexDensity_eq H
  have hHcoepos : 0 < H.coe.edgeVertexDensity := by
    rw [← subgraphEdgeVertexDensity_eq H]
    exact hHpos
  have hHE : 0 < H.coe.edgeFinset.card := by
    by_contra h
    have hz : H.coe.edgeFinset.card = 0 := Nat.eq_zero_of_not_pos h
    simp [edgeVertexDensity, hz] at hHcoepos
  have hHne : H.coe ≠ ⊥ := H.coe.edgeFinset_nonempty.mp (Finset.card_pos.mp hHE)
  obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hHne
  letI : Nonempty H.verts := ⟨a⟩
  by_contra hstrict
  have hstrict' : (H.coe.minDegree : ℚ) ≤ H.coe.edgeVertexDensity := not_lt.mp hstrict
  obtain ⟨v, hvmin⟩ := H.coe.exists_minimal_degree_vertex
  letI : Fintype (H.coe.neighborSet v) := H.coe.neighborSetFintype v
  have hv : (H.coe.degree v : ℚ) ≤ H.coe.edgeVertexDensity := by
    simpa only [hvmin] using hstrict'
  let K : G.Subgraph := H.deleteVerts ({v.val} : Set V)
  letI : Fintype K.verts := Fintype.ofFinite _
  letI : DecidableRel K.Adj := Classical.decRel _
  have hdelete : H.coe.edgeVertexDensity ≤
      (H.coe.induce ({v}ᶜ : Set H.verts)).edgeVertexDensity :=
    edgeVertexDensity_le_induce_compl_singleton H.coe v hHE hv
  have hiso : K.coe ≃g H.coe.induce ({v}ᶜ : Set H.verts) := by
    have hset : {w : H.verts | (w : V) ∉ ({v.val} : Set V)} =
        ({v}ᶜ : Set H.verts) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_compl_iff]
      exact not_congr Subtype.ext_iff.symm
    change (H.deleteVerts ({v.val} : Set V)).coe ≃g
      H.coe.induce ({v}ᶜ : Set H.verts)
    rw [← hset]
    exact H.coeDeleteVertsIso ({v.val} : Set V)
  have hKge : density H ≤ density K := by
    change subgraphEdgeVertexDensity H ≤ subgraphEdgeVertexDensity K
    calc
      subgraphEdgeVertexDensity H = H.coe.edgeVertexDensity :=
        subgraphEdgeVertexDensity_eq H
      _ ≤ (H.coe.induce ({v}ᶜ : Set H.verts)).edgeVertexDensity := hdelete
      _ = K.coe.edgeVertexDensity := hiso.edgeVertexDensity_eq.symm
      _ = subgraphEdgeVertexDensity K := (subgraphEdgeVertexDensity_eq K).symm
  have hKle : density K ≤ density H := hHmax K
  have hKeq : density K = density H := le_antisymm hKle hKge
  have hKmem : K ∈ maximizers := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ K, ?_⟩
    exact hKeq.trans hHdensity
  have hcardmin : H.verts.ncard ≤ K.verts.ncard := hmin K hKmem
  have hcardK : K.verts.ncard = H.verts.ncard - 1 := by
    change (H.deleteVerts ({v.val} : Set V)).verts.ncard = H.verts.ncard - 1
    rw [Subgraph.deleteVerts_verts]
    exact Set.ncard_diff_singleton_of_mem v.prop
  rw [hcardK] at hcardmin
  have hncardpos : 0 < H.verts.ncard :=
    (Set.ncard_pos (s := H.verts)).mpr ⟨v.val, v.prop⟩
  omega

end DensestSubgraph

/-! ## Large mean degree with minimum degree zero -/

/-- The canonical embedding whose complement is the isolated `none` vertex. -/
private def optionSomeEmbedding (n : ℕ) : Fin n ↪ Option (Fin n) where
  toFun := Option.some
  inj' := Option.some_injective (Fin n)

/-- A complete graph on `n` vertices together with one isolated vertex `none`. -/
def completeGraphWithIsolatedVertex (n : ℕ) : SimpleGraph (Option (Fin n)) :=
  (⊤ : SimpleGraph (Fin n)).map (optionSomeEmbedding n)

instance (n : ℕ) : DecidableRel (completeGraphWithIsolatedVertex n).Adj := by
  unfold completeGraphWithIsolatedVertex
  infer_instance

@[simp]
theorem completeGraphWithIsolatedVertex_card_edges (n : ℕ) :
    (completeGraphWithIsolatedVertex n).edgeFinset.card = n.choose 2 := by
  unfold completeGraphWithIsolatedVertex
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    edgeSet_map, Set.ncard_image_of_injective _ (optionSomeEmbedding n).sym2Map.injective]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_edgeSet,
    card_edgeFinset_top_eq_card_choose_two]
  simp

@[simp]
theorem completeGraphWithIsolatedVertex_degree_none (n : ℕ) :
    (completeGraphWithIsolatedVertex n).degree none = 0 := by
  rw [degree_eq_zero_iff_notMem_support]
  intro hnone
  rw [mem_support] at hnone
  obtain ⟨w, hw⟩ := hnone
  rw [completeGraphWithIsolatedVertex, map_adj] at hw
  obtain ⟨u, -, -, hu, -⟩ := hw
  cases hu

@[simp]
theorem completeGraphWithIsolatedVertex_minDegree (n : ℕ) :
    (completeGraphWithIsolatedVertex n).minDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    (completeGraphWithIsolatedVertex n).minDegree ≤
        (completeGraphWithIsolatedVertex n).degree none :=
      (completeGraphWithIsolatedVertex n).minDegree_le_degree none
    _ = 0 := completeGraphWithIsolatedVertex_degree_none n

/-- **Diestel §1.2.** Arbitrarily large mean degree does not force positive
minimum degree: for every natural threshold `k`, a clique on `k+2` vertices
together with one isolated vertex has mean degree at least `k` and minimum
degree zero. -/
theorem exists_graph_meanDegree_ge_with_minDegree_zero (k : ℕ) :
    ∃ (V' : Type) (_ : Fintype V') (G' : SimpleGraph V') (_ : DecidableRel G'.Adj),
      (k : ℚ) ≤ G'.meanDegree ∧ G'.minDegree = 0 := by
  let G' := completeGraphWithIsolatedVertex (k + 2)
  refine ⟨Option (Fin (k + 2)), inferInstance, G', inferInstance, ?_, ?_⟩
  · dsimp [G']
    unfold meanDegree
    rw [completeGraphWithIsolatedVertex_card_edges]
    simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
    rw [Nat.cast_choose_two]
    push_cast
    rw [show (k : ℚ) + 2 - 1 = k + 1 by ring]
    rw [show (2 : ℚ) * (((k : ℚ) + 2) * ((k : ℚ) + 1) / 2) =
      ((k : ℚ) + 2) * ((k : ℚ) + 1) by ring]
    rw [show (k : ℚ) + 2 + 1 = k + 3 by ring]
    have hk3 : (0 : ℚ) < k + 3 := by positivity
    rw [le_div_iff₀ hk3]
    nlinarith
  · exact completeGraphWithIsolatedVertex_minDegree (k + 2)

end SimpleGraph
