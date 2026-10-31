/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Minor.Antisymmetry
import GraphTheory.SimpleGraph.AverageDegree
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Average degree forces complete minor (Diestel, Proposition 7.2.3)

If the average degree d(G) = 2|E|/|V| >= 2^(h-2), then G contains K_h as a minor.
This is a classical result connecting edge density to the existence of complete minors.

## Proof structure

The proof uses induction on h:
* **Base case (h = 2)**: d(G) ≥ 1 implies G has at least one edge, hence a K₂ minor.
* **Inductive step (h ≥ 3)**: If d(G) ≥ 2^(h-2), there exists a vertex v of degree
  ≥ 2^(h-2). The neighborhood N(v) induces a subgraph with average degree ≥ 2^(h-3).
  By IH, N(v) contains a K_{h-1} minor. Adding v extends this to a K_h minor.
  The minor model extension (Step 4) is fully proved. The neighborhood density
  argument (Step 2) is proved from a per-vertex common-neighbors hypothesis.

## Proof status

* `avg_degree_implies_min_degree` -- PROVED (degeneracy argument by induction on |V|)
* `commonNeighbors_implies_induced_degree` -- PROVED (bridge from CN to induced degree)
* `neighborhood_density` -- PROVED (handshaking + Finset.card_nsmul_le_sum)
* `contractAdj` -- DEFINED (edge contraction on `{s}ᶜ`)
* `contractAdj_isMinor` -- PROVED (contraction is a minor via branch sets)
* `exists_dense_minor_with_cn_bound` -- PROVED (extracts ε-minimal minor with CN bound)
* `averageDegree_inductive_step` -- PROVED (uses CN-bounded minor + IH)
* `card_edgeFinset_contractAdj` -- PROVED (edge-count formula for contraction,
  via Finset.card_bij with the σ-map that merges s into t)

## Main results

* `SimpleGraph.averageDegree_forces_complete_minor` -- d(G) >= 2^(h-2) implies G has a K_h minor
* `SimpleGraph.IsKMinorFree.averageDegree_lt` -- contrapositive: K_h-minor-free implies
  average degree < 2^(h-2)
* `SimpleGraph.IsKMinorFree.edgeFinset_card_lt` -- K_h-minor-free implies
  |E| < 2^(h-3) * |V|

## References

* Diestel, *Graph Theory*, 5th ed., Proposition 7.2.3
* Kostochka (1984), Thomason (1984)
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Helper: extracting an edge from a non-empty graph -/

/-- A non-bottom graph has at least one edge. -/
private lemma exists_adj_of_ne_bot (G : SimpleGraph V)
    (hne : G ≠ ⊥) : ∃ v w : V, G.Adj v w := by
  by_contra h; push Not at h; apply hne; ext v w
  exact ⟨fun ha => absurd ha (h v w), fun hb => absurd hb (by simp [bot_adj])⟩

/-! ### K₂ minor model from an edge -/

/-- Given an edge {v, w} in G, construct a minor model of K₂ in G.
Branch set 0 = {v}, branch set 1 = {w}. -/
noncomputable def MinorModel.ofEdge (G : SimpleGraph V) {v w : V} (hadj : G.Adj v w) :
    MinorModel (SimpleGraph.completeGraph (Fin 2)) G where
  branchSet := fun i => if i = 0 then {v} else {w}
  nonempty := by intro i; fin_cases i <;> simp
  disjoint := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · exact fun heq => G.irrefl (heq ▸ hadj)
    · exact fun heq => G.irrefl (heq ▸ hadj.symm)
  connected := by intro i; fin_cases i <;> simp
  adjacent := by
    intro i j hij; fin_cases i <;> fin_cases j
    · exfalso; revert hij; decide
    · exact ⟨v, Set.mem_singleton v, w, Set.mem_singleton w, hadj⟩
    · exact ⟨w, Set.mem_singleton w, v, Set.mem_singleton v, hadj.symm⟩
    · exfalso; revert hij; decide

/-! ### Helper lemmas for the inductive step -/

/-- **Step 1 of the inductive step**: If `c * |V| ≤ 2|E|` and `|V| > 0`,
then `G.maxDegree ≥ c`. This follows from `2|E| ≤ maxDegree * |V|`. -/
private lemma maxDegree_ge_of_avg_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℕ) (hV : 0 < Fintype.card V)
    (havg : c * Fintype.card V ≤ 2 * G.edgeFinset.card) :
    c ≤ G.maxDegree := by
  have h2 := G.two_mul_card_edges_le_maxDegree_mul_card
  have hle : c * Fintype.card V ≤ G.maxDegree * Fintype.card V := by linarith
  exact Nat.le_of_mul_le_mul_right hle hV

/-- **Step 1b**: There exists a vertex achieving the maximum degree. Combined with
`maxDegree_ge_of_avg_bound`, we get a vertex of degree ≥ c. -/
private lemma exists_vertex_high_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℕ) (hV : 0 < Fintype.card V)
    (havg : c * Fintype.card V ≤ 2 * G.edgeFinset.card) :
    ∃ v : V, c ≤ G.degree v := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  exact ⟨v, by linarith [maxDegree_ge_of_avg_bound G c hV havg]⟩

/-- **Step 4**: Extending a K_{h-1} minor model in the neighborhood to a K_h minor model.

If `v` is a vertex of `G`, and `G.induce (G.neighborSet v)` contains `K_{h-1}` as a minor,
then `G` contains `K_h` as a minor. The new branch set for the additional vertex of `K_h`
is `{v}`, and it connects to all existing branch sets because each branch set lies
within `N(v)` and `v` is adjacent to everything in `N(v)`.

**Fully proved.** The proof constructs Fin h → Set V branch sets by combining the
K_{h-1} minor model (on Fin (h-1) mapped into N(v) ⊂ V) with the singleton {v}.
Branch set 0 = {v}, branch set (i+1) = Subtype.val '' (m.branchSet i).
Key ingredients: Fin index arithmetic, connectivity transfer via graph homomorphism,
disjointness from irreflexivity (v ∉ N(v)) and original branch set disjointness. -/
private lemma extend_minor_from_neighborhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (h : ℕ) (hh : 3 ≤ h)
    (hminor : ¬ (G.induce (G.neighborSet v)).IsKMinorFree (h - 1)) :
    ¬ G.IsKMinorFree h := by
  -- Helper: connectivity transfers through Subtype.val image
  have image_connected : ∀ (S : Set V) (T : Set S) (hconn : (G.induce S).induce T |>.Connected),
      (G.induce (Subtype.val '' T)).Connected := by
    intro S T hconn
    rw [connected_iff_exists_forall_reachable] at hconn ⊢
    obtain ⟨⟨root, hroot⟩, hreach⟩ := hconn
    refine ⟨⟨root.val, Set.mem_image_of_mem _ hroot⟩, ?_⟩
    intro ⟨w, hw⟩
    obtain ⟨⟨w', hw'_S⟩, hw'_T, hw'_eq⟩ := hw
    subst hw'_eq
    specialize hreach ⟨⟨w', hw'_S⟩, hw'_T⟩
    -- Transfer the walk via Reachable.map
    obtain ⟨walk⟩ := hreach
    constructor
    -- Define the homomorphism explicitly as a `let` so it's transparent
    let hom : ((G.induce S).induce T) →g (G.induce (Subtype.val '' T)) :=
      ⟨fun ⟨⟨u, hu_S⟩, hu_T⟩ => ⟨u, Set.mem_image_of_mem _ hu_T⟩,
       fun {a b} hadj => hadj⟩
    exact walk.map hom
  -- Extract the minor model
  have ⟨m⟩ : (completeGraph (Fin (h - 1))) ≤m (G.induce (G.neighborSet v)) := by
    by_contra h_contra; exact hminor (fun ⟨mm⟩ => h_contra ⟨mm⟩)
  -- Build a K_h minor model in G
  intro hfree; apply hfree
  -- For i : Fin h, branch set is: {v} if i=0, else Subtype.val '' m.branchSet (i-1)
  -- Helper: lift index from Fin h (with i.val > 0) to Fin (h-1)
  -- Using `let` so that it's definitionally transparent
  let idx : ∀ i : Fin h, i.val ≠ 0 → Fin (h - 1) :=
    fun i hi => ⟨i.val - 1, by omega⟩
  -- Helper: elements of branch sets are in G.neighborSet v
  have mem_nbr : ∀ (i : Fin (h - 1)) (w : G.neighborSet v),
      w ∈ m.branchSet i → (w : V) ∈ G.neighborSet v := fun _ w _ => w.prop
  -- The branch sets
  let bs : Fin h → Set V := fun i =>
    if hi : i.val = 0 then {v}
    else Subtype.val '' (m.branchSet (idx i hi))
  refine ⟨{ branchSet := bs, nonempty := ?_, disjoint := ?_,
             connected := ?_, adjacent := ?_ }⟩
  · -- Nonempty
    intro i; dsimp only [bs]
    split
    · exact ⟨v, rfl⟩
    · rename_i hi
      obtain ⟨w, hw⟩ := m.nonempty (idx i hi)
      exact ⟨w.val, Set.mem_image_of_mem _ hw⟩
  · -- Disjoint
    intro i j hij
    simp only [bs]
    rw [Set.disjoint_left]
    intro u hui huj
    split at hui <;> split at huj
    case isTrue.isTrue hi hj =>
      exact hij (Fin.ext (by omega))
    case isTrue.isFalse hi hj =>
      rw [Set.mem_singleton_iff] at hui
      obtain ⟨⟨w, hw_nbr⟩, _, hw_eq⟩ := huj
      -- w ∈ G.neighborSet v and w = u = v, giving G.Adj v v
      simp only [Subtype.coe_mk] at hw_eq
      rw [hui] at hw_eq
      rw [hw_eq] at hw_nbr
      exact G.irrefl hw_nbr
    case isFalse.isTrue hi hj =>
      rw [Set.mem_singleton_iff] at huj
      obtain ⟨⟨w, hw_nbr⟩, _, hw_eq⟩ := hui
      simp only [Subtype.coe_mk] at hw_eq
      rw [huj] at hw_eq
      rw [hw_eq] at hw_nbr
      exact G.irrefl hw_nbr
    case isFalse.isFalse hi hj =>
      obtain ⟨⟨wi, hwi_nbr⟩, hwi_bs, rfl⟩ := hui
      obtain ⟨⟨wj, hwj_nbr⟩, hwj_bs, hwij⟩ := huj
      -- hwij : wj = wi (as V-elements), so the subtypes are equal
      have hsub : (⟨wj, hwj_nbr⟩ : G.neighborSet v) = ⟨wi, hwi_nbr⟩ :=
        Subtype.ext hwij
      rw [hsub] at hwj_bs
      -- Now hwi_bs and hwj_bs place ⟨wi, hwi_nbr⟩ in both branch sets
      have hne : idx i hi ≠ idx j hj := by
        intro heq; apply hij
        have := congr_arg Fin.val heq
        simp only [idx] at this
        exact Fin.ext (by omega)
      exact (m.disjoint _ _ hne).ne_of_mem hwi_bs hwj_bs rfl
  · -- Connected
    intro i; dsimp only [bs]
    by_cases hi : i.val = 0
    · rw [dif_pos hi]
      haveI : Nonempty ({v} : Set V) := ⟨⟨v, rfl⟩⟩
      haveI : Subsingleton ({v} : Set V) := Unique.instSubsingleton
      exact Connected.of_subsingleton
    · rw [dif_neg hi]
      exact image_connected (G.neighborSet v) (m.branchSet (idx i hi)) (m.connected (idx i hi))
  · -- Adjacent
    intro i j hadj_kh
    dsimp only [bs]
    have hij : i ≠ j := hadj_kh.ne
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
      <;> simp only [hi, hj, dite_true, dite_false]
    · exact absurd (Fin.ext (by omega)) hij
    · -- i=0 maps to {v}, j>0 maps to image of branch set ⊂ N(v)
      obtain ⟨w, hw⟩ := m.nonempty (idx j hj)
      -- w : G.neighborSet v, so w.prop : G.Adj v w.val  (since neighborSet v = {u | G.Adj v u})
      exact ⟨v, rfl, w.val, Set.mem_image_of_mem _ hw, w.prop⟩
    · -- symmetric
      obtain ⟨w, hw⟩ := m.nonempty (idx i hi)
      exact ⟨w.val, Set.mem_image_of_mem _ hw, v, rfl, w.prop.symm⟩
    · -- Both > 0: use adjacency from m
      have hadj' : (completeGraph (Fin (h - 1))).Adj (idx i hi) (idx j hj) := by
        simp only [completeGraph, ne_eq]
        intro heq; apply hij
        have := congr_arg Fin.val heq
        simp only [idx] at this
        exact Fin.ext (by omega)
      obtain ⟨w₁, hw₁, w₂, hw₂, hadj_ind⟩ := m.adjacent _ _ hadj'
      exact ⟨w₁.val, Set.mem_image_of_mem _ hw₁,
             w₂.val, Set.mem_image_of_mem _ hw₂, hadj_ind⟩

/-! ### Neighborhood density helpers -/

/-- An induced subgraph `G.induce s` is a minor of `G`. The branch sets are singletons.
(This is also proved in `Mader.lean` as `induce_isMinor`, but we include a copy here
to avoid a circular import.) -/
private theorem induce_isMinor_local (G : SimpleGraph V)
    (s : Set V) : (G.induce s) ≤m G := by
  constructor
  refine {
    branchSet := fun v => {v.val}
    nonempty := fun v => Set.singleton_nonempty v.val
    disjoint := fun v1 v2 hne => by
      simp only [Set.disjoint_singleton]
      exact fun h => hne (Subtype.val_injective h)
    connected := fun v => ?_
    adjacent := fun v1 v2 hadj =>
      ⟨v1.val, rfl, v2.val, rfl, hadj⟩
  }
  haveI : Nonempty ({v.val} : Set V) := (Set.singleton_nonempty v.val).to_subtype
  haveI : Subsingleton ({v.val} : Set V) := Unique.instSubsingleton
  exact Connected.of_subsingleton

/-- Removing a vertex of degree < t from a graph with avg degree ≥ 2t preserves
the average degree condition. -/
private lemma remove_low_degree_preserves_avg (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (v : V) (hv : G.degree v < t)
    (havg : 2 * t * Fintype.card V ≤ 2 * G.edgeFinset.card) :
    2 * t * Fintype.card ({v}ᶜ : Set V) ≤
      2 * (G.induce ({v}ᶜ : Set V)).edgeFinset.card := by
  rw [Fintype.card_compl_set, Set.card_singleton]
  rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
  have hle : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  zify [hle, hV] at *; nlinarith

/-- Auxiliary for `avg_degree_implies_min_degree`: induction on the card bound `n`.
The statement is universe-polymorphic in V' so the recursive call (on a subtype)
can instantiate V' to a different type. -/
private theorem avg_degree_implies_min_degree_aux :
    ∀ (n : ℕ) (t : ℕ)
    (V' : Type u_1) [Fintype V'] [DecidableEq V']
    (G' : SimpleGraph V') [DecidableRel G'.Adj],
    Fintype.card V' ≤ n →
    0 < Fintype.card V' →
    2 * t * Fintype.card V' ≤ 2 * G'.edgeFinset.card →
    ∃ (V'' : Type u_1) (_ : Fintype V'') (_ : DecidableEq V'')
      (G'' : SimpleGraph V'') (_ : DecidableRel G''.Adj),
      0 < Fintype.card V'' ∧
      (∀ w : V'', t ≤ G''.degree w) ∧
      (2 * t * Fintype.card V'' ≤ 2 * G''.edgeFinset.card) ∧
      (∀ h : ℕ, G'.IsKMinorFree h → G''.IsKMinorFree h) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t V' _ _ G' _ hn hV' havg
  by_cases hmin : ∀ w : V', t ≤ G'.degree w
  · exact ⟨V', inferInstance, inferInstance, G', inferInstance, hV', hmin, havg,
      fun _ hf => hf⟩
  · push_neg at hmin
    obtain ⟨v₀, hv₀⟩ := hmin
    -- |V'| ≥ 2 (if |V'| = 1, then t > deg ≥ 0 forces t ≥ 1, but 2t ≤ 2|E| and |E| = 0 for 1 vertex)
    have hV'_ge2 : 2 ≤ Fintype.card V' := by
      by_contra hlt; push_neg at hlt
      have hle1 : Fintype.card V' ≤ 1 := by omega
      have hcard1 : Fintype.card V' = 1 := by omega
      have hd : G'.degree v₀ = 0 := by have := G'.degree_lt_card_verts v₀; omega
      have hedge0 : G'.edgeFinset.card = 0 := by
        have hhs := G'.sum_degrees_eq_twice_card_edges
        have huniq : ∀ w : V', w = v₀ :=
          fun w => Fintype.card_le_one_iff.mp hle1 w v₀
        have hsum1 : (Finset.univ : Finset V').sum (fun v => G'.degree v) = G'.degree v₀ := by
          conv_lhs => rw [show (Finset.univ : Finset V') = {v₀} from by
            ext w; simp [huniq w]]
          simp
        omega
      -- Now: 2*t*1 ≤ 2*0, so t = 0, but G'.degree v₀ = 0 ≥ t = 0, contradiction
      have ht0 : t = 0 := by rw [hcard1] at havg; omega
      exact absurd (ht0 ▸ Nat.zero_le (G'.degree v₀)) (not_le.mpr hv₀)
    have hcard_compl_pos : 0 < Fintype.card ({v₀}ᶜ : Set V') := by
      rw [Fintype.card_compl_set, Set.card_singleton]; omega
    have hcard_compl_lt : Fintype.card ({v₀}ᶜ : Set V') < n := by
      rw [Fintype.card_compl_set, Set.card_singleton]; omega
    have havg' := remove_low_degree_preserves_avg G' t v₀ hv₀ havg
    obtain ⟨V'', _, _, G'', _, hV'', hmin'', havg'', htrans''⟩ :=
      ih _ hcard_compl_lt t ({v₀}ᶜ : Set V') (G'.induce ({v₀}ᶜ : Set V'))
        (le_refl _) hcard_compl_pos havg'
    exact ⟨V'', inferInstance, inferInstance, G'', inferInstance, hV'', hmin'', havg'',
      fun h hfree => htrans'' h (IsHMinorFree.minor hfree (induce_isMinor_local G' _))⟩

/-- **Helper (degeneracy argument)**: Every graph with average degree ≥ 2t has a
subgraph with minimum degree ≥ t.

This is a classical result (Diestel, Proposition 1.2.2): repeatedly remove vertices
of degree < t. Each removal preserves the avg degree condition. The process
terminates because |V| decreases.

The transfer condition: if G is K_h-minor-free, then G' is too (because G' ≤m G
via `induce_isMinor_local` and minor-freeness is inherited by subgraphs). -/
lemma avg_degree_implies_min_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (hV : 0 < Fintype.card V)
    (havg : 2 * t * Fintype.card V ≤ 2 * G.edgeFinset.card) :
    ∃ (V' : Type u_1) (_ : Fintype V') (_ : DecidableEq V')
      (G' : SimpleGraph V') (_ : DecidableRel G'.Adj),
      0 < Fintype.card V' ∧
      (∀ v : V', t ≤ G'.degree v) ∧
      (2 * t * Fintype.card V' ≤ 2 * G'.edgeFinset.card) ∧
      (∀ h : ℕ, G.IsKMinorFree h → G'.IsKMinorFree h) :=
  avg_degree_implies_min_degree_aux (Fintype.card V) t V G (le_refl _) hV havg

/-- The degree of w in G[N(v)] equals the number of common neighbors of v and w.
This is a key identity connecting induced subgraph degree to common neighborhoods. -/
private lemma induce_neighborSet_degree_eq_card_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (w : G.neighborSet v) :
    (G.induce (G.neighborSet v)).degree w = Fintype.card (G.commonNeighbors v w) := by
  rw [← card_neighborSet_eq_degree]
  apply Fintype.card_of_bijective
    (f := fun (x : (G.induce (G.neighborSet v)).neighborSet w) =>
      (⟨x.val.val, by
        have hx := x.prop
        simp only [mem_neighborSet] at hx
        rw [mem_commonNeighbors]
        exact ⟨x.val.prop, hx⟩
      ⟩ : G.commonNeighbors v ↑w))
  refine ⟨fun a b heq => ?_, fun ⟨u, hu⟩ => ?_⟩
  · simp only [Subtype.mk.injEq] at heq
    exact Subtype.ext (Subtype.ext heq)
  · rw [mem_commonNeighbors] at hu
    exact ⟨⟨⟨u, hu.1⟩, by
      simp only [mem_neighborSet, comap_adj, Function.Embedding.subtype_apply]
      exact hu.2⟩, by simp⟩

/-- **Helper (common neighbors → induced degree)**: If v and w are adjacent and they
have at least t common neighbors, then w has degree ≥ t in G[N(v)].

This replaces the original `neighborhood_min_degree_bound` which was FALSE as stated.
The correct version uses the common-neighbors hypothesis directly. -/
lemma commonNeighbors_implies_induced_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (t : ℕ)
    (w : G.neighborSet v)
    (hcn : t ≤ Fintype.card (G.commonNeighbors v w)) :
    t ≤ (G.induce (G.neighborSet v)).degree w := by
  rw [induce_neighborSet_degree_eq_card_commonNeighbors]
  exact hcn

/-- **Step 2 (neighborhood density)**: If v has degree >= 2^(h-2) and h >= 3,
and every vertex in N(v) has degree >= 2^(h-1-2) in the induced subgraph G[N(v)]
(the `hmin_induced` hypothesis), then G[N(v)] satisfies the average degree
condition for K_{h-1}, i.e., `2^(h-1-2) * |N(v)| <= 2 * |E(G[N(v)])|`.

The previous version (without `hmin_induced`) was **FALSE** -- a star K_{1,n}
is a counterexample. The added hypothesis is provable from Diestel's proof
structure: first extract a minimal dense subgraph (via `avg_degree_implies_min_degree`),
then use `neighborhood_min_degree_bound` to get the per-vertex lower bound.

**Proof**: By handshaking (`sum_degrees_eq_twice_card_edges`), we have
`sum_{w in N(v)} deg_{G[N(v)]}(w) = 2|E(G[N(v)])|`. The hypothesis `hmin_induced`
gives each summand >= 2^(h-1-2), so `|N(v)| * 2^(h-1-2) <= sum = 2|E|`.
Fully proved using `Finset.card_nsmul_le_sum`. -/
private lemma neighborhood_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (h : ℕ) (hh3 : 3 ≤ h)
    (hdeg : 2 ^ (h - 2) ≤ G.degree v)
    (hmin_induced : ∀ w : G.neighborSet v,
      2 ^ (h - 1 - 2) ≤ (G.induce (G.neighborSet v)).degree w) :
    let Nv := G.neighborSet v
    2 ^ (h - 1 - 2) * Fintype.card Nv ≤
      2 * (G.induce Nv).edgeFinset.card := by
  intro Nv
  -- Handshaking: sum of degrees = 2|E|
  have hshake := SimpleGraph.sum_degrees_eq_twice_card_edges (G.induce Nv)
  -- Lower bound on sum using hmin_induced
  have hsum : (Finset.univ : Finset Nv).card • (2 ^ (h - 1 - 2)) ≤
      (Finset.univ : Finset Nv).sum (fun w => (G.induce Nv).degree w) := by
    apply Finset.card_nsmul_le_sum
    intro w _
    exact hmin_induced w
  rw [hshake, Finset.card_univ] at hsum
  -- hsum : Fintype.card Nv • 2^(h-1-2) ≤ 2 * edgeFinset.card
  -- goal : 2^(h-1-2) * Fintype.card Nv ≤ 2 * edgeFinset.card
  -- nsmul on Nat is just mul, and we need commutativity
  rw [smul_eq_mul, mul_comm] at hsum
  exact hsum

/-- **Step 2b (neighborhood nonempty)**: If v has degree ≥ 2^(h-2) and h ≥ 3,
then v has at least one neighbor (N(v) is nonempty). -/
private lemma neighborhood_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (h : ℕ) (hh3 : 3 ≤ h)
    (hdeg : 2 ^ (h - 2) ≤ G.degree v) :
    0 < Fintype.card (G.neighborSet v) := by
  rw [G.card_neighborSet_eq_degree]
  exact lt_of_lt_of_le (by positivity) hdeg

/-! ### Edge contraction infrastructure (Diestel §7.2)

Edge contraction is the key operation needed for the common-neighbours bound:
in a ε-minimal minor, contracting any edge {s,t} produces a minor with
|E| - 1 - |CN(s,t)| edges, and by minimality this forces |CN(s,t)| ≥ k. -/

/-- **Edge contraction**: contract edge `{s, t}` by merging `s` into `t`.
The result lives on vertex type `({s}ᶜ : Set V)`: vertex `t` inherits the
union `N(s) ∪ N(t)` of neighbourhoods, all other adjacencies are unchanged,
and vertex `s` is deleted. -/
noncomputable def contractAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hadj : G.Adj s t) : SimpleGraph ({s}ᶜ : Set V) where
  Adj v w :=
    v ≠ w ∧
    ((v.val = t ∧ (G.Adj t w.val ∨ G.Adj s w.val)) ∨
     (w.val = t ∧ (G.Adj v.val t ∨ G.Adj v.val s)) ∨
     (v.val ≠ t ∧ w.val ≠ t ∧ G.Adj v.val w.val))
  symm v w := by
    intro ⟨hne, h⟩; refine ⟨hne.symm, ?_⟩
    rcases h with ⟨rfl, hor⟩ | ⟨rfl, hor⟩ | ⟨hv, hw, ha⟩
    · exact Or.inr (Or.inl ⟨rfl, hor.imp G.adj_symm G.adj_symm⟩)
    · exact Or.inl ⟨rfl, hor.imp G.adj_symm G.adj_symm⟩
    · exact Or.inr (Or.inr ⟨hw, hv, ha.symm⟩)
  loopless := ⟨fun v ⟨h, _⟩ => h rfl⟩

/-- `contractAdj` has decidable adjacency. -/
noncomputable instance contractAdj_decidableRel (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hadj : G.Adj s t) :
    DecidableRel (G.contractAdj s t hadj).Adj := by
  intro v w; unfold contractAdj; exact inferInstance

/-- **Edge contraction is a minor**: `G.contractAdj s t hadj` is a minor of `G`.

Branch sets: `{s, t}` for vertex `t` (the merged vertex), `{v}` for other `v ≠ s`.
Connected: `{s,t}` is connected via the edge `G.Adj s t`.
Adjacent: follows from the definition of `contractAdj`. -/
-- Helper: branch sets for the contraction minor model
private def contractBranchSet (s t : V) (v : ({s}ᶜ : Set V)) : Set V :=
  if v.val = t then {s, t} else {v.val}

private theorem contractAdj_isMinor (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hadj : G.Adj s t) :
    (G.contractAdj s t hadj) ≤m G := by
  have hne : s ≠ t := hadj.ne
  refine ⟨{
    branchSet := contractBranchSet s t
    nonempty := fun v => by
      unfold contractBranchSet
      split
      · exact ⟨s, Set.mem_insert s _⟩
      · exact ⟨v.val, rfl⟩
    disjoint := fun v₁ v₂ hne₁₂ => by
      unfold contractBranchSet
      rw [Set.disjoint_iff]; intro u ⟨hu₁, hu₂⟩
      split_ifs at hu₁ hu₂ with h₁ h₂ h₂
      · exact (hne₁₂ (Subtype.ext (h₁.trans h₂.symm))).elim
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu₁
        simp only [Set.mem_singleton_iff] at hu₂
        rcases hu₁ with rfl | rfl <;> [exact v₂.prop hu₂.symm; exact h₂ hu₂.symm]
      · simp only [Set.mem_singleton_iff] at hu₁
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu₂
        rcases hu₂ with rfl | rfl <;> [exact v₁.prop hu₁.symm; exact h₁ hu₁.symm]
      · simp only [Set.mem_singleton_iff] at hu₁ hu₂
        exact (hne₁₂ (Subtype.ext (hu₁.symm.trans hu₂))).elim
    connected := fun v => by
      unfold contractBranchSet
      by_cases hvt : v.val = t
      · rw [if_pos hvt, connected_iff_exists_forall_reachable]
        refine ⟨⟨s, Set.mem_insert s _⟩, fun ⟨w, hw⟩ => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact Reachable.refl _
        · refine ⟨Walk.cons ?_ Walk.nil⟩
          exact hadj
      · rw [if_neg hvt]
        haveI : Nonempty ({v.val} : Set V) := ⟨⟨v.val, rfl⟩⟩
        haveI : Subsingleton ({v.val} : Set V) := Set.subsingleton_singleton.coe_sort
        exact Connected.of_subsingleton
    adjacent := fun v₁ v₂ ha => by
      unfold contractBranchSet
      obtain ⟨hne₁₂, h_adj⟩ := ha
      rcases h_adj with ⟨h₁, hor⟩ | ⟨h₂, hor⟩ | ⟨hne₁, hne₂, hadj'⟩
      · -- v₁.val = t
        have hv₂ne : v₂.val ≠ t := fun heq => hne₁₂ (Subtype.ext (h₁.trans heq.symm))
        simp only [h₁, ↓reduceIte, hv₂ne]
        rcases hor with hadj' | hadj'
        · exact ⟨t, Set.mem_insert_of_mem s rfl, v₂.val, rfl, hadj'⟩
        · exact ⟨s, Set.mem_insert s _, v₂.val, rfl, hadj'⟩
      · -- v₂.val = t
        have hv₁ne : v₁.val ≠ t := fun heq => hne₁₂ (Subtype.ext (heq.trans h₂.symm))
        simp only [hv₁ne, ↓reduceIte, h₂]
        rcases hor with hadj' | hadj'
        · exact ⟨v₁.val, rfl, t, Set.mem_insert_of_mem s rfl, hadj'⟩
        · exact ⟨v₁.val, rfl, s, Set.mem_insert s _, hadj'⟩
      · -- neither is t
        simp only [hne₁, ↓reduceIte, hne₂]
        exact ⟨v₁.val, rfl, v₂.val, rfl, hadj'⟩
  }⟩

/-- The vertex type of `contractAdj` has one fewer vertex than `V`. -/
private lemma card_contractAdj_vertices (s : V) :
    Fintype.card ({s}ᶜ : Set V) = Fintype.card V - 1 := by
  rw [Fintype.card_compl_set, Set.card_singleton]

/-- **Edge count for contraction**:
`|E(G/st)| + 1 + |CN(s,t)| = |E(G)|`.

Equivalently, `|E(G/st)| = |E(G)| - 1 - |CN(s,t)|`: the contraction removes
exactly the edge `{s,t}` and one copy of each edge `{s,u}` for `u ∈ CN(s,t)`. -/
private lemma card_edgeFinset_contractAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hadj : G.Adj s t) (hne : s ≠ t) :
    (G.contractAdj s t hadj).edgeFinset.card + 1 +
      Fintype.card (G.commonNeighbors s t) = G.edgeFinset.card := by
  -- We partition G.edgeFinset into "dropped" edges and a bijective image of contractAdj edges.
  -- Dropped = {s(s,t)} ∪ {s(s,u) | u ∈ CN(s,t)}: the contracted edge + one copy per common nbr.
  set G' := G.contractAdj s t hadj with hG'_def
  set CN := (G.commonNeighbors s t).toFinset with hCN_def
  set cn_edges := CN.image (fun u => s(s, u)) with hcn_edges_def
  set dropped := ({s(s, t)} : Finset (Sym2 V)) ∪ cn_edges with hdropped_def
  -- Key facts about CN
  have hCN_card : CN.card = Fintype.card (G.commonNeighbors s t) := Set.toFinset_card _
  have hs_not_cn : s ∉ CN := by simp [CN, Set.mem_toFinset, mem_commonNeighbors]
  have ht_not_cn : t ∉ CN := by simp [CN, Set.mem_toFinset, mem_commonNeighbors]
  -- cn_edges injection: s(s, u₁) = s(s, u₂) → u₁ = u₂ for u_i ∈ CN (since u_i ≠ s)
  have hcn_inj : Set.InjOn (fun u => s(s, u)) ↑CN := by
    intro u₁ hu₁ u₂ hu₂ heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hu₁ (by simpa using hs_not_cn)
  have hcn_card : cn_edges.card = CN.card :=
    Finset.card_image_of_injOn hcn_inj
  -- Disjointness: s(s,t) ∉ cn_edges (because t ∉ CN)
  have hst_not_cn : s(s, t) ∉ cn_edges := by
    simp only [hcn_edges_def, Finset.mem_image]
    rintro ⟨u, hu, heq⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hu ht_not_cn
    · exact absurd hu hs_not_cn
  have hdisj : Disjoint ({s(s, t)} : Finset (Sym2 V)) cn_edges := by
    rwa [Finset.disjoint_singleton_left]
  -- |dropped| = 1 + |CN|
  have hdropped_card : dropped.card = 1 + Fintype.card (G.commonNeighbors s t) := by
    rw [hdropped_def, Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
        hcn_card, hCN_card]
  -- dropped ⊆ G.edgeFinset
  have hdropped_sub : dropped ⊆ G.edgeFinset := by
    intro e he
    rw [hdropped_def, Finset.mem_union] at he
    rcases he with he | he
    · rw [Finset.mem_singleton.mp he, mem_edgeFinset, mem_edgeSet]
      exact hadj
    · rw [hcn_edges_def, Finset.mem_image] at he
      obtain ⟨u, hu, rfl⟩ := he
      rw [mem_edgeFinset, mem_edgeSet]
      rw [Set.mem_toFinset, mem_commonNeighbors] at hu
      exact hu.1
  -- The main step: build a bijection G.edgeFinset \ dropped ↔ G'.edgeFinset.
  -- Define σ : V → {s}ᶜ by σ(s) = t, σ(v) = v for v ≠ s; then φ = Sym2.map σ.
  have hts : t ∈ ({s}ᶜ : Set V) := Set.mem_compl (by simp [hne.symm])
  let σ : V → ({s}ᶜ : Set V) := fun v =>
    if h : v = s then ⟨t, hts⟩ else ⟨v, Set.mem_compl (by simp [h])⟩
  have hσ_val_s : (σ s).val = t := by simp [σ, dif_pos rfl]
  have hσ_val_ne : ∀ v, v ≠ s → (σ v).val = v := by
    intro v hv; simp [σ, dif_neg hv]
  let φ : Sym2 V → Sym2 ({s}ᶜ : Set V) := Sym2.map σ
  -- f = Subtype.val ∘ σ : V → V maps s↦t, v↦v
  -- Used to reduce Sym2.map σ equalities to V-level equalities
  have hf_s : (Subtype.val ∘ σ) s = t := hσ_val_s
  have hf_ne : ∀ v, v ≠ s → (Subtype.val ∘ σ) v = v := hσ_val_ne
  have hf_eq_cases : ∀ x y, (Subtype.val ∘ σ) x = (Subtype.val ∘ σ) y →
      x = y ∨ (x = s ∧ y = t) ∨ (x = t ∧ y = s) := by
    intro x y h
    by_cases hxs : x = s
    · rw [hxs, hf_s] at h
      by_cases hys : y = s
      · left; exact hxs.trans hys.symm
      · rw [hf_ne y hys] at h; right; left; exact ⟨hxs, h.symm⟩
    · rw [hf_ne x hxs] at h
      by_cases hys : y = s
      · rw [hys, hf_s] at h; right; right; exact ⟨h, hys⟩
      · rw [hf_ne y hys] at h; left; exact h
  -- The bijection via Finset.card_bij
  have hbij : (G.edgeFinset \ dropped).card = G'.edgeFinset.card := by
    apply Finset.card_bij (fun a _ => φ a)
    · -- maps_to: φ sends G.edgeFinset \ dropped into G'.edgeFinset
      intro a ha
      rw [Finset.mem_sdiff] at ha; obtain ⟨ha_mem, ha_not⟩ := ha
      rw [mem_edgeFinset] at ha_mem ⊢
      revert ha_mem ha_not
      refine Sym2.ind (fun v w ha_adj ha_not => ?_) a
      rw [mem_edgeSet] at ha_adj
      change Sym2.map σ s(v, w) ∈ G'.edgeSet
      rw [Sym2.map_pair_eq, mem_edgeSet, hG'_def]
      have hvw : v ≠ w := ha_adj.ne
      have hσ_ne_vw : σ v ≠ σ w := by
        intro heq
        have hval := congr_arg Subtype.val heq
        rcases hf_eq_cases v w hval with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hvw rfl
        · apply ha_not; rw [hdropped_def]
          exact Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl)
        · apply ha_not; rw [hdropped_def]
          exact Finset.mem_union_left _ (Finset.mem_singleton.mpr Sym2.eq_swap)
      refine ⟨hσ_ne_vw, ?_⟩
      by_cases hvs : v = s
      · -- v = s: σ v = ⟨t,...⟩
        have hws : w ≠ s := fun h => hvw (hvs.trans h.symm)
        left; constructor
        · show (σ v).val = t; rw [hvs]; exact hσ_val_s
        · right; show G.Adj s (σ w).val
          rw [hσ_val_ne w hws]; exact hvs ▸ ha_adj
      · by_cases hws : w = s
        · -- w = s: σ w = ⟨t,...⟩
          right; left; constructor
          · show (σ w).val = t; rw [hws]; exact hσ_val_s
          · right; show G.Adj (σ v).val s
            rw [hσ_val_ne v hvs]; exact hws ▸ ha_adj
        · -- Neither v nor w is s
          by_cases hvt : v = t
          · left; constructor
            · show (σ v).val = t; rw [hσ_val_ne v hvs]; exact hvt
            · left; show G.Adj t (σ w).val
              rw [hσ_val_ne w hws]; exact hvt ▸ ha_adj
          · by_cases hwt : w = t
            · right; left; constructor
              · show (σ w).val = t; rw [hσ_val_ne w hws]; exact hwt
              · left; show G.Adj (σ v).val t
                rw [hσ_val_ne v hvs]; exact hwt ▸ ha_adj
            · right; right
              exact ⟨by show (σ v).val ≠ t; rw [hσ_val_ne v hvs]; exact hvt,
                by show (σ w).val ≠ t; rw [hσ_val_ne w hws]; exact hwt,
                by show G.Adj (σ v).val (σ w).val
                   rw [hσ_val_ne v hvs, hσ_val_ne w hws]; exact ha_adj⟩
    · -- inj: φ is injective on G.edgeFinset \ dropped
      intro a₁ ha₁ a₂ ha₂ hφ_eq
      rw [Finset.mem_sdiff] at ha₁ ha₂
      by_contra hne_a
      -- Lift to V-level
      have hfval : Sym2.map (Subtype.val ∘ σ) a₁ = Sym2.map (Subtype.val ∘ σ) a₂ := by
        rw [← Sym2.map_map, ← Sym2.map_map]; exact congr_arg _ hφ_eq
      obtain ⟨v₁, w₁, rfl⟩ := Sym2.exists.mp ⟨a₁, rfl⟩
      obtain ⟨v₂, w₂, rfl⟩ := Sym2.exists.mp ⟨a₂, rfl⟩
      simp only [Sym2.map_pair_eq, Function.comp_apply] at hfval
      rw [Sym2.eq_iff] at hfval
      rw [mem_edgeFinset, mem_edgeSet] at ha₁ ha₂
      -- Helpers for dropped membership
      have hcn_drop : ∀ x y, x = s → G.Adj s y → G.Adj t y → s(x, y) ∈ dropped := by
        intro x y hx hs_y ht_y; rw [hx, hdropped_def]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,
          Set.mem_toFinset.mpr (G.mem_commonNeighbors.mpr ⟨hs_y, ht_y⟩), rfl⟩)
      have hcn_drop' : ∀ x y, y = s → G.Adj s x → G.Adj t x → s(x, y) ∈ dropped := by
        intro x y hy hs_x ht_x; rw [hy, Sym2.eq_swap, hdropped_def]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,
          Set.mem_toFinset.mpr (G.mem_commonNeighbors.mpr ⟨hs_x, ht_x⟩), rfl⟩)
      have hst_drop : ∀ x y, x = s → y = t → s(x, y) ∈ dropped := by
        intro x y hx hy; rw [hx, hy, hdropped_def]
        exact Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl)
      -- Process case analysis. For each pair equality from hf_eq_cases,
      -- either the endpoints match (giving a₁ = a₂, contradiction),
      -- or one is {s,t}, giving dropped membership (contradiction) or a loop.
      -- We use a uniform handler for the {s,t} collapse cases.
      -- Given hx : x₁ = s, hy : y₁ = t (or vice versa), and the adj hypotheses,
      -- derive contradiction.
      -- Helper to handle the case analysis uniformly
      -- For each pair of equalities from Sym2.eq_iff, we get 2 endpoint-pair equalities.
      -- From hf_eq_cases on each, the "x = y" case gives matching endpoints.
      -- The "{s,t}" cases give dropped/loop contradictions.
      -- Suffices: a uniform lemma that given matching f-images of two edge pairs,
      -- either the pairs are equal (as Sym2) or we get a contradiction.
      suffices hsuff : ∀ x₁ y₁ x₂ y₂ : V,
          G.Adj x₁ y₁ → s(x₁, y₁) ∉ dropped →
          G.Adj x₂ y₂ → s(x₂, y₂) ∉ dropped →
          (Subtype.val ∘ σ) x₁ = (Subtype.val ∘ σ) x₂ →
          (Subtype.val ∘ σ) y₁ = (Subtype.val ∘ σ) y₂ →
          s(x₁, y₁) = s(x₂, y₂) by
        rcases hfval with ⟨hv, hw⟩ | ⟨hc1, hc2⟩
        · exact hne_a (hsuff v₁ w₁ v₂ w₂ ha₁.1 ha₁.2 ha₂.1 ha₂.2 hv hw)
        · have ha₂' : s(w₂, v₂) ∉ dropped := Sym2.eq_swap ▸ ha₂.2
          exact hne_a ((hsuff v₁ w₁ w₂ v₂ ha₁.1 ha₁.2 ha₂.1.symm ha₂'
            hc1 hc2).trans Sym2.eq_swap)
      -- Prove the suffices: 9 cases from 3×3 of hf_eq_cases
      intro x₁ y₁ x₂ y₂ hadj₁ hnot₁ hadj₂ hnot₂ hfx hfy
      rcases hf_eq_cases x₁ x₂ hfx with rfl | ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · -- x₁ = x₂ (x₂ eliminated, use x₁ for both)
        rcases hf_eq_cases y₁ y₂ hfy with rfl | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
        · rfl
        · -- y₁ = s, y₂ = t. s(x₁, s) ∈ dropped via CN
          exfalso; exact hnot₁ (hcn_drop' x₁ y₁ hy1 (hy1 ▸ hadj₁.symm) (hy2 ▸ hadj₂.symm))
        · -- y₁ = t, y₂ = s. s(x₁, s) ∈ dropped
          exfalso; exact hnot₂ (hcn_drop' x₁ y₂ hy2 (hy2 ▸ hadj₂.symm) (hy1 ▸ hadj₁.symm))
      · -- x₁ = s, x₂ = t
        rcases hf_eq_cases y₁ y₂ hfy with rfl | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
        · -- y₁ = y₂ (y₂ eliminated). s(s, y₁) ∈ dropped via CN
          exfalso; exact hnot₁ (hcn_drop x₁ y₁ hx1 (hx1 ▸ hadj₁) (hx2 ▸ hadj₂))
        · -- y₁ = s, y₂ = t → s(s,s) loop
          exfalso; rw [hx1, hy1] at hadj₁; exact absurd hadj₁ G.irrefl
        · -- y₁ = t, y₂ = s → s(s,t) ∈ dropped
          exfalso; exact hnot₁ (hst_drop x₁ y₁ hx1 hy1)
      · -- x₁ = t, x₂ = s
        rcases hf_eq_cases y₁ y₂ hfy with rfl | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
        · -- y₁ = y₂. s(s, y₁) ∈ dropped via CN
          exfalso; exact hnot₂ (hcn_drop x₂ y₁ hx2 (hx2 ▸ hadj₂) (hx1 ▸ hadj₁))
        · -- y₁ = s, y₂ = t → s(s,t) ∈ dropped
          exfalso; exact hnot₂ (hst_drop x₂ y₂ hx2 hy2)
        · -- y₁ = t, y₂ = s → s(s,s) loop
          exfalso; rw [hx2, hy2] at hadj₂; exact absurd hadj₂ G.irrefl
    · -- surj: every G'.edge has a preimage in G.edgeFinset \ dropped
      intro b hb
      rw [mem_edgeFinset] at hb
      -- Decompose b = s(v, w) with v, w : {s}ᶜ
      revert hb
      refine Sym2.ind (fun v w hb => ?_) b
      rw [mem_edgeSet, hG'_def] at hb
      obtain ⟨hne_vw, hadj_cases⟩ := hb
      -- For each case, find the preimage
      -- Helper: given endpoint values, build the preimage edge and verify
      -- The preimage for endpoints (a, c) where a, c ≠ s:
      -- φ(s(a, c)) = s(σ a, σ c) = s(⟨a,...⟩, ⟨c,...⟩)
      -- We need σ a = v and σ c = w (as elements of {s}ᶜ).
      -- For a ≠ s: σ a = ⟨a,...⟩, so (σ a).val = a.
      -- For a = s: σ s = ⟨t,...⟩, so (σ s).val = t.
      -- So to get (σ a).val = v.val: if v.val ≠ t, pick a = v.val (≠ s since v ∈ {s}ᶜ).
      -- If v.val = t: pick a = t (giving σ t = ⟨t,...⟩) if G.Adj t w.val,
      --              or a = s (giving σ s = ⟨t,...⟩) if G.Adj s w.val.
      -- The key: after choosing the right a and c, show φ(s(a,c)) = s(v,w)
      -- by showing σ a = v and σ c = w as Subtypes (via Subtype.ext).
      -- We handle based on contractAdj cases.
      have htns : t ≠ s := hne.symm
      -- Helper: show φ(s(a, b)) = s(v, w) by Subtype.ext on each endpoint
      have hφ_eq_mk : ∀ a b : V, (σ a).val = v.val → (σ b).val = w.val →
          φ s(a, b) = s(v, w) := by
        intro a b ha hb; show Sym2.map σ s(a, b) = s(v, w)
        rw [Sym2.map_pair_eq]; exact congr_arg₂ _ (Subtype.ext ha) (Subtype.ext hb)
      -- Helper: edge s(x, y) ∉ dropped when x ≠ s and y ≠ s
      have hne_not_drop : ∀ x y : V, x ≠ s → y ≠ s → s(x, y) ∉ dropped := by
        intro x y hx hy hmem
        rw [hdropped_def, Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · rw [Finset.mem_singleton] at hmem
          rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> contradiction
        · rw [hcn_edges_def, Finset.mem_image] at hmem
          obtain ⟨u, _, heq⟩ := hmem
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> contradiction
      -- Helper: s(s, y) ∉ dropped when ¬G.Adj t y and y ≠ t
      have hs_not_drop : ∀ y : V, y ≠ t → ¬G.Adj t y → s(s, y) ∉ dropped := by
        intro y hyt hntadj hmem
        rw [hdropped_def, Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · rw [Finset.mem_singleton] at hmem
          rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, rfl⟩ | ⟨rfl, _⟩
          · exact hyt rfl
          · exact hne rfl
        · rw [hcn_edges_def, Finset.mem_image] at hmem
          obtain ⟨u, hu, heq⟩ := hmem
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
          · rw [Set.mem_toFinset, G.mem_commonNeighbors] at hu; exact hntadj hu.2
          · exact hs_not_cn hu
      rcases hadj_cases with ⟨hvt, hor⟩ | ⟨hwt, hor⟩ | ⟨hvnt, hwnt, hadj_orig⟩
      · -- Case 1: v.val = t
        have hwns : (w : V) ≠ s := w.prop
        have hwv : w.val ≠ t := fun h => hne_vw (Subtype.ext (hvt.trans h.symm))
        by_cases htw : G.Adj t w.val
        · exact ⟨s(t, w.val), Finset.mem_sdiff.mpr
            ⟨mem_edgeFinset.mpr ((G.mem_edgeSet).mpr htw), hne_not_drop t w.val htns hwns⟩,
            hφ_eq_mk t w.val (by rw [hσ_val_ne t htns]; exact hvt.symm)
              (by rw [hσ_val_ne w.val hwns])⟩
        · exact ⟨s(s, w.val), Finset.mem_sdiff.mpr
            ⟨mem_edgeFinset.mpr ((G.mem_edgeSet).mpr (hor.resolve_left htw)),
             hs_not_drop w.val hwv htw⟩,
            hφ_eq_mk s w.val (by rw [hσ_val_s]; exact hvt.symm)
              (by rw [hσ_val_ne w.val hwns])⟩
      · -- Case 2: w.val = t (symmetric)
        have hvns : (v : V) ≠ s := v.prop
        have hvw : v.val ≠ t := fun h => hne_vw (Subtype.ext (h.trans hwt.symm))
        by_cases htv : G.Adj t v.val
        · exact ⟨s(v.val, t), Finset.mem_sdiff.mpr
            ⟨mem_edgeFinset.mpr ((G.mem_edgeSet).mpr htv.symm), hne_not_drop v.val t hvns htns⟩,
            hφ_eq_mk v.val t (by rw [hσ_val_ne v.val hvns])
              (by rw [hσ_val_ne t htns]; exact hwt.symm)⟩
        · have hsv : G.Adj s v.val := by
            rcases hor with h | h
            · exfalso; exact absurd h.symm htv
            · exact h.symm
          refine ⟨s(v.val, s), Finset.mem_sdiff.mpr
            ⟨mem_edgeFinset.mpr ((G.mem_edgeSet).mpr hsv.symm), ?_⟩,
            hφ_eq_mk v.val s (by rw [hσ_val_ne v.val hvns])
              (by rw [hσ_val_s]; exact hwt.symm)⟩
          rw [Sym2.eq_swap]; exact hs_not_drop v.val hvw htv
      · -- Case 3: v.val ≠ t, w.val ≠ t, G.Adj v.val w.val
        exact ⟨s(v.val, w.val), Finset.mem_sdiff.mpr
          ⟨mem_edgeFinset.mpr ((G.mem_edgeSet).mpr hadj_orig),
           hne_not_drop v.val w.val v.prop w.prop⟩,
          hφ_eq_mk v.val w.val (by rw [hσ_val_ne v.val v.prop])
            (by rw [hσ_val_ne w.val w.prop])⟩
  -- Conclude: use card_sdiff_add_card_eq_card
  have hfinal := Finset.card_sdiff_add_card_eq_card hdropped_sub
  linarith

/-- **Contraction preserves ε-density when CN is small**: If `|E(G)| ≥ k·|V|`
and `|CN(s,t)| < k`, then the contraction `G/{s,t}` has `|E'| ≥ k·(|V|-1)`. -/
private lemma contractAdj_preserves_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hadj : G.Adj s t) (hne : s ≠ t)
    (k : ℕ) (hε : k * Fintype.card V ≤ G.edgeFinset.card)
    (hcn : Fintype.card (G.commonNeighbors s t) < k) :
    k * Fintype.card ({s}ᶜ : Set V) ≤
      (G.contractAdj s t hadj).edgeFinset.card := by
  rw [card_contractAdj_vertices]
  -- heq: contract + 1 + CN = |E|.  hε: k*|V| ≤ |E|.  hcn: CN < k.
  -- Need: k * (|V| - 1) ≤ contract.
  -- k*(|V|-1) + 1 + CN ≤ k*(|V|-1) + k = k*|V| ≤ |E| = contract + 1 + CN.
  have heq := card_edgeFinset_contractAdj G s t hadj hne
  have hV1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hrewrite : k * (Fintype.card V - 1) + k = k * Fintype.card V := by
    nlinarith [Nat.sub_add_cancel hV1]
  linarith

/-- **Dense minors have the common-neighbours bound** (Diestel §7.2):
If `|E| ≥ k · |V|` and `|V| > 0`, then there exists a minor `G'` of `G`
(on vertex type `V'` in the same universe) satisfying:
  (1) `|E'| ≥ k · |V'|`
  (2) `|V'| > 0`
  (3) Every edge `{v, w}` of `G'` has `|CN(v,w)| ≥ k`
  (4) `K_h`-minor-freeness transfers from `G` to `G'`

Proved by well-founded induction on `|V|`: if some edge has `CN < k`,
contract it (the density is preserved) and recurse on a smaller vertex type. -/
private theorem exists_dense_minor_with_cn_bound :
    ∀ (n : ℕ) (k : ℕ)
    (V' : Type u_1) [Fintype V'] [DecidableEq V']
    (G' : SimpleGraph V') [DecidableRel G'.Adj],
    Fintype.card V' ≤ n →
    0 < Fintype.card V' →
    k * Fintype.card V' ≤ G'.edgeFinset.card →
    ∃ (V'' : Type u_1) (_ : Fintype V'') (_ : DecidableEq V'')
      (G'' : SimpleGraph V'') (_ : DecidableRel G''.Adj),
      0 < Fintype.card V'' ∧
      k * Fintype.card V'' ≤ G''.edgeFinset.card ∧
      (∀ v w : V'', G''.Adj v w → k ≤ Fintype.card (G''.commonNeighbors v w)) ∧
      (∀ h : ℕ, G'.IsKMinorFree h → G''.IsKMinorFree h) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k V' _ _ G' _ hn hV' hε
  -- Check if every edge already has CN ≥ k
  by_cases hcn : ∀ v w : V', G'.Adj v w → k ≤ Fintype.card (G'.commonNeighbors v w)
  · -- Already done
    exact ⟨V', inferInstance, inferInstance, G', inferInstance, hV', hε, hcn,
      fun _ hf => hf⟩
  · -- Some edge has CN < k; contract it
    push_neg at hcn
    obtain ⟨s, t, hadj, hlt⟩ := hcn
    have hne : s ≠ t := hadj.ne
    have hV'ge2 : 2 ≤ Fintype.card V' := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, ← Nat.lt_iff_add_one_le]
      exact Fintype.one_lt_card_iff.mpr ⟨s, t, hne⟩
    have hcard_pos : 0 < Fintype.card ({s}ᶜ : Set V') := by
      rw [card_contractAdj_vertices]; omega
    have hcard_lt : Fintype.card ({s}ᶜ : Set V') < n := by
      rw [card_contractAdj_vertices]; omega
    have hε' := contractAdj_preserves_density G' s t hadj hne k hε hlt
    obtain ⟨V'', _, _, G'', _, hV'', hε'', hcn'', htrans''⟩ :=
      ih _ hcard_lt k ({s}ᶜ : Set V')
        (G'.contractAdj s t hadj) (le_refl _) hcard_pos hε'
    exact ⟨V'', inferInstance, inferInstance, G'', inferInstance, hV'', hε'', hcn'',
      fun h hfree => htrans'' h
        (IsHMinorFree.minor hfree (contractAdj_isMinor G' s t hadj))⟩

/-- **Step 2/3/4 combined**: The inductive step -- if the average degree is high enough
and h >= 3, then G contains K_h as a minor.

Uses `exists_dense_minor_with_cn_bound` to extract a dense minor where every
edge has `|CN| ≥ 2^{h-3}`. In that minor:
- `exists_vertex_high_degree` (Step 1) finds a vertex `v` of high degree
- `commonNeighbors_implies_induced_degree` + `neighborhood_density` (Step 2)
  give density in `G'[N(v)]`
- The IH (Step 3) gives a `K_{h-1}` minor in `G'[N(v)]`
- `extend_minor_from_neighborhood` (Step 4) extends to `K_h` -/
private lemma averageDegree_inductive_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h) (hV : 0 < Fintype.card V)
    (havg : 2 ^ (h - 2) * Fintype.card V ≤ 2 * G.edgeFinset.card)
    (hh3 : 3 ≤ h)
    (ih : ∀ h' : ℕ, h' < h → 2 ≤ h' →
      ∀ (V' : Type u_1) [Fintype V'] [DecidableEq V']
      (G' : SimpleGraph V') [DecidableRel G'.Adj],
      0 < Fintype.card V' →
      2 ^ (h' - 2) * Fintype.card V' ≤ 2 * G'.edgeFinset.card →
      ¬ G'.IsKMinorFree h') :
    ¬ G.IsKMinorFree h := by
  -- Convert avg-degree condition to ε-form: 2^(h-3) * |V| ≤ |E|
  have hk : 2 ^ (h - 3) * Fintype.card V ≤ G.edgeFinset.card := by
    have hpow : 2 * 2 ^ (h - 3) = 2 ^ (h - 2) := by
      rw [show h - 2 = (h - 3) + 1 from by omega, pow_succ, mul_comm]
    nlinarith
  -- Extract a dense minor with CN ≥ 2^(h-3) for every edge
  obtain ⟨V₀, _, _, G₀, _, hV₀, hε₀, hcn₀, htrans₀⟩ :=
    exists_dense_minor_with_cn_bound (Fintype.card V) (2 ^ (h - 3)) V G
      (le_refl _) hV hk
  -- Convert back to 2|E| form
  have havg₀ : 2 ^ (h - 2) * Fintype.card V₀ ≤ 2 * G₀.edgeFinset.card := by
    have hpow : 2 * 2 ^ (h - 3) = 2 ^ (h - 2) := by
      rw [show h - 2 = (h - 3) + 1 from by omega, pow_succ, mul_comm]
    nlinarith
  -- Step 1: Get a high-degree vertex in G₀
  obtain ⟨v, hv⟩ := exists_vertex_high_degree G₀ (2 ^ (h - 2)) hV₀ havg₀
  -- Step 2: Use the CN bound for high induced degree in G₀[N(v)]
  have hmin_induced : ∀ w : G₀.neighborSet v,
      2 ^ (h - 1 - 2) ≤ (G₀.induce (G₀.neighborSet v)).degree w := by
    intro w
    have hexp : h - 1 - 2 = h - 3 := by omega
    rw [hexp]
    apply commonNeighbors_implies_induced_degree
    exact hcn₀ v w w.prop
  have hdensity := neighborhood_density G₀ v h hh3 hv hmin_induced
  have hNv_pos := neighborhood_nonempty G₀ v h hh3 hv
  -- Step 3: Apply IH for K_{h-1}
  have hminor := ih (h - 1) (by omega) (by omega)
    ↥(G₀.neighborSet v) (G₀.induce (G₀.neighborSet v)) hNv_pos hdensity
  -- Step 4: Extend and transfer
  have hG₀_not_free := extend_minor_from_neighborhood G₀ v h hh3 hminor
  intro hfree
  exact hG₀_not_free (htrans₀ h hfree)

/-! ### Main theorem: average degree forces complete minor -/

/-- **Diestel Proposition 7.2.3** (auxiliary, universe-polymorphic):
If the average degree d(G) = 2|E|/|V| >= 2^(h-2), then G contains K_h as a minor.

This is the main inductive engine, proved by strong induction on h with
quantification over all vertex types, so that the inductive hypothesis
applies to induced subgraphs (which have different vertex types). -/
private theorem averageDegree_forces_complete_minor_aux :
    ∀ (h : ℕ), 2 ≤ h →
    ∀ (V' : Type*) [Fintype V'] [DecidableEq V']
      (G' : SimpleGraph V') [DecidableRel G'.Adj],
    0 < Fintype.card V' →
    2 ^ (h - 2) * Fintype.card V' ≤ 2 * G'.edgeFinset.card →
    ¬ G'.IsKMinorFree h := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
  intro hh V' _ _ G' _ hV' havg
  rcases (show h = 2 ∨ 3 ≤ h by omega) with rfl | hh3
  · -- Base case h = 2: d(G) ≥ 1 means G has an edge, hence K₂ minor
    simp only [show (2 : ℕ) - 2 = 0 from rfl, pow_zero, one_mul] at havg
    have hedge : 0 < G'.edgeFinset.card := by omega
    have hne : G' ≠ ⊥ := edgeFinset_nonempty.mp (Finset.card_pos.mp hedge)
    obtain ⟨v, w, hadj⟩ := exists_adj_of_ne_bot G' hne
    intro hfree
    exact hfree ⟨MinorModel.ofEdge G' hadj⟩
  · -- Inductive case h ≥ 3: delegate to the decomposed lemma
    exact averageDegree_inductive_step G' h hh hV' havg hh3
      (fun h' hlt hh' V'' _ _ G'' _ hV'' havg'' => ih h' hlt hh' V'' G'' hV'' havg'')

/-- **Diestel Proposition 7.2.3**: If the average degree d(G) = 2|E|/|V| >= 2^(h-2),
then G contains K_h as a minor. Stated contrapositively: high average degree implies
G is NOT K_h-minor-free.

The condition `2^(h-2) * |V| <= 2 * |E|` is equivalent to `d(G) >= 2^(h-2)`.

**Base case (h = 2)** is fully proved: d(G) ≥ 1 implies G has an edge, giving a K₂ minor.

**Inductive step (h ≥ 3)** is decomposed into helper lemmas:
- `maxDegree_ge_of_avg_bound`: finds a high-degree vertex
- `extend_minor_from_neighborhood`: extends K_{h-1} minor to K_h
- `averageDegree_inductive_step`: combines steps with the IH

All components are fully proved, including the edge-count formula for contraction
(`card_edgeFinset_contractAdj`): `|E(G/{s,t})| + 1 + |CN(s,t)| = |E(G)|`. -/
theorem averageDegree_forces_complete_minor (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hV : 0 < Fintype.card V)
    (havg : 2 ^ (h - 2) * Fintype.card V ≤ 2 * G.edgeFinset.card) :
    ¬ G.IsKMinorFree h :=
  averageDegree_forces_complete_minor_aux h hh V G hV havg

/-! ### Contrapositive: K_h-minor-free implies bounded average degree -/

/-- If G is K_h-minor-free (h >= 2), then 2|E| < 2^(h-2) * |V|.
This is the contrapositive of `averageDegree_forces_complete_minor`. -/
theorem IsKMinorFree.two_mul_edges_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hV : 0 < Fintype.card V)
    (hfree : G.IsKMinorFree h) :
    2 * G.edgeFinset.card < 2 ^ (h - 2) * Fintype.card V := by
  by_contra hle
  push Not at hle
  exact averageDegree_forces_complete_minor G h hh hV hle hfree

/-- If G is K_h-minor-free (h >= 2), then |E| < 2^(h-3) * |V|.
A convenient form bounding the number of edges directly.
Note: for h >= 3, 2^(h-2)/2 = 2^(h-3). For h = 2, the bound gives |E| < |V|/2. -/
theorem IsKMinorFree.edgeFinset_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hh : 2 ≤ h)
    (hV : 0 < Fintype.card V)
    (hfree : G.IsKMinorFree h) :
    2 * G.edgeFinset.card < 2 ^ (h - 2) * Fintype.card V :=
  hfree.two_mul_edges_lt G h hh hV

/-- If G is K_h-minor-free (h >= 2), then the rational average degree
epsilon(G) = |E|/|V| < 2^(h-2)/2 = 2^(h-3). -/
theorem IsKMinorFree.averageDegree_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (h : ℕ) (hh : 2 ≤ h)
    (hV : 0 < Fintype.card V)
    (hfree : G.IsKMinorFree h) :
    G.averageDegree < (2 ^ (h - 2) : ℚ) / 2 := by
  unfold averageDegree
  have hlt := hfree.two_mul_edges_lt G h hh hV
  rw [div_lt_div_iff₀ (by positivity : (0 : ℚ) < (Fintype.card V : ℚ))
      (by positivity : (0 : ℚ) < 2)]
  norm_cast
  linarith

/-! ### A small minimum-degree minor from exact density

The following refinement of the common-neighbours argument is the density
lemma used in the Bollobás--Thomason linkage proof.  Starting from
`k * |V(G)| ≤ |E(G)|`, first delete excess edges and isolated vertices and
contract every edge with fewer than `k` common neighbours.  Strong induction
on `|V| + |E|` terminates with an exact-density minor in which every vertex has
positive degree and every edge has at least `k` common neighbours.  The
neighbourhood of a minimum-degree vertex then has between `k` and `2k`
vertices and minimum degree at least `k`.
-/

/-- Exact-density core for `exists_small_minDegree_minor_of_dense`. -/
private theorem exists_exact_dense_minor_with_cn_bound :
    ∀ (μ k : ℕ), 0 < k →
    ∀ (V' : Type u_1) [Fintype V'] [DecidableEq V']
      (G' : SimpleGraph V') [DecidableRel G'.Adj],
    Fintype.card V' + G'.edgeFinset.card = μ →
    0 < Fintype.card V' →
    k * Fintype.card V' ≤ G'.edgeFinset.card →
    ∃ (V'' : Type u_1) (_ : Fintype V'') (_ : DecidableEq V'')
      (G'' : SimpleGraph V'') (_ : DecidableRel G''.Adj),
      0 < Fintype.card V'' ∧
      k * Fintype.card V'' = G''.edgeFinset.card ∧
      (∀ v : V'', 0 < G''.degree v) ∧
      (∀ v w : V'', G''.Adj v w →
        k ≤ Fintype.card (G''.commonNeighbors v w)) ∧
      G'' ≤m G' := by
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
    intro k hk V' _ _ G' _ hμ hV' hdense
    by_cases hpositive : ∀ v : V', 0 < G'.degree v
    · by_cases hexact : k * Fintype.card V' = G'.edgeFinset.card
      · by_cases hcn : ∀ v w : V', G'.Adj v w →
            k ≤ Fintype.card (G'.commonNeighbors v w)
        · exact ⟨V', inferInstance, inferInstance, G', inferInstance,
            hV', hexact, hpositive, hcn, IsMinor.refl G'⟩
        · push Not at hcn
          obtain ⟨s, t, hadj, hlt⟩ := hcn
          have hne : s ≠ t := hadj.ne
          have hcard_pos : 0 < Fintype.card ({s}ᶜ : Set V') := by
            rw [card_contractAdj_vertices]
            have htwo : 2 ≤ Fintype.card V' := by
              rw [show (2 : ℕ) = 1 + 1 from rfl, ← Nat.lt_iff_add_one_le]
              exact Fintype.one_lt_card_iff.mpr ⟨s, t, hne⟩
            omega
          have hdense' :=
            contractAdj_preserves_density G' s t hadj hne k hdense hlt
          have hmeasure :
              Fintype.card ({s}ᶜ : Set V') +
                (G'.contractAdj s t hadj).edgeFinset.card < μ := by
            have hv := card_contractAdj_vertices (V := V') s
            have he := card_edgeFinset_contractAdj G' s t hadj hne
            omega
          obtain ⟨V'', _, _, G'', _, hV'', hexact'', hpositive'', hcn'', hminor''⟩ :=
            ih _ hmeasure k hk ({s}ᶜ : Set V') (G'.contractAdj s t hadj)
              rfl hcard_pos hdense'
          exact ⟨V'', inferInstance, inferInstance, G'', inferInstance,
            hV'', hexact'', hpositive'', hcn'',
            IsMinor.trans hminor'' (contractAdj_isMinor G' s t hadj)⟩
      · have hstrict : k * Fintype.card V' < G'.edgeFinset.card :=
          lt_of_le_of_ne hdense hexact
        have hedge : 0 < G'.edgeFinset.card := by omega
        obtain ⟨e, he⟩ := Finset.card_pos.mp hedge
        let Gdel := G'.deleteEdges (↑({e} : Finset (Sym2 V')))
        letI : DecidableRel Gdel.Adj := inferInstance
        have hcard_del : Gdel.edgeFinset.card = G'.edgeFinset.card - 1 := by
          dsimp only [Gdel]
          rw [edgeFinset_deleteEdges, Finset.sdiff_singleton_eq_erase,
            Finset.card_erase_of_mem he]
        have hdense_del : k * Fintype.card V' ≤ Gdel.edgeFinset.card := by
          rw [hcard_del]
          omega
        have hmeasure : Fintype.card V' + Gdel.edgeFinset.card < μ := by
          rw [hcard_del]
          omega
        obtain ⟨V'', _, _, G'', _, hV'', hexact'', hpositive'', hcn'', hminor''⟩ :=
          ih _ hmeasure k hk V' Gdel rfl hV' hdense_del
        have hminor_del : Gdel ≤m G' := by
          exact IsMinor.of_subgraph (G'.deleteEdges_le _)
        exact ⟨V'', inferInstance, inferInstance, G'', inferInstance,
          hV'', hexact'', hpositive'', hcn'', IsMinor.trans hminor'' hminor_del⟩
    · push Not at hpositive
      obtain ⟨v, hv⟩ := hpositive
      have hvzero : G'.degree v = 0 := by omega
      have hedge : 0 < G'.edgeFinset.card := by
        have : 0 < k * Fintype.card V' := Nat.mul_pos hk hV'
        omega
      have hnebot : G' ≠ ⊥ :=
        G'.edgeFinset_nonempty.mp (Finset.card_pos.mp hedge)
      obtain ⟨s, t, hadj⟩ := exists_adj_of_ne_bot G' hnebot
      have htwo : 2 ≤ Fintype.card V' := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, ← Nat.lt_iff_add_one_le]
        exact Fintype.one_lt_card_iff.mpr ⟨s, t, hadj.ne⟩
      let R := ({v}ᶜ : Set V')
      let Gi := G'.induce R
      letI : DecidableRel Gi.Adj := inferInstance
      have hcard_R : Fintype.card R = Fintype.card V' - 1 := by
        dsimp only [R]
        rw [Fintype.card_compl_set, Set.card_singleton]
      have hRpos : 0 < Fintype.card R := by
        rw [hcard_R]
        omega
      have hcard_i : Gi.edgeFinset.card = G'.edgeFinset.card := by
        dsimp only [Gi, R]
        rw [G'.card_edgeFinset_induce_compl_singleton,
          G'.card_edgeFinset_deleteIncidenceSet, hvzero]
        simp
      have hdense_i : k * Fintype.card R ≤ Gi.edgeFinset.card := by
        calc
          k * Fintype.card R ≤ k * Fintype.card V' :=
            Nat.mul_le_mul_left k (by rw [hcard_R]; omega)
          _ ≤ G'.edgeFinset.card := hdense
          _ = Gi.edgeFinset.card := hcard_i.symm
      have hmeasure : Fintype.card R + Gi.edgeFinset.card < μ := by
        rw [hcard_R, hcard_i]
        omega
      obtain ⟨V'', _, _, G'', _, hV'', hexact'', hpositive'', hcn'', hminor''⟩ :=
        ih _ hmeasure k hk R Gi rfl hRpos hdense_i
      have hminor_i : Gi ≤m G' := by
        dsimp only [Gi, R]
        exact IsMinor.of_induce G' _
      exact ⟨V'', inferInstance, inferInstance, G'', inferInstance,
        hV'', hexact'', hpositive'', hcn'', IsMinor.trans hminor'' hminor_i⟩

omit [DecidableEq V] in
/-- A finite graph with `k * |V| ≤ |E|` and `k > 0` has a minor `H` with
`0 < |V(H)| ≤ 2k` and minimum degree at least `k`.

This is the small dense-minor lemma used in the proof that every
`22k`-connected graph is `k`-linked. -/
theorem exists_small_minDegree_minor_of_dense
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (hV : 0 < Fintype.card V)
    (hdense : k * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u_1) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      H ≤m G ∧
      0 < Fintype.card W ∧
      Fintype.card W ≤ 2 * k ∧
      k ≤ H.minDegree := by
  classical
  obtain ⟨V₀, _, _, G₀, _, hV₀, hexact, hpositive, hcn, hminor⟩ :=
    exists_exact_dense_minor_with_cn_bound
      (Fintype.card V + G.edgeFinset.card) k hk V G rfl hV hdense
  letI : Nonempty V₀ := Fintype.card_pos_iff.mp hV₀
  obtain ⟨v, hvmin⟩ := G₀.exists_minimal_degree_vertex
  let W := G₀.neighborSet v
  let H := G₀.induce (G₀.neighborSet v)
  have hWcard : Fintype.card W = G₀.degree v := by
    simpa only [W] using G₀.card_neighborSet_eq_degree v
  have hWpos : 0 < Fintype.card W := by
    rw [hWcard]
    exact hpositive v
  letI : Nonempty W := Fintype.card_pos_iff.mp hWpos
  have hmin_bound : G₀.minDegree ≤ 2 * k := by
    have hbound := G₀.minDegree_mul_card_le_two_mul_card_edges
    rw [← hexact] at hbound
    nlinarith
  have hWle : Fintype.card W ≤ 2 * k := by
    rw [hWcard, ← hvmin]
    exact hmin_bound
  have hHdegree : ∀ w : W, k ≤ H.degree w := by
    intro w
    dsimp only [H, W]
    exact commonNeighbors_implies_induced_degree G₀ v k w (hcn v w w.prop)
  have hHmin : k ≤ H.minDegree := H.le_minDegree_of_forall_le_degree k hHdegree
  have hHminor : H ≤m G := by
    exact IsMinor.trans (by
      dsimp only [H]
      exact IsMinor.of_induce G₀ _) hminor
  exact ⟨W, inferInstance, inferInstance, H, inferInstance,
    hHminor, hWpos, hWle, hHmin⟩

/-! ### Adding an apex to a minor

The sharp density refinement used for the `22k` linkage bound starts with a
minor of the form `K₁ + H₁`, contracts inside `H₁`, and finally takes a
neighbourhood once more to obtain `K₂ + H₃`.  The following private API models
`K₁ + H` on `Option V`, lifts arbitrary minor models through that construction,
and realizes the cone over an induced neighbourhood as a minor of the original
graph.
-/

/-- The cone `K₁ + G`; `none` is the apex. -/
private def kid2056Cone (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some x, some y => G.Adj x y
  symm := by
    intro a b hab
    cases a <;> cases b <;> simp_all only
    exact G.symm hab
  loopless := ⟨by
    intro a
    cases a with
    | none => simp
    | some x => exact G.loopless.irrefl x⟩

private instance kid2056ConeDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (kid2056Cone G).Adj := by
  intro a b
  cases a <;> cases b <;> simp only [kid2056Cone] <;> infer_instance

omit [Fintype V] [DecidableEq V] in
@[simp] private theorem kid2056Cone_none_some (G : SimpleGraph V) (v : V) :
    (kid2056Cone G).Adj none (some v) := trivial

omit [Fintype V] [DecidableEq V] in
@[simp] private theorem kid2056Cone_some_none (G : SimpleGraph V) (v : V) :
    (kid2056Cone G).Adj (some v) none := trivial

omit [Fintype V] [DecidableEq V] in
@[simp] private theorem kid2056Cone_some_some (G : SimpleGraph V) (v w : V) :
    (kid2056Cone G).Adj (some v) (some w) ↔ G.Adj v w := Iff.rfl

omit [DecidableEq V] in
private theorem kid2056Cone_degree_none (G : SimpleGraph V) [DecidableRel G.Adj] :
    (kid2056Cone G).degree none = Fintype.card V := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rw [univ_option]
  have hfilter :
      (Finset.insertNone (Finset.univ : Finset V)).filter
          (fun w => (kid2056Cone G).Adj none w) =
        (Finset.univ : Finset V).map ⟨some, Option.some_injective V⟩ := by
    ext o
    cases o <;> simp [kid2056Cone]
  rw [hfilter, Finset.card_map, Finset.card_univ]

omit [DecidableEq V] in
private theorem kid2056Cone_degree_some (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (kid2056Cone G).degree (some v) = G.degree v + 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have hfilter :
      (Finset.univ : Finset (Option V)).filter
          (fun w => (kid2056Cone G).Adj (some v) w) =
        Finset.insertNone (G.neighborFinset v) := by
    ext o
    cases o <;> simp [kid2056Cone]
  rw [hfilter, Finset.card_insertNone, card_neighborFinset_eq_degree]

omit [DecidableEq V] in
private theorem kid2056Cone_minDegree_add_one_le (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree + 1 ≤ (kid2056Cone G).minDegree := by
  apply (kid2056Cone G).le_minDegree_of_forall_le_degree
  intro o
  cases o with
  | none =>
      rw [kid2056Cone_degree_none]
      exact G.minDegree_lt_card
  | some v =>
      rw [kid2056Cone_degree_some]
      exact Nat.add_le_add_right (G.minDegree_le_degree v) 1

omit [DecidableEq V] in
/-- A finite minor has no more vertices than its ambient graph. -/
private theorem kid2056_isMinor_card_le {H : SimpleGraph V} {G : SimpleGraph W}
    [Fintype W] (h : H ≤m G) : Fintype.card V ≤ Fintype.card W := by
  obtain ⟨m⟩ := h
  simpa only [Nat.card_eq_fintype_card] using m.natCard_le

/-- Branch sets obtained by adding a singleton apex to a minor model. -/
private def kid2056ConeBranchSet {H : SimpleGraph V} {G : SimpleGraph W}
    (m : MinorModel H G) : Option V → Set (Option W)
  | none => {none}
  | some v => Option.some '' m.branchSet v

/-- A minor model lifts functorially through the cone construction. -/
private def kid2056ConeMinorModel {H : SimpleGraph V} {G : SimpleGraph W}
    (m : MinorModel H G) : MinorModel (kid2056Cone H) (kid2056Cone G) where
  branchSet := kid2056ConeBranchSet m
  nonempty := by
    intro a
    cases a with
    | none => exact Set.singleton_nonempty none
    | some a => exact (m.nonempty a).image Option.some
  disjoint := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact (hab rfl).elim
        | some b =>
            rw [Set.disjoint_left]
            intro z hznone hzsome
            simp only [kid2056ConeBranchSet, Set.mem_singleton_iff] at hznone
            subst z
            obtain ⟨w, _, hw⟩ := hzsome
            cases hw
    | some a =>
        cases b with
        | none =>
            rw [Set.disjoint_left]
            intro z hzsome hznone
            simp only [kid2056ConeBranchSet, Set.mem_singleton_iff] at hznone
            subst z
            obtain ⟨w, _, hw⟩ := hzsome
            cases hw
        | some b =>
            rw [Set.disjoint_left]
            intro z hza hzb
            obtain ⟨x, hxa, rfl⟩ := hza
            obtain ⟨y, hyb, hxy⟩ := hzb
            have hxy' : x = y := Option.some.inj hxy.symm
            subst y
            exact (m.disjoint a b (fun h => hab (congrArg some h))).ne_of_mem hxa hyb rfl
  connected := by
    intro a
    cases a with
    | none =>
        rw [connected_iff_exists_forall_reachable]
        exact ⟨⟨none, rfl⟩, fun ⟨z, hz⟩ => by
          simp only [kid2056ConeBranchSet, Set.mem_singleton_iff] at hz
          subst z
          exact Reachable.refl _⟩
    | some a =>
        let f : (G.induce (m.branchSet a)) →g
            ((kid2056Cone G).induce (Option.some '' m.branchSet a)) :=
          { toFun := fun z => ⟨some z.1, ⟨z.1, z.2, rfl⟩⟩
            map_rel' := by
              intro x y hxy
              exact hxy }
        have hf : Function.Surjective f := by
          rintro ⟨z, hz⟩
          obtain ⟨w, hw, rfl⟩ := hz
          exact ⟨⟨w, hw⟩, rfl⟩
        simpa only [kid2056ConeBranchSet] using Connected.map f hf (m.connected a)
  adjacent := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact False.elim hab
        | some b =>
            obtain ⟨w, hw⟩ := m.nonempty b
            exact ⟨none, rfl, some w, ⟨w, hw, rfl⟩, trivial⟩
    | some a =>
        cases b with
        | none =>
            obtain ⟨v, hv⟩ := m.nonempty a
            exact ⟨some v, ⟨v, hv, rfl⟩, none, rfl, trivial⟩
        | some b =>
            obtain ⟨v, hv, w, hw, hvw⟩ := m.adjacent a b hab
            exact ⟨some v, ⟨v, hv, rfl⟩, some w, ⟨w, hw, rfl⟩, hvw⟩

omit [Fintype V] [DecidableEq V] in
/-- If `H` is a minor of `G`, then `K₁ + H` is a minor of `K₁ + G`. -/
private theorem kid2056Cone_isMinor_mono {H : SimpleGraph V} {G : SimpleGraph W}
    (h : H ≤m G) : kid2056Cone H ≤m kid2056Cone G := by
  obtain ⟨m⟩ := h
  exact ⟨kid2056ConeMinorModel m⟩

/-- An injective graph homomorphism gives a singleton-branch-set minor model. -/
private def kid2056MinorModelOfInjectiveHom {H : SimpleGraph V} {G : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f) : MinorModel H G where
  branchSet v := {f v}
  nonempty v := Set.singleton_nonempty _
  disjoint v w hvw := by
    rw [Set.disjoint_singleton]
    exact fun h => hvw (hf h)
  connected v := by
    rw [connected_iff_exists_forall_reachable]
    exact ⟨⟨f v, rfl⟩, fun ⟨w, hw⟩ => by
      simp only [Set.mem_singleton_iff] at hw
      subst w
      exact Reachable.refl _⟩
  adjacent v w hvw := ⟨f v, rfl, f w, rfl, f.map_rel hvw⟩

/-- The natural homomorphism from the cone over `G[N(v)]` into `G`. -/
private def kid2056NeighborConeHom (G : SimpleGraph V) (v : V) :
    kid2056Cone (G.induce (G.neighborSet v)) →g G where
  toFun
    | none => v
    | some w => w.1
  map_rel' := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact False.elim hab
        | some b => exact b.2
    | some a =>
        cases b with
        | none => exact a.2.symm
        | some b => exact hab

omit [Fintype V] [DecidableEq V] in
private theorem kid2056NeighborConeHom_injective (G : SimpleGraph V) (v : V) :
    Function.Injective (kid2056NeighborConeHom G v) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (b.2.ne hab)
  | some a =>
      cases b with
      | none => exact False.elim (a.2.ne hab.symm)
      | some b => exact congrArg some (Subtype.ext hab)

omit [Fintype V] [DecidableEq V] in
/-- The cone over an induced neighbourhood is a minor of the ambient graph. -/
private theorem kid2056NeighborCone_isMinor (G : SimpleGraph V) (v : V) :
    kid2056Cone (G.induce (G.neighborSet v)) ≤m G :=
  ⟨kid2056MinorModelOfInjectiveHom (kid2056NeighborConeHom G v)
    (kid2056NeighborConeHom_injective G v)⟩

/-! ### A minimal minor for a monotone edge threshold -/

/-- Let `T n` be a nondecreasing integral edge threshold above a positive
vertex floor `B`, and suppose no graph on exactly `B` vertices can meet the
threshold.  Any finite graph meeting `T` has a minor strictly above the floor
with exactly `T n` edges, no isolated vertices, and such that contracting any
edge drops below `T (n - 1)`.

This is the purely finite combinatorial selection step behind the logarithmic
potential in the Bollobás--Thomason density refinement. -/
private theorem exists_threshold_minimal_minor :
    ∀ (μ B : ℕ) (T : ℕ → ℕ), 0 < B →
    (∀ n, B < n → T (n - 1) ≤ T n) →
    B.choose 2 < T B →
    ∀ (V' : Type u_1) [Fintype V'] [DecidableEq V']
      (G' : SimpleGraph V') [DecidableRel G'.Adj],
    Fintype.card V' + G'.edgeFinset.card = μ →
    B ≤ Fintype.card V' →
    T (Fintype.card V') ≤ G'.edgeFinset.card →
    ∃ (V'' : Type u_1) (_ : Fintype V'') (_ : DecidableEq V'')
      (G'' : SimpleGraph V'') (_ : DecidableRel G''.Adj),
      B < Fintype.card V'' ∧
      G''.edgeFinset.card = T (Fintype.card V'') ∧
      (∀ v : V'', 0 < G''.degree v) ∧
      (∀ s t : V'', (hadj : G''.Adj s t) →
        (G''.contractAdj s t hadj).edgeFinset.card <
          T (Fintype.card V'' - 1)) ∧
      G'' ≤m G' := by
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
    intro B T hB hmono hboundary V' _ _ G' _ hμ hBcard hdense
    have hBlt : B < Fintype.card V' := by
      apply lt_of_le_of_ne hBcard
      intro heq
      have hedge := G'.card_edgeFinset_le_card_choose_two
      rw [← heq] at hdense hedge
      omega
    by_cases hpositive : ∀ v : V', 0 < G'.degree v
    · by_cases hexact : G'.edgeFinset.card = T (Fintype.card V')
      · by_cases hcontract : ∀ s t : V', (hadj : G'.Adj s t) →
            (G'.contractAdj s t hadj).edgeFinset.card <
              T (Fintype.card V' - 1)
        · exact ⟨V', inferInstance, inferInstance, G', inferInstance,
            hBlt, hexact, hpositive, hcontract, IsMinor.refl G'⟩
        · push Not at hcontract
          obtain ⟨s, t, hadj, hge⟩ := hcontract
          have hne : s ≠ t := hadj.ne
          have hcard : Fintype.card ({s}ᶜ : Set V') = Fintype.card V' - 1 :=
            card_contractAdj_vertices (V := V') s
          have hBcard' : B ≤ Fintype.card ({s}ᶜ : Set V') := by
            rw [hcard]
            omega
          have hmeasure :
              Fintype.card ({s}ᶜ : Set V') +
                (G'.contractAdj s t hadj).edgeFinset.card < μ := by
            have hedge := card_edgeFinset_contractAdj G' s t hadj hne
            rw [hcard]
            omega
          obtain ⟨V'', _, _, G'', _, hBlt'', hexact'', hpositive'',
              hcontract'', hminor''⟩ :=
            ih _ hmeasure B T hB hmono hboundary
              ({s}ᶜ : Set V') (G'.contractAdj s t hadj)
              rfl hBcard' (by simpa only [hcard] using hge)
          exact ⟨V'', inferInstance, inferInstance, G'', inferInstance,
            hBlt'', hexact'', hpositive'', hcontract'',
            IsMinor.trans hminor'' (contractAdj_isMinor G' s t hadj)⟩
      · have hstrict : T (Fintype.card V') < G'.edgeFinset.card :=
          lt_of_le_of_ne hdense (Ne.symm hexact)
        have hedge : 0 < G'.edgeFinset.card := by omega
        obtain ⟨e, he⟩ := Finset.card_pos.mp hedge
        let Gdel := G'.deleteEdges (↑({e} : Finset (Sym2 V')))
        letI : DecidableRel Gdel.Adj := inferInstance
        have hcard_del : Gdel.edgeFinset.card = G'.edgeFinset.card - 1 := by
          dsimp only [Gdel]
          rw [edgeFinset_deleteEdges, Finset.sdiff_singleton_eq_erase,
            Finset.card_erase_of_mem he]
        have hdense_del : T (Fintype.card V') ≤ Gdel.edgeFinset.card := by
          rw [hcard_del]
          omega
        have hmeasure : Fintype.card V' + Gdel.edgeFinset.card < μ := by
          rw [hcard_del]
          omega
        obtain ⟨V'', _, _, G'', _, hBlt'', hexact'', hpositive'',
            hcontract'', hminor''⟩ :=
          ih _ hmeasure B T hB hmono hboundary V' Gdel
            rfl hBcard hdense_del
        exact ⟨V'', inferInstance, inferInstance, G'', inferInstance,
          hBlt'', hexact'', hpositive'', hcontract'',
          IsMinor.trans hminor'' (IsMinor.of_subgraph (G'.deleteEdges_le _))⟩
    · push Not at hpositive
      obtain ⟨v, hv⟩ := hpositive
      have hvzero : G'.degree v = 0 := by omega
      let R := ({v}ᶜ : Set V')
      let Gi := G'.induce R
      letI : DecidableRel Gi.Adj := inferInstance
      have hcard_R : Fintype.card R = Fintype.card V' - 1 := by
        dsimp only [R]
        rw [Fintype.card_compl_set, Set.card_singleton]
      have hBcard_R : B ≤ Fintype.card R := by
        rw [hcard_R]
        omega
      have hcard_i : Gi.edgeFinset.card = G'.edgeFinset.card := by
        dsimp only [Gi, R]
        rw [G'.card_edgeFinset_induce_compl_singleton,
          G'.card_edgeFinset_deleteIncidenceSet, hvzero]
        simp
      have hdense_i : T (Fintype.card R) ≤ Gi.edgeFinset.card := by
        calc
          T (Fintype.card R) = T (Fintype.card V' - 1) := by rw [hcard_R]
          _ ≤ T (Fintype.card V') := hmono _ hBlt
          _ ≤ G'.edgeFinset.card := hdense
          _ = Gi.edgeFinset.card := hcard_i.symm
      have hmeasure : Fintype.card R + Gi.edgeFinset.card < μ := by
        rw [hcard_R, hcard_i]
        omega
      obtain ⟨V'', _, _, G'', _, hBlt'', hexact'', hpositive'',
          hcontract'', hminor''⟩ :=
        ih _ hmeasure B T hB hmono hboundary R Gi
          rfl hBcard_R hdense_i
      exact ⟨V'', inferInstance, inferInstance, G'', inferInstance,
        hBlt'', hexact'', hpositive'', hcontract'',
        IsMinor.trans hminor'' (by
          dsimp only [Gi, R]
          exact IsMinor.of_induce G' _)⟩

/-! ### The Bollobás--Thomason logarithmic potential -/

/-- The only numerical logarithm estimate needed for the constant `22`.
Five nonnegative terms of the exponential series already give
`11 / 2 ≤ exp (7 / 4)`. -/
private theorem kid2056_log_eleven_halves_le_seven_fourths :
    Real.log (11 / 2 : ℝ) ≤ 7 / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 11 / 2)).2
  calc
    (11 / 2 : ℝ) ≤
        ∑ i ∈ Finset.range 5, (7 / 4 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (7 / 4) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 5

/-- The real potential `B n / 2 * (log (n / B) + 1)`.  In the linkage
application `B = 4k`; equivalently this is the book's potential with
`β = 4/11` and `ℓ = 11k`. -/
private noncomputable def kid2056Potential (B n : ℕ) : ℝ :=
  (B : ℝ) * (n : ℝ) / 2 * (Real.log ((n : ℝ) / (B : ℝ)) + 1)

/-- The integral edge threshold obtained by rounding the potential up. -/
private noncomputable def kid2056Threshold (B n : ℕ) : ℕ :=
  ⌈kid2056Potential B n⌉₊

private theorem kid2056Potential_nonneg {B n : ℕ} (hB : 0 < B) (hBn : B ≤ n) :
    0 ≤ kid2056Potential B n := by
  have hratio : (1 : ℝ) ≤ (n : ℝ) / (B : ℝ) := by
    rw [le_div_iff₀ (Nat.cast_pos.2 hB)]
    norm_num
    exact_mod_cast hBn
  have hlog : 0 ≤ Real.log ((n : ℝ) / (B : ℝ)) := Real.log_nonneg hratio
  unfold kid2056Potential
  positivity

private theorem kid2056Potential_pred_le {B n : ℕ} (hB : 0 < B) (hBn : B < n) :
    kid2056Potential B (n - 1) ≤ kid2056Potential B n := by
  have hBpred : B ≤ n - 1 := by omega
  have hpredpos : 0 < n - 1 := lt_of_lt_of_le hB hBpred
  have hratioPred : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / (B : ℝ) := by
    rw [le_div_iff₀ (Nat.cast_pos.2 hB)]
    norm_num
    exact_mod_cast hBpred
  have hratioLe : ((n - 1 : ℕ) : ℝ) / (B : ℝ) ≤ (n : ℝ) / (B : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg B)
    norm_cast
    omega
  have hlogLe :
      Real.log (((n - 1 : ℕ) : ℝ) / (B : ℝ)) ≤
        Real.log ((n : ℝ) / (B : ℝ)) :=
    Real.log_le_log (by positivity) hratioLe
  have htermPred :
      0 ≤ Real.log (((n - 1 : ℕ) : ℝ) / (B : ℝ)) + 1 := by
    have := Real.log_nonneg hratioPred
    linarith
  unfold kid2056Potential
  calc
    (B : ℝ) * ((n - 1 : ℕ) : ℝ) / 2 *
          (Real.log (((n - 1 : ℕ) : ℝ) / (B : ℝ)) + 1) =
        ((B : ℝ) / 2) * (((n - 1 : ℕ) : ℝ) *
          (Real.log (((n - 1 : ℕ) : ℝ) / (B : ℝ)) + 1)) := by ring
    _ ≤ ((B : ℝ) / 2) * ((n : ℝ) *
          (Real.log ((n : ℝ) / (B : ℝ)) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (by norm_cast; omega) (by linarith) htermPred (by positivity)
    _ = (B : ℝ) * (n : ℝ) / 2 *
          (Real.log ((n : ℝ) / (B : ℝ)) + 1) := by ring

private theorem kid2056_choose_two_lt_threshold {B : ℕ} (hB : 0 < B) :
    B.choose 2 < kid2056Threshold B B := by
  rw [kid2056Threshold, Nat.lt_ceil]
  rw [Nat.cast_choose_two]
  unfold kid2056Potential
  have hB0 : (B : ℝ) ≠ 0 := (Nat.cast_pos.2 hB).ne'
  rw [div_self hB0, Real.log_one]
  norm_num
  have hBreal : (0 : ℝ) < B := Nat.cast_pos.2 hB
  nlinarith

private theorem kid2056Threshold_pred_le {B n : ℕ} (hB : 0 < B) (hBn : B < n) :
    kid2056Threshold B (n - 1) ≤ kid2056Threshold B n := by
  unfold kid2056Threshold
  exact Nat.ceil_le_ceil (kid2056Potential_pred_le hB hBn)

/-- On the interval `B ≤ n ≤ 11B/2`, the potential is at most
`(11/8)Bn`.  This is the estimate that lets an `11k`-minimum-degree graph
meet the threshold when `B = 4k`. -/
private theorem kid2056Potential_le_initial {B n : ℕ} (hB : 0 < B)
    (hBn : B ≤ n) (hn : 2 * n ≤ 11 * B) :
    kid2056Potential B n ≤ (11 / 8 : ℝ) * (B : ℝ) * (n : ℝ) := by
  have hnpos : 0 < n := lt_of_lt_of_le hB hBn
  have hratioPos : 0 < (n : ℝ) / (B : ℝ) := by positivity
  have hratioLe : (n : ℝ) / (B : ℝ) ≤ (11 / 2 : ℝ) := by
    rw [div_le_iff₀ (Nat.cast_pos.2 hB)]
    have hnreal : (2 : ℝ) * (n : ℝ) ≤ 11 * (B : ℝ) := by
      exact_mod_cast hn
    nlinarith
  have hlogLe : Real.log ((n : ℝ) / (B : ℝ)) ≤ 7 / 4 :=
    (Real.log_le_log hratioPos hratioLe).trans
      kid2056_log_eleven_halves_le_seven_fourths
  unfold kid2056Potential
  have hBreal : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hBreal hnreal]

/-- The discrete derivative of the potential.  The estimate is the elementary
inequality `1 - 1/x ≤ log x` applied to `x = n/(n-1)`. -/
private theorem kid2056Potential_step_lower {B n : ℕ} (hB : 0 < B) (hBn : B < n) :
    (B : ℝ) *
        (Real.log ((n : ℝ) / (B : ℝ)) + 2 - 1 / (n : ℝ)) ≤
      2 * (kid2056Potential B n - kid2056Potential B (n - 1)) := by
  have hnpos : 0 < n := lt_trans hB hBn
  have hpredpos : 0 < n - 1 := by omega
  have hB0 : (B : ℝ) ≠ 0 := (Nat.cast_pos.2 hB).ne'
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hnpos).ne'
  have hpred0 : ((n - 1 : ℕ) : ℝ) ≠ 0 :=
    (Nat.cast_pos.2 hpredpos).ne'
  have hlogdiff :
      Real.log ((n : ℝ) / (B : ℝ)) -
          Real.log (((n - 1 : ℕ) : ℝ) / (B : ℝ)) =
        Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    rw [Real.log_div hn0 hB0, Real.log_div hpred0 hB0,
      Real.log_div hn0 hpred0]
    ring
  have hratioPos : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) := by positivity
  have hlogratio := Real.one_sub_inv_le_log_of_pos hratioPos
  have hpredcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hinv :
      1 - ((n : ℝ) / ((n - 1 : ℕ) : ℝ))⁻¹ = 1 / (n : ℝ) := by
    rw [hpredcast]
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have hnone : 1 < n := by omega
      have : (1 : ℝ) < n := by exact_mod_cast hnone
      linarith
    field_simp [hn0, hn1]
    ring
  rw [hinv] at hlogratio
  have hscaled :
      (B : ℝ) * ((n - 1 : ℕ) : ℝ) * (1 / (n : ℝ)) ≤
        (B : ℝ) * ((n - 1 : ℕ) : ℝ) *
          Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    gcongr
  calc
    (B : ℝ) *
          (Real.log ((n : ℝ) / (B : ℝ)) + 2 - 1 / (n : ℝ)) =
        (B : ℝ) *
          (Real.log ((n : ℝ) / (B : ℝ)) + 1 +
            ((n - 1 : ℕ) : ℝ) * (1 / (n : ℝ))) := by
      field_simp
      rw [hpredcast]
      ring
    _ ≤ (B : ℝ) *
          (Real.log ((n : ℝ) / (B : ℝ)) + 1 +
            ((n - 1 : ℕ) : ℝ) *
              Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) := by
      linarith
    _ = 2 * (kid2056Potential B n - kid2056Potential B (n - 1)) := by
      rw [← hlogdiff]
      unfold kid2056Potential
      rw [hpredcast]
      ring

/-- In a threshold-minimal graph, every edge has many common neighbours.  The
loss of that edge under contraction is compared with the discrete derivative
of the logarithmic potential, while the minimum degree is bounded by the mean
degree. -/
private theorem kid2056_commonNeighbors_bound_of_threshold
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (B : ℕ) (hB : 0 < B) (hfour : 4 ≤ B)
    (hBcard : B < Fintype.card V)
    (hexact : H.edgeFinset.card = kid2056Threshold B (Fintype.card V))
    (hcontract : ∀ s t : V, (hadj : H.Adj s t) →
      (H.contractAdj s t hadj).edgeFinset.card <
        kid2056Threshold B (Fintype.card V - 1))
    {s t : V} (hadj : H.Adj s t) :
    B - 3 + H.minDegree ≤ 2 * Fintype.card (H.commonNeighbors s t) := by
  let n := Fintype.card V
  let c := Fintype.card (H.commonNeighbors s t)
  have hnpos : 0 < n := lt_trans hB hBcard
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hpotNonneg : 0 ≤ kid2056Potential B n :=
    kid2056Potential_nonneg hB hBcard.le
  have hpotEdges : kid2056Potential B n ≤ (H.edgeFinset.card : ℝ) := by
    rw [hexact, kid2056Threshold]
    exact Nat.le_ceil _
  have hcontractReal :
      ((H.contractAdj s t hadj).edgeFinset.card : ℝ) <
        kid2056Potential B (n - 1) := by
    have h := hcontract s t hadj
    change (H.contractAdj s t hadj).edgeFinset.card < kid2056Threshold B (n - 1) at h
    rw [kid2056Threshold, Nat.lt_ceil] at h
    exact h
  have hedgeCount := card_edgeFinset_contractAdj H s t hadj hadj.ne
  have hedgeCountReal :
      ((H.contractAdj s t hadj).edgeFinset.card : ℝ) + 1 + (c : ℝ) =
        (H.edgeFinset.card : ℝ) := by
    exact_mod_cast hedgeCount
  have hcLower :
      kid2056Potential B n - kid2056Potential B (n - 1) - 1 < (c : ℝ) := by
    linarith
  have hceilUpper :
      (H.edgeFinset.card : ℝ) < kid2056Potential B n + 1 := by
    rw [hexact, kid2056Threshold]
    exact Nat.ceil_lt_add_one hpotNonneg
  have hdegreeCount := H.minDegree_mul_card_le_two_mul_card_edges
  have hdegreeCountReal :
      (H.minDegree : ℝ) * (n : ℝ) ≤ 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast hdegreeCount
  have hdegreeTimes :
      (H.minDegree : ℝ) * (n : ℝ) <
        2 * (kid2056Potential B n + 1) := by
    exact hdegreeCountReal.trans_lt (mul_lt_mul_of_pos_left hceilUpper (by norm_num))
  have hnrealpos : (0 : ℝ) < n := Nat.cast_pos.2 hnpos
  have hdegreeUpper :
      (H.minDegree : ℝ) <
        (B : ℝ) * (Real.log ((n : ℝ) / (B : ℝ)) + 1) + 2 / (n : ℝ) := by
    calc
      (H.minDegree : ℝ) < 2 * (kid2056Potential B n + 1) / (n : ℝ) :=
        (lt_div_iff₀ hnrealpos).2 hdegreeTimes
      _ = (B : ℝ) * (Real.log ((n : ℝ) / (B : ℝ)) + 1) +
          2 / (n : ℝ) := by
        unfold kid2056Potential
        field_simp
  have hstep := kid2056Potential_step_lower hB hBcard
  have hcAnalytic :
      (B : ℝ) *
          (Real.log ((n : ℝ) / (B : ℝ)) + 2 - 1 / (n : ℝ)) - 2 <
        2 * (c : ℝ) := by
    nlinarith
  have hfrac : ((B : ℝ) + 2) / (n : ℝ) < 2 := by
    rw [div_lt_iff₀ hnrealpos]
    have hnat : B + 2 < 2 * n := by omega
    exact_mod_cast hnat
  have hgapIdentity :
      ((B : ℝ) *
            (Real.log ((n : ℝ) / (B : ℝ)) + 2 - 1 / (n : ℝ)) - 2) -
          ((B : ℝ) * (Real.log ((n : ℝ) / (B : ℝ)) + 1) + 2 / (n : ℝ)) =
        (B : ℝ) - 2 - ((B : ℝ) + 2) / (n : ℝ) := by
    ring
  have hgap :
      (B : ℝ) - 4 <
        ((B : ℝ) *
            (Real.log ((n : ℝ) / (B : ℝ)) + 2 - 1 / (n : ℝ)) - 2) -
          ((B : ℝ) * (Real.log ((n : ℝ) / (B : ℝ)) + 1) + 2 / (n : ℝ)) := by
    rw [hgapIdentity]
    linarith
  have hcombine :
      ((B : ℝ) *
            (Real.log ((n : ℝ) / (B : ℝ)) + 2 - 1 / (n : ℝ)) - 2) -
          ((B : ℝ) * (Real.log ((n : ℝ) / (B : ℝ)) + 1) + 2 / (n : ℝ)) <
        2 * (c : ℝ) - H.minDegree :=
    sub_lt_sub hcAnalytic hdegreeUpper
  have hreal : (B : ℝ) - 4 + H.minDegree < 2 * (c : ℝ) := by
    linarith [hgap.trans hcombine]
  have hrealNat : ((B - 4 + H.minDegree : ℕ) : ℝ) < (2 * c : ℕ) := by
    push_cast [Nat.cast_sub hfour]
    exact hreal
  have hnat : B - 4 + H.minDegree < 2 * c := by
    exact_mod_cast hrealNat
  dsimp only [c] at hnat ⊢
  omega

/-! ### The strong dense subcontraction -/

/-- The first neighbourhood step in the Bollobás--Thomason argument.  Exact
`11k`-density yields a minor of the form `K₁ + H` with at most `22k` vertices
in `H` and minimum degree at least `11k`. -/
private theorem exists_small_minDegree_coneMinor_of_dense
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (hV : 0 < Fintype.card V)
    (hdense : 11 * k * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u_1) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      kid2056Cone H ≤m G ∧
      0 < Fintype.card W ∧
      Fintype.card W ≤ 22 * k ∧
      11 * k ≤ H.minDegree := by
  classical
  let ell := 11 * k
  have hell : 0 < ell := by
    dsimp only [ell]
    omega
  obtain ⟨V₀, _, _, G₀, _, hV₀, hexact, hpositive, hcn, hminor⟩ :=
    exists_exact_dense_minor_with_cn_bound
      (Fintype.card V + G.edgeFinset.card) ell hell V G rfl hV (by
        simpa only [ell] using hdense)
  letI : Nonempty V₀ := Fintype.card_pos_iff.mp hV₀
  obtain ⟨v, hvmin⟩ := G₀.exists_minimal_degree_vertex
  let W := G₀.neighborSet v
  let H := G₀.induce (G₀.neighborSet v)
  have hWcard : Fintype.card W = G₀.degree v := by
    simpa only [W] using G₀.card_neighborSet_eq_degree v
  have hWpos : 0 < Fintype.card W := by
    rw [hWcard]
    exact hpositive v
  letI : Nonempty W := Fintype.card_pos_iff.mp hWpos
  have hminBound : G₀.minDegree ≤ 2 * ell := by
    have hbound := G₀.minDegree_mul_card_le_two_mul_card_edges
    rw [← hexact] at hbound
    nlinarith
  have hWle : Fintype.card W ≤ 22 * k := by
    rw [hWcard, ← hvmin]
    dsimp only [ell] at hminBound
    omega
  have hHdegree : ∀ w : W, ell ≤ H.degree w := by
    intro w
    dsimp only [H, W]
    exact commonNeighbors_implies_induced_degree G₀ v ell w (hcn v w w.prop)
  have hHmin : ell ≤ H.minDegree :=
    H.le_minDegree_of_forall_le_degree ell hHdegree
  have hcone : kid2056Cone H ≤m G₀ := by
    dsimp only [H]
    exact kid2056NeighborCone_isMinor G₀ v
  exact ⟨W, inferInstance, inferInstance, H, inferInstance,
    IsMinor.trans hcone hminor, hWpos, hWle, by simpa only [ell] using hHmin⟩

omit [DecidableEq V] in
/-- A graph in the first-neighbourhood range meets the rounded logarithmic
threshold with `B=4k`. -/
private theorem kid2056_threshold_le_edges_of_minDegree
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (k : ℕ) (hk : 0 < k) (hV : 0 < Fintype.card V)
    (hcard : Fintype.card V ≤ 22 * k)
    (hmin : 11 * k ≤ H.minDegree) :
    kid2056Threshold (4 * k) (Fintype.card V) ≤ H.edgeFinset.card := by
  let n := Fintype.card V
  let B := 4 * k
  letI : Nonempty V := Fintype.card_pos_iff.mp hV
  have hB : 0 < B := by
    dsimp only [B]
    omega
  have hBn : B ≤ n := by
    have hminlt := H.minDegree_lt_card
    dsimp only [B, n]
    omega
  have hnrange : 2 * n ≤ 11 * B := by
    dsimp only [n, B]
    omega
  have hpot := kid2056Potential_le_initial hB hBn hnrange
  have hdegree := H.minDegree_mul_card_le_two_mul_card_edges
  have hdenseNat : 11 * k * n ≤ 2 * H.edgeFinset.card := by
    exact (Nat.mul_le_mul_right n hmin).trans (by simpa only [n] using hdegree)
  have hdenseReal :
      ((11 * k * n : ℕ) : ℝ) ≤ 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast hdenseNat
  have hscale :
      (11 / 8 : ℝ) * (B : ℝ) * (n : ℝ) =
        ((11 * k * n : ℕ) : ℝ) / 2 := by
    dsimp only [B]
    push_cast
    ring
  have hpotEdges : kid2056Potential B n ≤ (H.edgeFinset.card : ℝ) := by
    rw [hscale] at hpot
    linarith
  change kid2056Threshold B n ≤ H.edgeFinset.card
  rw [kid2056Threshold, Nat.ceil_le]
  exact hpotEdges

omit [DecidableEq V] in
/-- The threshold-minimal graph obtained from the first neighbourhood has
minimum degree at most `11k`. -/
private theorem kid2056_minDegree_le_eleven_mul_of_threshold
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (k : ℕ) (hk : 0 < k)
    (hBcard : 4 * k < Fintype.card V)
    (hcard : Fintype.card V ≤ 22 * k)
    (hexact : H.edgeFinset.card =
      kid2056Threshold (4 * k) (Fintype.card V)) :
    H.minDegree ≤ 11 * k := by
  let n := Fintype.card V
  let B := 4 * k
  have hnpos : 0 < n := by
    dsimp only [n]
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hB : 0 < B := by
    dsimp only [B]
    omega
  have hBn : B ≤ n := by
    dsimp only [B, n]
    omega
  have hnrange : 2 * n ≤ 11 * B := by
    dsimp only [n, B]
    omega
  have hpot := kid2056Potential_le_initial hB hBn hnrange
  have hpotNonneg := kid2056Potential_nonneg hB hBn
  have hceil :
      (H.edgeFinset.card : ℝ) < kid2056Potential B n + 1 := by
    rw [hexact, kid2056Threshold]
    exact Nat.ceil_lt_add_one hpotNonneg
  have hscale :
      (11 / 8 : ℝ) * (B : ℝ) * (n : ℝ) =
        ((11 * k * n : ℕ) : ℝ) / 2 := by
    dsimp only [B]
    push_cast
    ring
  rw [hscale] at hpot
  have hedgeReal :
      2 * (H.edgeFinset.card : ℝ) < ((11 * k * n : ℕ) : ℝ) + 2 := by
    nlinarith
  have hedge : 2 * H.edgeFinset.card < 11 * k * n + 2 := by
    exact_mod_cast hedgeReal
  by_contra hnot
  have hdelta : 11 * k + 1 ≤ H.minDegree := by omega
  have hnlarge : 2 < n := by
    dsimp only [n] at hBcard ⊢
    omega
  have hbase : 11 * k * n + 2 < (11 * k + 1) * n := by
    simp only [Nat.add_mul, one_mul]
    omega
  have hdeltaMul : (11 * k + 1) * n ≤ H.minDegree * n :=
    Nat.mul_le_mul_right n hdelta
  have hdegree : H.minDegree * n ≤ 2 * H.edgeFinset.card := by
    simpa only [n] using H.minDegree_mul_card_le_two_mul_card_edges
  have hcontra : 11 * k * n + 2 < 2 * H.edgeFinset.card :=
    hbase.trans_le (hdeltaMul.trans hdegree)
  omega

omit [DecidableEq V] in
/-- Strong dense subcontraction used by the rooted linkage argument.  From
average degree at least `22k`, it produces a minor with at most `11k+2`
vertices and minimum degree satisfying the exact Bollobás--Thomason margin. -/
theorem exists_small_strong_minor_of_dense
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (hV : 0 < Fintype.card V)
    (hdense : 11 * k * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u_1) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      H ≤m G ∧
      0 < Fintype.card W ∧
      Fintype.card W ≤ 11 * k + 2 ∧
      Fintype.card W + 4 * k - 1 ≤ 2 * H.minDegree := by
  classical
  obtain ⟨W₁, _, _, H₁, _, hcone₁G, hW₁pos, hW₁card, hH₁min⟩ :=
    exists_small_minDegree_coneMinor_of_dense G k hk hV hdense
  letI : Nonempty W₁ := Fintype.card_pos_iff.mp hW₁pos
  have hBpos : 0 < 4 * k := by omega
  have hBcard₁ : 4 * k ≤ Fintype.card W₁ := by
    have hminlt := H₁.minDegree_lt_card
    omega
  have hthreshold₁ :
      kid2056Threshold (4 * k) (Fintype.card W₁) ≤ H₁.edgeFinset.card :=
    kid2056_threshold_le_edges_of_minDegree
      H₁ k hk hW₁pos hW₁card hH₁min
  obtain ⟨W₂, _, _, H₂, _, hBlt₂, hexact₂, hpositive₂, hcontract₂, hminor₂₁⟩ :=
    exists_threshold_minimal_minor
      (Fintype.card W₁ + H₁.edgeFinset.card)
      (4 * k) (kid2056Threshold (4 * k)) hBpos
      (fun n hn => kid2056Threshold_pred_le hBpos hn)
      (kid2056_choose_two_lt_threshold hBpos)
      W₁ H₁ rfl hBcard₁ hthreshold₁
  have hW₂pos : 0 < Fintype.card W₂ := lt_trans hBpos hBlt₂
  letI : Nonempty W₂ := Fintype.card_pos_iff.mp hW₂pos
  have hW₂card₁ : Fintype.card W₂ ≤ Fintype.card W₁ :=
    kid2056_isMinor_card_le hminor₂₁
  have hW₂card : Fintype.card W₂ ≤ 22 * k := hW₂card₁.trans hW₁card
  have hH₂min : H₂.minDegree ≤ 11 * k :=
    kid2056_minDegree_le_eleven_mul_of_threshold
      H₂ k hk hBlt₂ hW₂card hexact₂
  obtain ⟨u, humin⟩ := H₂.exists_minimal_degree_vertex
  let W₃ := H₂.neighborSet u
  let H₃ := H₂.induce (H₂.neighborSet u)
  have hW₃card : Fintype.card W₃ = H₂.minDegree := by
    calc
      Fintype.card W₃ = H₂.degree u := by
        simpa only [W₃] using H₂.card_neighborSet_eq_degree u
      _ = H₂.minDegree := humin.symm
  have hW₃pos : 0 < Fintype.card W₃ := by
    rw [hW₃card, humin]
    exact hpositive₂ u
  letI : Nonempty W₃ := Fintype.card_pos_iff.mp hW₃pos
  have hW₃cardLe : Fintype.card W₃ ≤ 11 * k := by
    rw [hW₃card]
    exact hH₂min
  have hH₃degree : ∀ w : W₃,
      4 * k - 3 + H₂.minDegree ≤ 2 * H₃.degree w := by
    intro w
    have hcn := kid2056_commonNeighbors_bound_of_threshold
      H₂ (4 * k) hBpos (by omega) hBlt₂ hexact₂ hcontract₂ w.prop
    dsimp only [H₃, W₃]
    rw [induce_neighborSet_degree_eq_card_commonNeighbors]
    exact hcn
  have hH₃min : 4 * k - 3 + H₂.minDegree ≤ 2 * H₃.minDegree := by
    obtain ⟨z, hz⟩ := H₃.exists_minimal_degree_vertex
    rw [hz]
    exact hH₃degree z
  let H := kid2056Cone (kid2056Cone H₃)
  have hconeH₃H₂ : kid2056Cone H₃ ≤m H₂ := by
    dsimp only [H₃]
    exact kid2056NeighborCone_isMinor H₂ u
  have hminor : H ≤m G := by
    dsimp only [H]
    exact IsMinor.trans
      (kid2056Cone_isMinor_mono hconeH₃H₂)
      (IsMinor.trans (kid2056Cone_isMinor_mono hminor₂₁) hcone₁G)
  have hcardH : Fintype.card (Option (Option W₃)) = Fintype.card W₃ + 2 := by
    simp
  have hcard : Fintype.card (Option (Option W₃)) ≤ 11 * k + 2 := by
    rw [hcardH]
    omega
  have hdelta₁ : H₃.minDegree + 1 ≤ (kid2056Cone H₃).minDegree :=
    kid2056Cone_minDegree_add_one_le H₃
  have hdelta₂ : (kid2056Cone H₃).minDegree + 1 ≤ H.minDegree := by
    dsimp only [H]
    exact kid2056Cone_minDegree_add_one_le (kid2056Cone H₃)
  have hdelta : H₃.minDegree + 2 ≤ H.minDegree := by omega
  have hmargin :
      Fintype.card (Option (Option W₃)) + 4 * k - 1 ≤ 2 * H.minDegree := by
    rw [hcardH, hW₃card]
    omega
  exact ⟨Option (Option W₃), inferInstance, inferInstance, H, inferInstance,
    hminor, by simp, hcard, hmargin⟩

end SimpleGraph
