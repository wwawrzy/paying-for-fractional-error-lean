/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic

/-!
# k-Degeneracy of Graphs (Diestel, Section 1.5 / [B1])

A graph `G` is **k-degenerate** if every non-empty induced subgraph has a vertex of degree at
most `k` (within that subgraph). Equivalently, there exists a vertex ordering `(v_1, ..., v_n)`
such that each `v_i` has at most `k` earlier neighbours -- a *degeneracy ordering*.

The **degeneracy** of `G` is the minimum `k` for which `G` is k-degenerate.

## Main definitions

* `SimpleGraph.IsKDegenerate G k` -- every non-empty induced subgraph has a vertex of
  degree at most `k` in that subgraph.
* `SimpleGraph.degeneracy G` -- the degeneracy of `G`.
* `SimpleGraph.IsDegeneracyOrdering G ord k` -- `ord` is a valid degeneracy ordering.

## Main results

* `SimpleGraph.IsKDegenerate.mono` -- k-degeneracy is monotone in `k`.
* `SimpleGraph.isKDegenerate_of_degeneracy_order` -- degeneracy ordering implies k-degeneracy.
* `SimpleGraph.exists_degeneracy_order` -- every finite k-degenerate graph admits a degeneracy
  ordering.
* `SimpleGraph.IsKDegenerate.induce` -- induced subgraphs preserve k-degeneracy.
* `SimpleGraph.IsKDegenerate.edgeFinset_card_le_mul_card` -- a finite k-degenerate graph has
  at most `k * |V|` edges.
* `SimpleGraph.isKDegenerate_of_edgeDensityBound` -- edge density bound implies degeneracy.
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V]

/-! ## Definition of k-degeneracy -/

/-- The **degree of `v` in the induced subgraph on `s`**: the number of neighbours of `v`
in `s`. -/
def inducedDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (s : Finset V) : Nat :=
  (s.filter (G.Adj v)).card

/-- A graph `G` is **k-degenerate** if every non-empty finite set of vertices `s` contains
a vertex `v` whose degree in the induced subgraph `G[s]` is at most `k`. -/
def IsKDegenerate (G : SimpleGraph V) [DecidableRel G.Adj] (k : Nat) : Prop :=
  ∀ (s : Finset V), s.Nonempty →
    ∃ (v : V) (_ : v ∈ s), G.inducedDegree v s ≤ k

/-- The **degeneracy** of a finite graph: the minimum `k` for which `G` is k-degenerate. -/
noncomputable def degeneracy (G : SimpleGraph V) [DecidableRel G.Adj] : Nat :=
  sInf {k | G.IsKDegenerate k}

/-! ## Basic lemmas -/

omit [DecidableEq V] in
/-- Monotonicity: a k-degenerate graph is also k'-degenerate for any k' >= k. -/
theorem IsKDegenerate.mono {G : SimpleGraph V} [DecidableRel G.Adj] {k k' : Nat}
    (hk : G.IsKDegenerate k) (hle : k ≤ k') :
    G.IsKDegenerate k' := by
  intro s hs
  obtain ⟨v, hv, hdeg⟩ := hk s hs
  exact ⟨v, hv, Nat.le_trans hdeg hle⟩

omit [DecidableEq V] in
/-- The induced degree is at most the size of `s`. -/
theorem inducedDegree_le_card {G : SimpleGraph V} [DecidableRel G.Adj] (v : V) (s : Finset V) :
    G.inducedDegree v s ≤ s.card :=
  Finset.card_filter_le _ _

omit [DecidableEq V] in
/-- Every finite graph is k-degenerate for `k = |V|`. -/
theorem isKDegenerate_card (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V] :
    G.IsKDegenerate (Fintype.card V) := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  calc G.inducedDegree v s
      ≤ s.card := G.inducedDegree_le_card v s
    _ ≤ Fintype.card V := s.card_le_univ

omit [DecidableEq V] in
/-- The induced degree is monotone in the vertex set. -/
theorem inducedDegree_mono {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {s t : Finset V}
    (h : s ⊆ t) :
    G.inducedDegree v s ≤ G.inducedDegree v t :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [DecidableEq V] in
/-- K-degeneracy passes to every induced subgraph. -/
theorem IsKDegenerate.induce {G : SimpleGraph V} [DecidableRel G.Adj] {k : Nat}
    (hG : G.IsKDegenerate k) (t : Set V) :
    (G.induce t).IsKDegenerate k := by
  intro s hs
  let s' : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
  have hs' : s'.Nonempty := by
    obtain ⟨x, hx⟩ := hs
    exact ⟨x.val, Finset.mem_map_of_mem _ hx⟩
  obtain ⟨w, hw, hdeg⟩ := hG s' hs'
  rw [Finset.mem_map] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu, ?_⟩
  unfold inducedDegree at hdeg ⊢
  apply le_trans _ hdeg
  apply Finset.card_le_card_of_injOn (fun x => x.val)
  · intro x hx
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_map_of_mem _ (Finset.mem_filter.mp hx).1,
      SimpleGraph.induce_adj.mp (Finset.mem_filter.mp hx).2⟩
  · exact fun _ _ _ _ h => Subtype.val_injective h

omit [DecidableEq V] in
/-- Finset-specialized form of `IsKDegenerate.induce`. -/
theorem IsKDegenerate.induce_finset {G : SimpleGraph V} [DecidableRel G.Adj] {k : Nat}
    (hG : G.IsKDegenerate k) (t : Finset V) :
    (G.induce (t : Set V)).IsKDegenerate k :=
  hG.induce (t : Set V)

omit [DecidableEq V] in
/-- Deleting one vertex preserves k-degeneracy. -/
theorem IsKDegenerate.induce_ne {G : SimpleGraph V} [DecidableRel G.Adj] {k : Nat}
    (hG : G.IsKDegenerate k) (v : V) :
    (G.induce {w : V | w ≠ v}).IsKDegenerate k :=
  hG.induce {w : V | w ≠ v}

/-- A finite k-degenerate graph has at most `k * |V|` edges.

The proof repeatedly removes a vertex of degree at most `k`. Each removal
deletes exactly that vertex's degree many edges. -/
theorem IsKDegenerate.edgeFinset_card_le_mul_card (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : Nat} (hG : G.IsKDegenerate k) :
    G.edgeFinset.card ≤ k * Fintype.card V := by
  induction hcard : Fintype.card V using Nat.strongRecOn generalizing V with
  | _ n ih =>
    by_cases hV : Nonempty V
    · obtain ⟨v, _, hdeg⟩ :=
        hG Finset.univ ⟨Classical.arbitrary V, Finset.mem_univ _⟩
      let T : Set V := {v}ᶜ
      let G' : SimpleGraph T := G.induce T
      have hG' : G'.IsKDegenerate k := hG.induce T
      have hTcard : Fintype.card T = Fintype.card V - 1 := by
        simp [T, Fintype.card_compl_set]
      have hTlt : Fintype.card T < n := by
        rw [hTcard, ← hcard]
        exact Nat.sub_lt (Fintype.card_pos_iff.mpr hV) Nat.zero_lt_one
      have hIH : G'.edgeFinset.card ≤ k * Fintype.card T :=
        ih _ hTlt G' hG' rfl
      have hdegree : G.degree v ≤ k := by
        simpa [inducedDegree, degree, neighborFinset_eq_filter] using hdeg
      have hsplit : G'.edgeFinset.card = G.edgeFinset.card - G.degree v := by
        simpa [G', T] using
          (G.card_edgeFinset_induce_compl_singleton v).trans
            (G.card_edgeFinset_deleteIncidenceSet v)
      have hdegree_edges : G.degree v ≤ G.edgeFinset.card :=
        G.degree_le_card_edgeFinset v
      have hrestore :
          G.edgeFinset.card = G'.edgeFinset.card + G.degree v := by
        omega
      have hTsucc : Fintype.card T + 1 = Fintype.card V := by
        rw [hTcard]
        exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr hV)
      calc
        G.edgeFinset.card = G'.edgeFinset.card + G.degree v := hrestore
        _ ≤ k * Fintype.card T + k := Nat.add_le_add hIH hdegree
        _ = k * (Fintype.card T + 1) := by ring
        _ = k * Fintype.card V := by rw [hTsucc]
        _ = k * n := by rw [hcard]
    · rw [not_nonempty_iff] at hV
      letI : IsEmpty V := hV
      have hn : n = 0 := by
        rw [← hcard]
        exact Fintype.card_eq_zero
      have hedge : G.edgeFinset.card = 0 := by
        rw [Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e
        exact isEmptyElim e
      omega

omit [DecidableEq V] in
/-- Direct consequence of `IsKDegenerate`. -/
theorem IsKDegenerate.exists_low_degree_vertex {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKDegenerate k) (s : Finset V) (hs : s.Nonempty) :
    ∃ (v : V) (_ : v ∈ s), G.inducedDegree v s ≤ k :=
  hG s hs

/-! ## Degeneracy ordering -/

/-- A **degeneracy ordering** is a listing of all vertices of a finite graph such that each
vertex has at most `k` earlier neighbours in the list. -/
def IsDegeneracyOrdering (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (ord : List V) (k : Nat) : Prop :=
  ord.Nodup
  ∧ (∀ v : V, v ∈ ord)
  ∧ ∀ (i : Fin ord.length),
      (Finset.univ.filter (fun j : Fin ord.length =>
        j < i ∧ G.Adj (ord.get i) (ord.get j))).card ≤ k

/-- A graph admitting a degeneracy ordering is k-degenerate.

**Proof:** For any nonempty `s`, take the vertex in `s` that appears last in the ordering.
All its neighbours in `s` must appear earlier, so their count is bounded by `k`. -/
theorem isKDegenerate_of_degeneracy_order (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj]
    {ord : List V} {k : Nat}
    (h : G.IsDegeneracyOrdering ord k) :
    G.IsKDegenerate k := by
  intro s hs
  have hnodup := h.1
  have hmem := h.2.1
  have hbound := h.2.2
  -- Use the NoDup equivalence: Fin ord.length ≃ V
  let e := hnodup.getEquivOfForallMemList ord hmem
  -- Map vertices to their indices in ord
  let idx : V → Fin ord.length := e.symm
  -- Find the vertex in s with maximal index in ord
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image s (fun v => (idx v).val) hs
  refine ⟨v, hv, ?_⟩
  unfold inducedDegree
  -- Every w ∈ s with G.Adj v w has (idx w).val < (idx v).val
  have hinj : ∀ w ∈ s.filter (G.Adj v), (idx w).val < (idx v).val := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hne : w ≠ v := by intro heq; subst heq; exact G.irrefl hw.2
    have hle := hvmax w hw.1
    have hidx_ne : idx w ≠ idx v := by
      intro heq; exact hne (e.symm.injective heq)
    exact Nat.lt_of_le_of_ne hle (Fin.val_ne_of_ne hidx_ne)
  -- Inject s.filter (G.Adj v) into {j | j < idx v ∧ G.Adj ord[idx v] ord[j]}
  calc (s.filter (G.Adj v)).card
      ≤ (Finset.univ.filter (fun j : Fin ord.length =>
          j < idx v ∧ G.Adj (ord.get (idx v)) (ord.get j))).card := by
        apply Finset.card_le_card_of_injOn idx
        · intro w hw
          have hw' := Finset.mem_filter.mp hw
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          constructor
          · exact hinj w hw
          · -- ord.get (idx v) = v and ord.get (idx w) = w
            have hv_eq : ord.get (idx v) = v := by
              have := e.apply_symm_apply v
              rwa [List.Nodup.getEquivOfForallMemList_apply] at this
            have hw_eq : ord.get (idx w) = w := by
              have := e.apply_symm_apply w
              rwa [List.Nodup.getEquivOfForallMemList_apply] at this
            rw [hv_eq, hw_eq]
            exact hw'.2
        · intro w₁ _ w₂ _ heq; exact e.symm.injective heq
    _ ≤ k := hbound (idx v)

/-- Helper: `(l ++ [v]).get i = l.get i` when `i < l.length`. -/
private theorem get_append_left_aux {α : Type*} (l : List α) (v : α) (i : Nat)
    (hi : i < l.length) (hi' : i < (l ++ [v]).length) :
    (l ++ [v]).get ⟨i, hi'⟩ = l.get ⟨i, hi⟩ := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_left hi

/-- Helper: `(l ++ [v]).get l.length = v`. -/
private theorem get_append_right_aux {α : Type*} (l : List α) (v : α)
    (h : l.length < (l ++ [v]).length) :
    (l ++ [v]).get ⟨l.length, h⟩ = v := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (le_refl _)]
  simp

omit [DecidableEq V] in
/-- Auxiliary: for any Finset `s` of a k-degenerate graph, there exists a list covering `s`
that satisfies the bounded-earlier-neighbors property. Built by greedy elimination. -/
private theorem exists_ordering_aux (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKDegenerate k) :
    ∀ (s : Finset V), ∃ (l : List V),
      l.Nodup ∧ (∀ v, v ∈ l ↔ v ∈ s) ∧
      ∀ (i : Fin l.length),
        (Finset.univ.filter (fun j : Fin l.length =>
          j < i ∧ G.Adj (l.get i) (l.get j))).card ≤ k := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · -- Nonempty: extract low-degree vertex v, recurse on s \ {v}, append v
      obtain ⟨v, hv, hdeg⟩ := hG s hs
      obtain ⟨l', hnd', hmem', hbnd'⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
      -- v ∉ l' (since v ∉ s.erase v and l' covers s.erase v)
      have hv_not_in_l' : v ∉ l' := by
        intro habs
        exact (Finset.mem_erase.mp ((hmem' v).mp habs)).1 rfl
      refine ⟨l' ++ [v], ?_, ?_, ?_⟩
      · -- Nodup
        rw [List.nodup_append]
        refine ⟨hnd', List.nodup_singleton v, ?_⟩
        intro a ha b hb
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        subst hb
        intro heq
        exact hv_not_in_l' (heq ▸ ha)
      · -- Membership
        intro w
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        constructor
        · rintro (hw | rfl)
          · exact (Finset.mem_erase.mp ((hmem' w).mp hw)).2
          · exact hv
        · intro hw
          by_cases heq : w = v
          · right; exact heq
          · left; exact (hmem' w).mpr (Finset.mem_erase.mpr ⟨heq, hw⟩)
      · -- Bounded earlier neighbors
        intro ⟨i, hi⟩
        have hlen : (l' ++ [v]).length = l'.length + 1 := by simp
        by_cases hilt : i < l'.length
        · -- Position i < l'.length: vertex from l'
          -- get_append_left: (l' ++ [v]).get i = l'.get i
          -- All j < i also satisfy j < l'.length, so same elements
          -- Map j : Fin (l' ++ [v]).length to Fin l'.length
          -- We use: if j.val < l'.length then ⟨j.val, ...⟩ else ⟨0, ...⟩
          -- (the else branch is never used for filter members)
          have hlen_pos : 0 < l'.length := by omega
          let f : Fin (l' ++ [v]).length → Fin l'.length :=
            fun j => if h : j.val < l'.length then ⟨j.val, h⟩ else ⟨0, hlen_pos⟩
          calc (Finset.univ.filter (fun j : Fin (l' ++ [v]).length =>
                  j.val < i ∧ G.Adj ((l' ++ [v]).get ⟨i, hi⟩)
                    ((l' ++ [v]).get j))).card
              ≤ (Finset.univ.filter (fun j : Fin l'.length =>
                  j.val < i ∧ G.Adj (l'.get ⟨i, hilt⟩)
                    (l'.get j))).card := by
                apply Finset.card_le_card_of_injOn f
                · intro j hj
                  have hj' := (Finset.mem_filter.mp hj).2
                  have hjlt : j.val < l'.length := by omega
                  apply Finset.mem_filter.mpr
                  refine ⟨Finset.mem_univ _, ?_⟩
                  simp only [f, dif_pos hjlt]
                  constructor
                  · exact hj'.1
                  · -- Convert get on append to get on l'
                    have : G.Adj (l'.get ⟨i, hilt⟩) (l'.get ⟨j.val, hjlt⟩) := by
                      have := hj'.2
                      simp only [List.get_eq_getElem] at this ⊢
                      rwa [List.getElem_append_left hilt,
                           List.getElem_append_left hjlt] at this
                    exact this
                · intro j₁ hj₁ j₂ hj₂ heq
                  have hj₁' := (Finset.mem_filter.mp hj₁).2
                  have hj₂' := (Finset.mem_filter.mp hj₂).2
                  have h1 : j₁.val < l'.length := by omega
                  have h2 : j₂.val < l'.length := by omega
                  simp only [f, dif_pos h1, dif_pos h2, Fin.mk.injEq] at heq
                  exact Fin.ext heq
            _ ≤ k := hbnd' ⟨i, hilt⟩
        · -- Position i = l'.length: this is vertex v
          have hi_eq : i = l'.length := by omega
          subst hi_eq
          calc (Finset.univ.filter (fun j : Fin (l' ++ [v]).length =>
                  j.val < l'.length ∧ G.Adj ((l' ++ [v]).get ⟨l'.length, hi⟩)
                    ((l' ++ [v]).get j))).card
              ≤ (s.filter (G.Adj v)).card := by
                apply Finset.card_le_card_of_injOn
                  (fun (j : Fin (l' ++ [v]).length) => (l' ++ [v]).get j)
                · -- MapsTo: filter members map to s.filter (G.Adj v)
                  intro j hj
                  have hj_cond := (Finset.mem_filter.mp hj).2
                  have hjlt_cond : j.val < l'.length := hj_cond.1
                  have hadj_cond := hj_cond.2
                  apply Finset.mem_filter.mpr
                  simp only [List.get_eq_getElem] at hadj_cond ⊢
                  have key_j : (l' ++ [v])[j.val] = l'[j.val]'hjlt_cond :=
                    List.getElem_append_left hjlt_cond
                  have key_len : (l' ++ [v])[l'.length]'hi = v := by
                    rw [List.getElem_append_right (le_refl _)]; simp
                  constructor
                  · -- l'[j.val] ∈ s
                    rw [key_j]
                    have : l'[j.val]'hjlt_cond ∈ l' := List.getElem_mem hjlt_cond
                    exact (Finset.mem_erase.mp ((hmem' _).mp this)).2
                  · -- G.Adj v (l'[j.val])
                    convert hadj_cond using 1; simp [key_len]
                · -- InjOn
                  intro j₁ hj₁ j₂ hj₂ heq
                  have hj₁' := (Finset.mem_filter.mp hj₁).2
                  have hj₂' := (Finset.mem_filter.mp hj₂).2
                  have hj₁lt : j₁.val < l'.length := by omega
                  have hj₂lt : j₂.val < l'.length := by omega
                  simp only [List.get_eq_getElem] at heq
                  rw [List.getElem_append_left hj₁lt,
                      List.getElem_append_left hj₂lt] at heq
                  have hinj := List.nodup_iff_injective_getElem.mp hnd'
                  have heq' := @hinj ⟨j₁.val, hj₁lt⟩ ⟨j₂.val, hj₂lt⟩ heq
                  exact Fin.ext (by exact Fin.mk.injEq _ _ _ _ |>.mp heq')
            _ = G.inducedDegree v s := rfl
            _ ≤ k := hdeg
    · -- Empty case
      rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      exact ⟨[], List.nodup_nil, by simp, fun i => absurd i.isLt (by simp)⟩

/-- **Existence of a degeneracy ordering**: every finite k-degenerate graph has a degeneracy
ordering. -/
theorem exists_degeneracy_order (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKDegenerate k) :
    ∃ ord : List V, G.IsDegeneracyOrdering ord k := by
  obtain ⟨l, hnd, hmem, hbnd⟩ := exists_ordering_aux G hG Finset.univ
  exact ⟨l, hnd, fun v => (hmem v).mpr (Finset.mem_univ v), hbnd⟩

/-! ## Degeneracy bounds -/

omit [DecidableEq V] in
/-- The degeneracy of a k-degenerate graph is at most k. -/
theorem degeneracy_le_of_isKDegenerate (G : SimpleGraph V)
    [DecidableRel G.Adj]
    {k : Nat} (hG : G.IsKDegenerate k) :
    G.degeneracy ≤ k :=
  Nat.sInf_le hG

/-! ## Degeneracy from edge density [B4] -/

/-- The number of edges in the induced subgraph on `s`. -/
noncomputable def inducedEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) : Nat :=
  (G.induce (s : Set V)).edgeFinset.card

/-- Edge density hypothesis: `|E(G[s])| ≤ k * |V(G[s])|` for all nonempty `s`. -/
def HasEdgeDensityBound (G : SimpleGraph V) [DecidableRel G.Adj] (k : Nat) : Prop :=
  ∀ (s : Finset V), s.Nonempty → G.inducedEdgeCount s ≤ k * s.card

omit [DecidableEq V] in
/-- **[B4] Degeneracy from edge density:** If every induced subgraph of `G` has
    edge density at most `k`, then `G` is `2k`-degenerate.

    Uses the handshaking lemma and pigeonhole principle on the induced subgraph. -/
theorem isKDegenerate_of_edgeDensityBound (G : SimpleGraph V)
    [DecidableRel G.Adj]
    {k : Nat} (h : G.HasEdgeDensityBound k) :
    G.IsKDegenerate (2 * k) := by
  intro s hs
  let H := G.induce (s : Set V)
  -- Handshaking: sum of degrees = 2 * |edges|
  have hhand : ∑ v : { x : V // x ∈ (s : Set V) }, H.degree v =
      2 * H.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges H
  -- Edge density: |E(H)| ≤ k * |s|
  have hedge : H.edgeFinset.card ≤ k * s.card := h s hs
  -- Fintype.card of subtype = s.card
  have hcard : Fintype.card { x : V // x ∈ (s : Set V) } = s.card := by
    apply Fintype.subtype_card s
    intro x; simp
  -- Sum of degrees ≤ 2k * |s|
  have hne : (Finset.univ : Finset { x : V // x ∈ (s : Set V) }).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    obtain ⟨v, hv⟩ := hs
    exact ⟨⟨v, hv⟩⟩
  -- By pigeonhole: ∃ vertex with degree ≤ 2k
  have hsum' : ∑ v : { x : V // x ∈ (s : Set V) }, H.degree v ≤
      ∑ _v : { x : V // x ∈ (s : Set V) }, (2 * k) := by
    calc ∑ v, H.degree v
        = 2 * H.edgeFinset.card := hhand
      _ ≤ 2 * (k * s.card) := Nat.mul_le_mul_left 2 hedge
      _ = 2 * k * s.card := by ring
      _ = 2 * k * Fintype.card { x : V // x ∈ (s : Set V) } := by rw [hcard]
      _ = Fintype.card { x : V // x ∈ (s : Set V) } * (2 * k) := by ring
      _ = ∑ _v : { x : V // x ∈ (s : Set V) }, (2 * k) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  obtain ⟨v, _, hle⟩ := Finset.exists_le_of_sum_le hne hsum'
  -- Translate degree in induced graph to inducedDegree
  refine ⟨v.val, v.property, ?_⟩
  -- Need: inducedDegree v.val s ≤ 2 * k
  -- We have: H.degree v ≤ 2 * k
  -- And H.degree v = inducedDegree v.val s (both count neighbors of v in s)
  suffices H.degree v = G.inducedDegree v.val s by
    rw [← this]; exact hle
  -- Prove the degree translation
  unfold inducedDegree degree
  simp only [neighborFinset]
  -- Both count |{w ∈ s : G.Adj v.val w}|
  -- LHS: |(neighborSet of v in H).toFinset| where neighborSet = {u : subtype | H.Adj v u}
  -- RHS: |s.filter (G.Adj v.val)|
  -- H.Adj v u ↔ G.Adj v.val u.val by induce_adj
  -- So they have the same cardinality via the subtype ↔ finset bijection
  rw [Set.toFinset_card]
  -- Goal: Fintype.card (H.neighborSet v) = (s.filter (G.Adj v.val)).card
  rw [← Fintype.card_coe (s.filter (G.Adj v.val))]
  -- Now both sides are Fintype.card, use bijection
  apply Fintype.card_of_bijective
    (f := fun (u : H.neighborSet v) =>
      (⟨u.val.val, by
        rw [Finset.mem_filter]
        constructor
        · exact u.val.property
        · have := u.property
          rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj] at this
          exact this⟩ : { x // x ∈ s.filter (G.Adj v.val) }))
  constructor
  · intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  · intro ⟨w, hw⟩
    rw [Finset.mem_filter] at hw
    refine ⟨⟨⟨w, hw.1⟩, ?_⟩, by simp⟩
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj]
    exact hw.2

omit [DecidableEq V] in
/-- Corollary: If `G` has edge density bound `k`, its degeneracy is at most `2k`. -/
theorem degeneracy_le_two_mul_of_edgeDensityBound (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj]
    {k : Nat} (h : G.HasEdgeDensityBound k) :
    G.degeneracy ≤ 2 * k :=
  degeneracy_le_of_isKDegenerate G (isKDegenerate_of_edgeDensityBound G h)

end SimpleGraph
