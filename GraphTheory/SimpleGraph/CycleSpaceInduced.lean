/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.CycleCutSpace
import GraphTheory.SimpleGraph.BipartiteOddCycle
import GraphTheory.SimpleGraph.CycleExistence
import GraphTheory.SimpleGraph.Euler
import GraphTheory.SimpleGraph.LongestPath

/-!
# Cycle-space generation and edge-disjoint cycle decompositions

This file proves Diestel Proposition 1.9.1.  For a finite simple graph, the
characteristic vectors of its induced cycles span the kernel of the incidence
boundary map over `ZMod 2`.  It also proves the exact answer to Diestel
Chapter 1, Exercise 24: an edge set belongs to the cycle space precisely when
it is the union of a finite pairwise edge-disjoint family of cycles.
-/

namespace SimpleGraph

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of a walk, regarded as a finset in the edge type of its graph. -/
def Walk.edgeFinset {u v : V} (p : G.Walk u v) : Finset G.edgeFinset :=
  Finset.univ.filter fun e => (e.1 : Sym2 V) ∈ p.edges

@[simp]
theorem Walk.mem_edgeFinset {u v : V} (p : G.Walk u v) (e : G.edgeFinset) :
    e ∈ p.edgeFinset ↔ (e.1 : Sym2 V) ∈ p.edges := by
  simp [Walk.edgeFinset]

/-- The characteristic vector over `ZMod 2` of the edge set of a walk. -/
def Walk.edgeVector {u v : V} (p : G.Walk u v) : EdgeSpace G :=
  G.edgeIndicator p.edgeFinset

/-- A cycle is induced when every graph edge joining two vertices on the
cycle is itself an edge of the cycle. -/
def Walk.IsInducedCycle {v : V} (p : G.Walk v v) : Prop :=
  p.IsCycle ∧
    ∀ ⦃x y : V⦄, x ∈ p.support → y ∈ p.support →
      G.Adj x y → s(x, y) ∈ p.edges

/-- Characteristic vectors of all induced cycles of `G`. -/
def inducedCycleFamily : Set (EdgeSpace G) :=
  {f | ∃ (v : V) (p : G.Walk v v), p.IsInducedCycle ∧ f = p.edgeVector}

private theorem Walk.filter_edgeFinset_card_eq_count
    {v : V} {p : G.Walk v v} (hp : p.IsTrail) (x : V) :
    (p.edgeFinset.filter fun e => x ∈ (e.1 : Sym2 V)).card =
      (p.edges.filter fun e => decide (x ∈ e)).length := by
  rw [← List.toFinset_card_of_nodup (hp.edges_nodup.filter _)]
  apply Finset.card_bij
      (fun e (_ : e ∈ p.edgeFinset.filter fun e => x ∈ (e.1 : Sym2 V)) =>
        (e.1 : Sym2 V))
  · intro e he
    simp only [Finset.mem_filter, Walk.mem_edgeFinset] at he
    simp [he.1, he.2]
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro e he
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at he
    have heG : e ∈ G.edgeSet := Walk.edges_subset_edgeSet p he.1
    refine ⟨⟨e, G.mem_edgeFinset.mpr heG⟩, ?_, rfl⟩
    simp [he.1, he.2]

/-- Every cycle vector has zero boundary. -/
theorem Walk.edgeVector_mem_cycleSpace
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.edgeVector ∈ G.CycleSpace := by
  rw [Walk.edgeVector, G.edgeIndicator_mem_cycleSpace_iff_even_incident]
  intro x
  rw [Walk.filter_edgeFinset_card_eq_count (G := G) hp.isTrail x]
  rw [← List.countP_eq_length_filter]
  exact closed_trail_count_even hp.isTrail x

/-- The spanning subgraph whose edge set is a prescribed finset of edges of
`G`.  This local construction is used to extract a cycle from a nonzero
cycle-space vector. -/
private abbrev edgeSubgraph (F : Finset G.edgeFinset) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑(F.image Subtype.val) : Set (Sym2 V))

private theorem edgeFinset_edgeSubgraph (F : Finset G.edgeFinset) :
    (G.edgeSubgraph F).edgeFinset = F.image Subtype.val := by
  ext e
  simp only [edgeSubgraph, mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_diff,
    Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hdiag⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, G.not_isDiag_of_mem_edgeFinset a.prop⟩

private theorem degree_edgeSubgraph (F : Finset G.edgeFinset) (v : V) :
    (G.edgeSubgraph F).degree v =
      (F.filter fun e => v ∈ (e.1 : Sym2 V)).card := by
  rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter,
    G.edgeFinset_edgeSubgraph F]
  have hfilter :
      (F.image Subtype.val).filter (fun e => v ∈ e) =
        (F.filter fun e => v ∈ (e.1 : Sym2 V)).image Subtype.val := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hva⟩
      exact ⟨a, ⟨ha, hva⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hva⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hva⟩
  rw [hfilter, Finset.card_image_of_injective _ Subtype.val_injective]

private theorem exists_cycle_edgeFinset_subset
    (F : Finset G.edgeFinset)
    (hF : G.edgeIndicator F ∈ G.CycleSpace) (hne : F.Nonempty) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.edgeFinset ⊆ F := by
  have hEven :
      ∀ v : V, Even ((F.filter fun e => v ∈ (e.1 : Sym2 V)).card) :=
    (G.edgeIndicator_mem_cycleSpace_iff_even_incident F).mp hF
  let H := G.edgeSubgraph F
  letI : DecidableRel H.Adj := by
    dsimp [H]
    infer_instance
  letI : Nonempty H.support := by
    rcases hne with ⟨⟨e, heG⟩, heF⟩
    induction e using Sym2.ind with
    | h a b =>
      have habG : G.Adj a b := G.mem_edgeSet.mp (G.mem_edgeFinset.mp heG)
      have habH : H.Adj a b := by
        rw [show H = G.edgeSubgraph F by rfl]
        rw [edgeSubgraph, fromEdgeSet_adj]
        refine ⟨?_, habG.ne⟩
        exact Finset.mem_image.mpr ⟨⟨s(a, b), heG⟩, heF, rfl⟩
      exact ⟨⟨a, H.mem_support.mpr ⟨b, habH⟩⟩⟩
  let J := H.induce H.support
  have hdeg : ∀ w : H.support, 2 ≤ J.degree w := by
    intro w
    have hdegree :
        J.degree w = (F.filter fun e => (w : V) ∈ (e.1 : Sym2 V)).card := by
      calc
        J.degree w = H.degree w := by
          change (H.induce H.support).degree w = H.degree w
          exact H.degree_induce_support w
        _ = (F.filter fun e => (w : V) ∈ (e.1 : Sym2 V)).card := by
          simpa [H] using degree_edgeSubgraph (G := G) F (w : V)
    rw [hdegree]
    have heven := hEven w
    have hpos : 0 < (F.filter fun e => (w : V) ∈ (e.1 : Sym2 V)).card := by
      have hHFdegree :
          H.degree w =
            (F.filter fun e => (w : V) ∈ (e.1 : Sym2 V)).card := by
        simpa [H] using degree_edgeSubgraph (G := G) F (w : V)
      rw [← hHFdegree]
      exact (H.degree_pos_iff_mem_support w).mpr w.property
    rcases heven with ⟨k, hk⟩
    omega
  have hmin : 2 ≤ J.minDegree :=
    J.le_minDegree_of_forall_le_degree 2 hdeg
  have hnacyc : ¬ J.IsAcyclic :=
    J.not_isAcyclic_of_two_le_minDegree hmin
  have hex : ∃ (w : H.support) (q : J.Walk w w), q.IsCycle := by
    by_contra h
    apply hnacyc
    intro w q hq
    exact h ⟨w, q, hq⟩
  obtain ⟨w, q, hq⟩ := hex
  let qH : H.Walk (w : V) (w : V) :=
    q.map (Embedding.induce H.support).toHom
  have hqH : qH.IsCycle := hq.map Subtype.val_injective
  have hHG : H ≤ G := by
    rw [← edgeFinset_subset_edgeFinset]
    rw [show H.edgeFinset = (G.edgeSubgraph F).edgeFinset by rfl,
      G.edgeFinset_edgeSubgraph F]
    intro e he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    exact a.prop
  let qG : G.Walk (w : V) (w : V) := qH.mapLe hHG
  have hqG : qG.IsCycle := hqH.mapLe hHG
  refine ⟨w, qG, hqG, ?_⟩
  intro e he
  have heqG : (e.1 : Sym2 V) ∈ qG.edges :=
    (Walk.mem_edgeFinset (G := G) qG e).mp he
  have heqH : (e.1 : Sym2 V) ∈ qH.edges := by
    simpa only [qG, Walk.edges_mapLe_eq_edges] using heqG
  have heHset : (e.1 : Sym2 V) ∈ H.edgeSet :=
    Walk.edges_subset_edgeSet qH heqH
  have heHfin : (e.1 : Sym2 V) ∈ H.edgeFinset := H.mem_edgeFinset.mpr heHset
  rw [show H.edgeFinset = (G.edgeSubgraph F).edgeFinset by rfl,
    G.edgeFinset_edgeSubgraph F] at heHfin
  rcases Finset.mem_image.mp heHfin with ⟨a, ha, hae⟩
  have hae' : a = e := Subtype.ext hae
  simpa [hae'] using ha

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem Walk.start_end_edge_mem_of_length_eq_one
    {u v : V} (p : G.Walk u v) (h : p.length = 1) :
    s(u, v) ∈ p.edges := by
  cases p with
  | nil => simp at h
  | @cons u w v hadj q =>
      have hq0 : q.length = 0 := by
        rw [Walk.length_cons] at h
        omega
      have hwv : w = v := Walk.eq_of_length_eq_zero hq0
      subst v
      rw [Walk.length_eq_zero_iff] at hq0
      subst q
      simp

private theorem Walk.exists_shorter_cycles_edgeVector_add
    {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (hnind : ¬ p.IsInducedCycle) :
    ∃ (v₁ : V) (p₁ : G.Walk v₁ v₁) (v₂ : V) (p₂ : G.Walk v₂ v₂),
      p₁.IsCycle ∧ p₂.IsCycle ∧
      p₁.length < p.length ∧ p₂.length < p.length ∧
      p.edgeVector = p₁.edgeVector + p₂.edgeVector := by
  simp only [Walk.IsInducedCycle, hp, true_and] at hnind
  push Not at hnind
  obtain ⟨x, y, hx, hy, hxy, hchord⟩ := hnind
  have hxy_ne : x ≠ y := hxy.ne
  let c : G.Walk x x := p.rotate x hx
  have hc : c.IsCycle := hp.rotate hx
  have hyc : y ∈ c.support := (Walk.mem_support_rotate_iff p x hx).mpr hy
  let q₁ : G.Walk x y := c.takeUntil y hyc
  let q₂ : G.Walk y x := c.dropUntil y hyc
  have happ : q₁.append q₂ = c := c.take_spec hyc
  have hq₁path : q₁.IsPath := hc.isPath_takeUntil hyc
  have hcappend : (q₁.append q₂).IsCycle := by
    rw [happ]
    exact hc
  have hq₂path : q₂.IsPath :=
    hcappend.isPath_of_append_right (Walk.not_nil_of_ne hxy_ne)
  have hchordc : s(x, y) ∉ c.edges := by
    intro he
    exact hchord ((p.rotate_edges x hx).mem_iff.mp he)
  have hchordq₁ : s(x, y) ∉ q₁.edges :=
    fun he => hchordc (c.edges_takeUntil_subset hyc he)
  have hchordq₂ : s(x, y) ∉ q₂.edges :=
    fun he => hchordc (c.edges_dropUntil_subset hyc he)
  let c₁ : G.Walk x x := Walk.cons hxy q₂
  let c₂ : G.Walk y y := Walk.cons hxy.symm q₁
  have hc₁ : c₁.IsCycle := by
    dsimp [c₁]
    rw [Walk.cons_isCycle_iff]
    exact ⟨hq₂path, hchordq₂⟩
  have hc₂ : c₂.IsCycle := by
    dsimp [c₂]
    rw [Walk.cons_isCycle_iff]
    exact ⟨hq₁path, by simpa [Sym2.eq_swap] using hchordq₁⟩
  have hq₁two : 2 ≤ q₁.length := by
    have hpos : 0 < q₁.length := by
      rw [← Walk.not_nil_iff_lt_length]
      exact Walk.not_nil_of_ne hxy_ne
    by_contra htwo
    have hone : q₁.length = 1 := by omega
    exact hchordq₁
      (Walk.start_end_edge_mem_of_length_eq_one (G := G) q₁ hone)
  have hq₂two : 2 ≤ q₂.length := by
    have hpos : 0 < q₂.length := by
      rw [← Walk.not_nil_iff_lt_length]
      exact Walk.not_nil_of_ne hxy_ne.symm
    by_contra htwo
    have hone : q₂.length = 1 := by omega
    have : s(y, x) ∈ q₂.edges :=
      Walk.start_end_edge_mem_of_length_eq_one (G := G) q₂ hone
    exact hchordq₂ (by simpa [Sym2.eq_swap] using this)
  have hsum : q₁.length + q₂.length = c.length := by
    have := congrArg Walk.length happ
    simpa [Walk.length_append] using this
  have hcp : c.length = p.length := by
    dsimp [c, Walk.rotate]
    rw [Walk.length_append, add_comm, ← Walk.length_append, Walk.take_spec]
  have hc₁lt : c₁.length < p.length := by
    simp only [c₁, Walk.length_cons]
    omega
  have hc₂lt : c₂.length < p.length := by
    simp only [c₂, Walk.length_cons]
    omega
  have hdisj : q₁.edges.Disjoint q₂.edges :=
    hc.isTrail.disjoint_edges_takeUntil_dropUntil hyc
  have hpmem (e : Sym2 V) :
      e ∈ p.edges ↔ e ∈ q₁.edges ∨ e ∈ q₂.edges := by
    rw [← (p.rotate_edges x hx).mem_iff]
    change e ∈ c.edges ↔ _
    rw [← happ, Walk.edges_append, List.mem_append]
  have hvec : p.edgeVector = c₁.edgeVector + c₂.edgeVector := by
    funext e
    have hnotboth :
        ¬ ((e.1 : Sym2 V) ∈ q₁.edges ∧ (e.1 : Sym2 V) ∈ q₂.edges) :=
      fun h => hdisj h.1 h.2
    by_cases h₁ : (e.1 : Sym2 V) ∈ q₁.edges
    · have h₂ : (e.1 : Sym2 V) ∉ q₂.edges := fun he => hnotboth ⟨h₁, he⟩
      by_cases hd : (e.1 : Sym2 V) = s(x, y)
      · exact (hchordq₁ (by simpa [hd] using h₁)).elim
      · simp [Walk.edgeVector, edgeIndicator, c₁, c₂, (hpmem (e.1 : Sym2 V)),
          h₁, h₂, hd, Sym2.eq_swap]
    · by_cases h₂ : (e.1 : Sym2 V) ∈ q₂.edges
      · by_cases hd : (e.1 : Sym2 V) = s(x, y)
        · exact (hchordq₂ (by simpa [hd] using h₂)).elim
        · simp [Walk.edgeVector, edgeIndicator, c₁, c₂, (hpmem (e.1 : Sym2 V)),
            h₁, h₂, hd, Sym2.eq_swap]
      · by_cases hd : (e.1 : Sym2 V) = s(x, y)
        · have hpval : Walk.edgeVector G p e = 0 := by
            simp [Walk.edgeVector, edgeIndicator, hchord, hd]
          have hc₁val : Walk.edgeVector G c₁ e = 1 := by
            simp [Walk.edgeVector, edgeIndicator, c₁, hd]
          have hc₂val : Walk.edgeVector G c₂ e = 1 := by
            simp [Walk.edgeVector, edgeIndicator, c₂, hd, Sym2.eq_swap]
          change Walk.edgeVector G p e =
            Walk.edgeVector G c₁ e + Walk.edgeVector G c₂ e
          rw [hpval, hc₁val, hc₂val]
          exact (CharP.cast_eq_zero (ZMod 2) 2).symm
        · simp [Walk.edgeVector, edgeIndicator, c₁, c₂, (hpmem (e.1 : Sym2 V)),
            h₁, h₂, hd, Sym2.eq_swap]
  exact ⟨x, c₁, y, c₂, hc₁, hc₂, hc₁lt, hc₂lt, hvec⟩

/-- The characteristic vector of any cycle is a linear combination of
characteristic vectors of induced cycles. -/
theorem Walk.edgeVector_mem_span_inducedCycleFamily
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.edgeVector ∈ Submodule.span (ZMod 2) G.inducedCycleFamily := by
  induction hlen : p.length using Nat.strong_induction_on generalizing v p with
  | _ n ih =>
    by_cases hind : p.IsInducedCycle
    · apply Submodule.subset_span
      exact ⟨v, p, hind, rfl⟩
    · obtain ⟨v₁, p₁, v₂, p₂, hp₁, hp₂, hp₁lt, hp₂lt, hvec⟩ :=
        Walk.exists_shorter_cycles_edgeVector_add (G := G) hp hind
      have hspan₁ :
          p₁.edgeVector ∈ Submodule.span (ZMod 2) G.inducedCycleFamily :=
        ih p₁.length (hlen ▸ hp₁lt) hp₁ rfl
      have hspan₂ :
          p₂.edgeVector ∈ Submodule.span (ZMod 2) G.inducedCycleFamily :=
        ih p₂.length (hlen ▸ hp₂lt) hp₂ rfl
      rw [hvec]
      exact Submodule.add_mem _ hspan₁ hspan₂

private theorem edgeIndicator_eq_add_sdiff
    {C F : Finset G.edgeFinset} (hCF : C ⊆ F) :
    G.edgeIndicator F =
      G.edgeIndicator C + G.edgeIndicator (F \ C) := by
  funext e
  by_cases heC : e ∈ C
  · have heF : e ∈ F := hCF heC
    have heD : e ∉ F \ C := by simp [heC]
    simp [edgeIndicator, heC, heF, heD]
  · by_cases heF : e ∈ F
    · have heD : e ∈ F \ C := by simp [heF, heC]
      simp [edgeIndicator, heC, heF, heD]
    · have heD : e ∉ F \ C := by simp [heF]
      simp [edgeIndicator, heC, heF, heD]

/-- Every edge-set characteristic vector in the cycle space lies in the span
of induced-cycle vectors. -/
theorem edgeIndicator_mem_span_inducedCycleFamily
    (F : Finset G.edgeFinset)
    (hF : G.edgeIndicator F ∈ G.CycleSpace) :
    G.edgeIndicator F ∈
      Submodule.span (ZMod 2) G.inducedCycleFamily := by
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    by_cases hne : F.Nonempty
    · obtain ⟨v, p, hp, hpF⟩ :=
        exists_cycle_edgeFinset_subset (G := G) F hF hne
      let C : Finset G.edgeFinset := p.edgeFinset
      let R : Finset G.edgeFinset := F \ C
      have hCsub : C ⊆ F := hpF
      have hCne : C.Nonempty := by
        have hedges : p.edges ≠ [] := by
          intro he
          exact hp.not_nil (Walk.edges_eq_nil.mp he)
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges hedges
        have heG : e ∈ G.edgeSet := Walk.edges_subset_edgeSet p he
        let eG : G.edgeFinset := ⟨e, G.mem_edgeFinset.mpr heG⟩
        exact ⟨eG, (Walk.mem_edgeFinset (G := G) p eG).mpr he⟩
      have hCcycle : G.edgeIndicator C ∈ G.CycleSpace := by
        simpa [C, Walk.edgeVector] using
          Walk.edgeVector_mem_cycleSpace (G := G) hp
      have hCspan :
          G.edgeIndicator C ∈
            Submodule.span (ZMod 2) G.inducedCycleFamily := by
        simpa [C, Walk.edgeVector] using
          Walk.edgeVector_mem_span_inducedCycleFamily (G := G) hp
      have hdecomp :
          G.edgeIndicator F =
            G.edgeIndicator C + G.edgeIndicator R := by
        simpa [R] using edgeIndicator_eq_add_sdiff (G := G) hCsub
      have hRcycle : G.edgeIndicator R ∈ G.CycleSpace := by
        have hReq :
            G.edgeIndicator R =
              G.edgeIndicator F - G.edgeIndicator C := by
          rw [hdecomp]
          abel
        rw [hReq]
        exact Submodule.sub_mem _ hF hCcycle
      have hRlt : R.card < F.card := by
        have hCpos : 0 < C.card := Finset.card_pos.mpr hCne
        have hCle : C.card ≤ F.card := Finset.card_le_card hCsub
        dsimp [R]
        rw [Finset.card_sdiff_of_subset hCsub]
        omega
      have hRspan :
          G.edgeIndicator R ∈
            Submodule.span (ZMod 2) G.inducedCycleFamily :=
        ih R.card (hn ▸ hRlt) R hRcycle rfl
      rw [hdecomp]
      exact Submodule.add_mem _ hCspan hRspan
    · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst F
      have hzero : G.edgeIndicator ∅ = 0 := by
        funext e
        simp [edgeIndicator]
      rw [hzero]
      exact Submodule.zero_mem _

private def nonzeroEdgeFinset (f : EdgeSpace G) : Finset G.edgeFinset :=
  Finset.univ.filter fun e => f e ≠ 0

private theorem zmod_two_eq_zero_or_one (a : ZMod 2) :
    a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem edgeIndicator_nonzeroEdgeFinset (f : EdgeSpace G) :
    G.edgeIndicator (G.nonzeroEdgeFinset f) = f := by
  funext e
  obtain he | he := zmod_two_eq_zero_or_one (f e)
  · simp [edgeIndicator, nonzeroEdgeFinset, he]
  · simp [edgeIndicator, nonzeroEdgeFinset, he]

/-- **Diestel Proposition 1.9.1.**  The characteristic vectors
of the induced cycles of a finite simple graph generate its entire cycle
space over `ZMod 2`. -/
theorem cycleSpace_eq_span_inducedCycleFamily :
    G.CycleSpace =
      Submodule.span (ZMod 2) G.inducedCycleFamily := by
  apply le_antisymm
  · intro f hf
    let F := G.nonzeroEdgeFinset f
    have hrepr : G.edgeIndicator F = f := by
      simpa [F] using G.edgeIndicator_nonzeroEdgeFinset f
    have hFind : G.edgeIndicator F ∈ G.CycleSpace := by
      rw [hrepr]
      exact hf
    rw [← hrepr]
    exact G.edgeIndicator_mem_span_inducedCycleFamily F hFind
  · apply Submodule.span_le.mpr
    rintro f ⟨v, p, hp, rfl⟩
    exact Walk.edgeVector_mem_cycleSpace (G := G) hp.1

private noncomputable def edgeCoordinateSum :
    EdgeSpace G →ₗ[ZMod 2] ZMod 2 where
  toFun f := ∑ e, f e
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

private theorem edgeCoordinateSum_edgeIndicator
    (F : Finset G.edgeFinset) :
    G.edgeCoordinateSum (G.edgeIndicator F) = (F.card : ZMod 2) := by
  classical
  simp only [edgeCoordinateSum, LinearMap.coe_mk, AddHom.coe_mk, edgeIndicator,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  congr 1
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

private theorem Walk.card_edgeFinset_eq_length
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    p.edgeFinset.card = p.length := by
  rw [← p.length_edges, ← List.toFinset_card_of_nodup hp.edges_nodup]
  apply Finset.card_bij
      (fun e (_ : e ∈ p.edgeFinset) => (e.1 : Sym2 V))
  · intro e he
    simpa using (Walk.mem_edgeFinset (G := G) p e).mp he
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro e he
    have he' : e ∈ p.edges := by simpa using he
    have heG : e ∈ G.edgeSet := Walk.edges_subset_edgeSet p he'
    refine ⟨⟨e, G.mem_edgeFinset.mpr heG⟩, ?_, rfl⟩
    exact (Walk.mem_edgeFinset (G := G) p _).mpr he'

private theorem Walk.edgeCoordinateSum_edgeVector
    {u v : V} (p : G.Walk u v) :
    G.edgeCoordinateSum p.edgeVector = (p.edgeFinset.card : ZMod 2) := by
  simpa [Walk.edgeVector] using
    G.edgeCoordinateSum_edgeIndicator p.edgeFinset

/-- **Diestel Chapter 1, Exercise 21.**  A finite simple graph is bipartite
exactly when every induced cycle has even length. -/
theorem isBipartite_iff_forall_inducedCycle_even :
    G.IsBipartite ↔
      ∀ v : V, ∀ p : G.Walk v v, p.IsInducedCycle → Even p.length := by
  constructor
  · intro hG v p hp
    exact isBipartite_iff_forall_cycle_even.mp hG v p hp.1
  · intro hind
    rw [isBipartite_iff_forall_cycle_even]
    intro v p hp
    have hspan :
        Submodule.span (ZMod 2) G.inducedCycleFamily ≤
          LinearMap.ker G.edgeCoordinateSum := by
      apply Submodule.span_le.mpr
      rintro f ⟨w, q, hq, rfl⟩
      change G.edgeCoordinateSum q.edgeVector = 0
      rw [Walk.edgeCoordinateSum_edgeVector,
        ZMod.natCast_eq_zero_iff_even,
        Walk.card_edgeFinset_eq_length (G := G) q hq.1.isTrail]
      exact hind w q hq
    have hpSpan :
        p.edgeVector ∈ Submodule.span (ZMod 2) G.inducedCycleFamily :=
      Walk.edgeVector_mem_span_inducedCycleFamily (G := G) hp
    have hzero : G.edgeCoordinateSum p.edgeVector = 0 := hspan hpSpan
    rw [Walk.edgeCoordinateSum_edgeVector, ZMod.natCast_eq_zero_iff_even,
      Walk.card_edgeFinset_eq_length (G := G) p hp.isTrail] at hzero
    exact hzero

/-- A finite edge set has an edge-disjoint cycle decomposition when it is the
union of the edge sets of a finite family of pairwise edge-disjoint cycles. -/
def HasEdgeDisjointCycleDecomposition (F : Finset G.edgeFinset) : Prop :=
  ∃ (n : ℕ) (v : Fin n → V) (p : ∀ i, G.Walk (v i) (v i)),
    (∀ i, (p i).IsCycle) ∧
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i => (p i).edgeFinset) ∧
    (Finset.univ : Finset (Fin n)).biUnion (fun i => (p i).edgeFinset) = F

private lemma even_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

private theorem HasEdgeDisjointCycleDecomposition.mem_cycleSpace
    {F : Finset G.edgeFinset} (h : G.HasEdgeDisjointCycleDecomposition F) :
    G.edgeIndicator F ∈ G.CycleSpace := by
  rw [G.edgeIndicator_mem_cycleSpace_iff_even_incident]
  rcases h with ⟨n, v, p, hcycle, hdisjoint, rfl⟩
  intro x
  rw [Finset.filter_biUnion]
  have hdisjoint' :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (fun i => (p i).edgeFinset.filter fun e => x ∈ (e.1 : Sym2 V)) :=
    Finset.pairwiseDisjoint_filter hdisjoint _
  rw [Finset.card_biUnion hdisjoint']
  apply even_finset_sum
  intro i hi
  exact (G.edgeIndicator_mem_cycleSpace_iff_even_incident
    ((p i).edgeFinset)).mp
      (by simpa [Walk.edgeVector] using
        Walk.edgeVector_mem_cycleSpace (G := G) (hcycle i)) x

private theorem hasEdgeDisjointCycleDecomposition_of_mem_cycleSpace
    (F : Finset G.edgeFinset)
    (hF : G.edgeIndicator F ∈ G.CycleSpace) :
    G.HasEdgeDisjointCycleDecomposition F := by
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    by_cases hne : F.Nonempty
    · obtain ⟨v₀, p₀, hp₀, hp₀F⟩ :=
        exists_cycle_edgeFinset_subset (G := G) F hF hne
      let C : Finset G.edgeFinset := p₀.edgeFinset
      let R : Finset G.edgeFinset := F \ C
      have hCsub : C ⊆ F := hp₀F
      have hCne : C.Nonempty := by
        have hedges : p₀.edges ≠ [] := by
          intro he
          exact hp₀.not_nil (Walk.edges_eq_nil.mp he)
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p₀.edges hedges
        have heG : e ∈ G.edgeSet := Walk.edges_subset_edgeSet p₀ he
        let eG : G.edgeFinset := ⟨e, G.mem_edgeFinset.mpr heG⟩
        exact ⟨eG, (Walk.mem_edgeFinset (G := G) p₀ eG).mpr he⟩
      have hCcycle : G.edgeIndicator C ∈ G.CycleSpace := by
        simpa [C, Walk.edgeVector] using
          Walk.edgeVector_mem_cycleSpace (G := G) hp₀
      have hdecomp :
          G.edgeIndicator F = G.edgeIndicator C + G.edgeIndicator R := by
        simpa [R] using edgeIndicator_eq_add_sdiff (G := G) hCsub
      have hRcycle : G.edgeIndicator R ∈ G.CycleSpace := by
        have hReq :
            G.edgeIndicator R = G.edgeIndicator F - G.edgeIndicator C := by
          rw [hdecomp]
          abel
        rw [hReq]
        exact Submodule.sub_mem _ hF hCcycle
      have hRlt : R.card < F.card := by
        have hCpos : 0 < C.card := Finset.card_pos.mpr hCne
        have hCle : C.card ≤ F.card := Finset.card_le_card hCsub
        dsimp [R]
        rw [Finset.card_sdiff_of_subset hCsub]
        omega
      obtain ⟨m, v, p, hcycles, hpairwise, hunion⟩ :=
        ih R.card (hn ▸ hRlt) R hRcycle rfl
      let v' : Fin (m + 1) → V := Fin.cases v₀ v
      let p' : ∀ i, G.Walk (v' i) (v' i) := Fin.cases p₀ p
      refine ⟨m + 1, v', p', ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases hp₀ (fun j => ?_) i
        simpa [p'] using hcycles j
      · intro i _ j _ hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (hij rfl).elim
            | succ j' =>
                apply Finset.disjoint_of_subset_right
                  (show (p j').edgeFinset ⊆ R by
                    rw [← hunion]
                    exact Finset.subset_biUnion_of_mem
                      (fun i => (p i).edgeFinset) (Finset.mem_univ j'))
                exact Finset.disjoint_sdiff
        | succ i' =>
            cases j using Fin.cases with
            | zero =>
                apply Finset.disjoint_of_subset_left
                  (show (p i').edgeFinset ⊆ R by
                    rw [← hunion]
                    exact Finset.subset_biUnion_of_mem
                      (fun i => (p i).edgeFinset) (Finset.mem_univ i'))
                exact Finset.sdiff_disjoint
            | succ j' =>
                have hij' : i' ≠ j' := fun h => hij (congrArg Fin.succ h)
                simpa [p'] using hpairwise (Finset.mem_univ i')
                  (Finset.mem_univ j') hij'
      · ext e
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_succ]
        change (e ∈ C ∨ ∃ i, e ∈ (p i).edgeFinset) ↔ e ∈ F
        have hrest : (∃ i, e ∈ (p i).edgeFinset) ↔ e ∈ R := by
          rw [← hunion]
          simp
        rw [hrest]
        rw [show R = F \ C by rfl]
        simp only [Finset.mem_sdiff]
        constructor
        · rintro (heC | ⟨heF, -⟩)
          · exact hCsub heC
          · exact heF
        · intro heF
          by_cases heC : e ∈ C
          · exact Or.inl heC
          · exact Or.inr ⟨heF, heC⟩
    · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst F
      refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · simp

/-- **Diestel Chapter 1, Exercise 24.**  A finite set of edges belongs to the
cycle space exactly when it is the union of a finite pairwise edge-disjoint
family of cycles.  The empty edge set is represented by the empty family. -/
theorem edgeIndicator_mem_cycleSpace_iff_hasEdgeDisjointCycleDecomposition
    (F : Finset G.edgeFinset) :
    G.edgeIndicator F ∈ G.CycleSpace ↔
      G.HasEdgeDisjointCycleDecomposition F := by
  constructor
  · exact G.hasEdgeDisjointCycleDecomposition_of_mem_cycleSpace F
  · exact HasEdgeDisjointCycleDecomposition.mem_cycleSpace (G := G)

end SimpleGraph
