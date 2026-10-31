import GraphTheory.Local.TopologicalBridge

/-!
# Graph-valued split deficit

This file continues the formalization after the finite arithmetic ledger.  Its
goal is the actual theorem for finite simple planar 2-connected graphs, with
the split term defined by connected components after deleting the endpoints of
each edge.
-/

namespace PlaneTopology.Faces.SplitDeficit

open scoped BigOperators
open SimpleGraph
open KID981TopologicalBridge

namespace FiniteLedger

/-- Inequality form of the adjacent-two-cut arithmetic.  Exact equality of
the split sums is stronger than necessary: the induction closes as soon as
the parent split budget is at most the sum of the piece budgets plus `k-1`. -/
theorem split_recursion_aggregation_le
    {ι : Type*} [Fintype ι]
    (pieceVertices pieceEdges pieceSplit : ι → ℕ)
    (vertices edges splitTotal : ℕ)
    (hpiece : ∀ i,
      pieceEdges i + pieceSplit i + 6 ≤ 3 * pieceVertices i)
    (hvertices : (∑ i, pieceVertices i) + 2 =
      vertices + 2 * Fintype.card ι)
    (hedges : (∑ i, pieceEdges i) + 1 =
      edges + Fintype.card ι)
    (hsplit : splitTotal + 1 ≤
      (∑ i, pieceSplit i) + Fintype.card ι) :
    edges + splitTotal + 6 ≤ 3 * vertices := by
  have hsum :
      (∑ i, (pieceEdges i + pieceSplit i + 6)) ≤
        ∑ i, 3 * pieceVertices i :=
    Finset.sum_le_sum fun i _ => hpiece i
  have hleft :
      (∑ i, (pieceEdges i + pieceSplit i + 6)) =
        (∑ i, pieceEdges i) + (∑ i, pieceSplit i) +
          Fintype.card ι * 6 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id]
  have hright :
      (∑ i, 3 * pieceVertices i) = 3 * ∑ i, pieceVertices i := by
    rw [Finset.mul_sum]
  rw [hleft, hright] at hsum
  omega

end FiniteLedger

namespace PieceFacts

open KID981TopologicalBridge.PairDeletion
open KID981TopologicalBridge.AdjacentTwoCut

variable {V : Type*} [DecidableEq V]

/-- The vertices of one concrete split piece are exactly the disjoint sum of
the two separator vertices and the vertices of its chosen component. -/
noncomputable def pieceVertexEquiv
    (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent) :
    {x : V // x ∈ pieceVertexSet G e C} ≃
      {x : V // x ∈ deletedSet e} ⊕ C where
  toFun x := by
    classical
    by_cases hx : x.val ∈ deletedSet e
    · exact Sum.inl ⟨x.val, hx⟩
    · have hxLift : x.val ∈ liftedComponentSet G e C :=
        (mem_pieceVertexSet_iff G e C x.val).mp x.property |>.resolve_left hx
      exact Sum.inr ⟨⟨x.val, hxLift.choose⟩, hxLift.choose_spec⟩
  invFun x := match x with
    | Sum.inl y => ⟨y.val, (mem_pieceVertexSet_iff G e C y.val).mpr (Or.inl y.property)⟩
    | Sum.inr y => ⟨y.val.val,
        (mem_pieceVertexSet_iff G e C y.val.val).mpr
          (Or.inr ⟨y.val.property, y.property⟩)⟩
  left_inv x := by
    classical
    by_cases hx : x.val ∈ deletedSet e
    · simp [hx]
    · simp [hx]
  right_inv x := by
    classical
    cases x with
    | inl x => simp [x.property]
    | inr x =>
        have hx : x.val.val ∉ deletedSet e := x.val.property
        simp [hx]

/-- The paper's number `|C|+2` is the actual cardinality of the vertex type of
the concrete induced piece. -/
theorem natCard_pieceVertexSet
    [Fintype V] (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent) (he : ¬e.IsDiag) :
    Nat.card {x : V // x ∈ pieceVertexSet G e C} = Nat.card C + 2 := by
  rw [Nat.card_congr (pieceVertexEquiv G e C), Nat.card_sum,
    natCard_deletedSet_of_not_isDiag e he]
  omega

open Classical in
/-- Every concrete split piece has at least three vertices: its component is
nonempty and it also contains the two distinct separator endpoints. -/
theorem pieceVertex_card_ge_three
    [Fintype V] (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent) (he : ¬e.IsDiag) :
    3 ≤ Fintype.card {x : V // x ∈ pieceVertexSet G e C} := by
  haveI : Nonempty C := by
    obtain ⟨x, hx⟩ := C.nonempty_supp
    exact ⟨⟨x, hx⟩⟩
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hcard := natCard_pieceVertexSet G e C he
  rw [Fintype.card_eq_nat_card, hcard]
  omega

open Classical in
/-- If deletion of the separator has at least two components, every piece is
strictly smaller than the ambient graph.  This is the well-founded decrease
needed by strong induction. -/
theorem pieceVertex_card_lt
    [Fintype V] (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent) (he : ¬e.IsDiag)
    (hsplit : 2 ≤ edgeComponentCount G e) :
    Fintype.card {x : V // x ∈ pieceVertexSet G e C} < Fintype.card V := by
  let H := edgeGraph G e
  letI : Fintype H.ConnectedComponent := SetLike.instFintype
  have hcomponentCard : 2 ≤ Fintype.card H.ConnectedComponent := by
    simpa only [H, edgeComponentCount, Fintype.card_eq_nat_card] using hsplit
  haveI : Nontrivial H.ConnectedComponent :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨D, hDC⟩ := exists_ne C
  obtain ⟨y, hyD⟩ := D.nonempty_supp
  have hyNotRange : y ∉ Set.range (fun x : C => x.val) := by
    rintro ⟨x, rfl⟩
    apply hDC
    exact ConnectedComponent.eq_of_common_vertex x.property hyD |>.symm
  have hC_lt_deleted : Fintype.card C < Fintype.card {x : V // x ∈ (deletedSet e)ᶜ} :=
    Fintype.card_lt_of_injective_of_notMem (fun x : C => x.val)
      (fun _ _ hxy => Subtype.ext hxy) hyNotRange
  have hpiece := natCard_pieceVertexSet G e C he
  have hdeleted := natCard_edgeGraph_vertices_add_two (V := V) e he
  have hC_lt_deletedNat :
      Nat.card C < Nat.card {x : V // x ∈ (deletedSet e)ᶜ} := by
    simpa only [Fintype.card_eq_nat_card] using hC_lt_deleted
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  omega

/-! ### One-vertex deletion inside a piece -/

/-- Delete one vertex from a concrete piece, using a simple `x ≠ a` carrier
which is convenient for the connectivity argument. -/
def pieceDeleteOneGraph
    (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent)
    (a : {x : V // x ∈ pieceVertexSet G e C}) :
    SimpleGraph {x : {x : V // x ∈ pieceVertexSet G e C} // x ≠ a} :=
  (pieceGraph G e C).induce {x | x ≠ a}

/-- Delete the corresponding ambient vertex. -/
def ambientDeleteOneGraph (G : SimpleGraph V) (a : V) :
    SimpleGraph {x : V // x ≠ a} :=
  G.induce {x | x ≠ a}

/-- Inclusion of a once-deleted piece in the once-deleted ambient graph. -/
def pieceDeleteOneEmbedding
    (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent)
    (a : {x : V // x ∈ pieceVertexSet G e C}) :
    pieceDeleteOneGraph G e C a ↪g ambientDeleteOneGraph G a.val where
  toEmbedding :=
    { toFun := fun x => ⟨x.val.val, fun h => x.property (Subtype.ext h)⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : {x : V // x ≠ a.val} => z.val) hxy }
  map_rel_iff' := Iff.rfl

/-- Regard a surviving ambient vertex known to lie in the piece as a vertex
of the locally deleted piece. -/
def ambientDeleteOneToLocalOfMem
    (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent)
    (a : {x : V // x ∈ pieceVertexSet G e C})
    (z : {x : V // x ≠ a.val}) (hzPiece : z.val ∈ pieceVertexSet G e C) :
    {x : {x : V // x ∈ pieceVertexSet G e C} // x ≠ a} :=
  ⟨⟨z.val, hzPiece⟩, fun h => z.property (congrArg Subtype.val h)⟩

@[simp]
theorem pieceDeleteOneEmbedding_ambientDeleteOneToLocalOfMem
    (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent)
    (a : {x : V // x ∈ pieceVertexSet G e C})
    (z : {x : V // x ≠ a.val}) (hzPiece : z.val ∈ pieceVertexSet G e C) :
    pieceDeleteOneEmbedding G e C a
        (ambientDeleteOneToLocalOfMem G e C a z hzPiece) = z := by
  apply Subtype.ext
  rfl

/-- Ambient survivors which can be represented by a locally reachable piece
vertex. -/
def localReachSet
    (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent)
    (a : {x : V // x ∈ pieceVertexSet G e C})
    (x : {z : {x : V // x ∈ pieceVertexSet G e C} // z ≠ a}) :
    Set {z : V // z ≠ a.val} :=
  {z | ∃ hzPiece : z.val ∈ pieceVertexSet G e C,
    (pieceDeleteOneGraph G e C a).Reachable x
      (ambientDeleteOneToLocalOfMem G e C a z hzPiece)}

open Classical in
/-- Connectivity engine for one deleted vertex.  If one surviving separator
vertex is chosen as an anchor and every other surviving separator vertex can
reach it inside the piece, ambient 2-connectivity forces the whole deleted
piece to be connected. -/
theorem pieceDeleteOneGraph_connected_of_anchor
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (a q : {x : V // x ∈ pieceVertexSet G e C})
    (hqa : q ≠ a)
    (hseparatorReach :
      ∀ (p : {x : V // x ∈ pieceVertexSet G e C})
        (_hp : p.val ∈ deletedSet e) (hpa : p ≠ a),
        (pieceDeleteOneGraph G e C a).Reachable ⟨p, hpa⟩ ⟨q, hqa⟩) :
    (pieceDeleteOneGraph G e C a).Connected := by
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hAmbientConnected : (ambientDeleteOneGraph G a.val).Connected := by
    have hdelete := hG.isVertexConnected.2 ({a.val} : Finset V) (by simp)
    have hset :
        (((Finset.univ \ {a.val} : Finset V) : Set V)) = {x : V | x ≠ a.val} := by
      ext x
      simp
    rw [hset] at hdelete
    exact hdelete
  rw [connected_iff]
  constructor
  · intro x y
    have reachAnchor :
        ∀ z : {z : {x : V // x ∈ pieceVertexSet G e C} // z ≠ a},
          (pieceDeleteOneGraph G e C a).Reachable z ⟨q, hqa⟩ := by
      intro z
      by_contra hnot
      let zAmbient := pieceDeleteOneEmbedding G e C a z
      let qAmbient := pieceDeleteOneEmbedding G e C a ⟨q, hqa⟩
      have hAmbientReach :
          (ambientDeleteOneGraph G a.val).Reachable zAmbient qAmbient :=
        hAmbientConnected.preconnected zAmbient qAmbient
      let Q : (ambientDeleteOneGraph G a.val).Subgraph :=
        (⊤ : (ambientDeleteOneGraph G a.val).Subgraph).induce
          (localReachSet G e C a z)
      have hzQ : zAmbient ∈ Q.verts := by
        change zAmbient ∈ localReachSet G e C a z
        refine ⟨z.val.property, ?_⟩
        have heq :
            ambientDeleteOneToLocalOfMem G e C a zAmbient z.val.property = z := by
          apply Subtype.ext
          apply Subtype.ext
          rfl
        rw [heq]
      have hclosed :
          ∀ v ∈ Q.verts, ∀ w,
            (ambientDeleteOneGraph G a.val).Adj v w → Q.Adj v w := by
        intro v hvQ w hvw
        have hvReachSet : v ∈ localReachSet G e C a z := by
          exact hvQ
        obtain ⟨hvPiece, hzv⟩ := hvReachSet
        let vLocal := ambientDeleteOneToLocalOfMem G e C a v hvPiece
        have hvNotSeparator : v.val ∉ deletedSet e := by
          intro hvSeparator
          have hvNeA :
              (⟨v.val, hvPiece⟩ : {x : V // x ∈ pieceVertexSet G e C}) ≠ a := by
            intro h
            exact v.property (congrArg Subtype.val h)
          have hvqRaw := hseparatorReach ⟨v.val, hvPiece⟩ hvSeparator hvNeA
          have hvq :
              (pieceDeleteOneGraph G e C a).Reachable vLocal ⟨q, hqa⟩ := by
            exact hvqRaw
          exact hnot (hzv.trans hvq)
        have hwPiece : w.val ∈ pieceVertexSet G e C := by
          by_cases hwSeparator : w.val ∈ deletedSet e
          · have hwPiece' : w.val ∈ pieceVertexSet G e C := Or.inl hwSeparator
            have hwNeA :
                (⟨w.val, hwPiece'⟩ : {x : V // x ∈ pieceVertexSet G e C}) ≠ a := by
              intro h
              exact w.property (congrArg Subtype.val h)
            let wLocal := ambientDeleteOneToLocalOfMem G e C a w hwPiece'
            have hvwLocal :
                (pieceDeleteOneGraph G e C a).Adj vLocal wLocal := by
              exact hvw
            have hzw :
                (pieceDeleteOneGraph G e C a).Reachable z wLocal :=
              hzv.trans hvwLocal.reachable
            have hwqRaw := hseparatorReach ⟨w.val, hwPiece'⟩ hwSeparator hwNeA
            have hwq :
                (pieceDeleteOneGraph G e C a).Reachable wLocal ⟨q, hqa⟩ := by
              exact hwqRaw
            exact False.elim (hnot (hzw.trans hwq))
          · have hvLift : v.val ∈ liftedComponentSet G e C :=
              (mem_pieceVertexSet_iff G e C v.val).mp hvPiece
                |>.resolve_left hvNotSeparator
            obtain ⟨hvOut, hvC⟩ :=
              (mem_liftedComponentSet_iff G e C v.val).mp hvLift
            have hwOut : w.val ∈ (deletedSet e)ᶜ := hwSeparator
            let vDeleted : {x : V // x ∈ (deletedSet e)ᶜ} := ⟨v.val, hvOut⟩
            let wDeleted : {x : V // x ∈ (deletedSet e)ᶜ} := ⟨w.val, hwOut⟩
            have hvwDeleted : (edgeGraph G e).Adj vDeleted wDeleted := by
              exact hvw
            have hwC : wDeleted ∈ C.supp :=
              C.mem_supp_of_adj_mem_supp hvC hvwDeleted
            exact Or.inr ⟨hwOut, hwC⟩
        let wLocal := ambientDeleteOneToLocalOfMem G e C a w hwPiece
        have hvwLocal :
            (pieceDeleteOneGraph G e C a).Adj vLocal wLocal := by
          exact hvw
        have hwReachSet : w ∈ localReachSet G e C a z :=
          ⟨hwPiece, hzv.trans hvwLocal.reachable⟩
        exact ⟨⟨hvPiece, hzv⟩, hwReachSet, hvw⟩
      have hqQ : qAmbient ∈ Q.verts :=
        hAmbientReach.mem_subgraphVerts hclosed hzQ
      have hqReachSet : qAmbient ∈ localReachSet G e C a z := hqQ
      obtain ⟨hqPiece, hzq⟩ := hqReachSet
      have heq :
          ambientDeleteOneToLocalOfMem G e C a qAmbient hqPiece = ⟨q, hqa⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      exact hnot (heq ▸ hzq)
    exact (reachAnchor x).trans (reachAnchor y).symm
  · exact ⟨⟨q, hqa⟩⟩

open Classical in
/-- Removing any one vertex from a concrete adjacent-two-cut piece leaves it
connected.  The surviving endpoint of the separator edge is the anchor
required by `pieceDeleteOneGraph_connected_of_anchor`. -/
theorem pieceDeleteOneGraph_connected
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (C : (edgeGraph G e).ConnectedComponent)
    (a : {x : V // x ∈ pieceVertexSet G e C}) :
    (pieceDeleteOneGraph G e C a).Connected := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := G.mem_edgeFinset.mp heG
      have huPiece : u ∈ pieceVertexSet G s(u, v) C :=
        Or.inl (by simp [deletedSet])
      have hvPiece : v ∈ pieceVertexSet G s(u, v) C :=
        Or.inl (by simp [deletedSet])
      let uPiece : {x : V // x ∈ pieceVertexSet G s(u, v) C} := ⟨u, huPiece⟩
      let vPiece : {x : V // x ∈ pieceVertexSet G s(u, v) C} := ⟨v, hvPiece⟩
      by_cases ha : a.val = u
      · have hva : vPiece ≠ a := by
          intro h
          have hvEq : v = a.val := congrArg Subtype.val h
          exact huv.ne (ha.symm.trans hvEq.symm)
        apply pieceDeleteOneGraph_connected_of_anchor
          G hcard hG s(u, v) C a vPiece hva
        intro p hp hpa
        have hpEnds : p.val = u ∨ p.val = v := by
          simpa [deletedSet] using hp
        rcases hpEnds with hpu | hpv
        · have hpaEq : p = a := Subtype.ext (hpu.trans ha.symm)
          exact False.elim (hpa hpaEq)
        · have hpEq : p = vPiece := Subtype.ext hpv
          subst p
          exact Reachable.rfl
      · have hua : uPiece ≠ a := by
          intro h
          exact ha (congrArg Subtype.val h).symm
        apply pieceDeleteOneGraph_connected_of_anchor
          G hcard hG s(u, v) C a uPiece hua
        intro p hp hpa
        have hpEnds : p.val = u ∨ p.val = v := by
          simpa [deletedSet] using hp
        rcases hpEnds with hpu | hpv
        · have hpEq : p = uPiece := Subtype.ext hpu
          subst p
          exact Reachable.rfl
        · have hpEq : p = vPiece := Subtype.ext hpv
          subst p
          apply Adj.reachable
          change G.Adj v u
          exact huv.symm

open Classical in
/-- Every concrete piece is connected.  Delete one separator endpoint, use
the preceding no-cut lemma, and attach that endpoint back along the separator
edge. -/
theorem pieceGraph_connected
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (C : (edgeGraph G e).ConnectedComponent) :
    (pieceGraph G e C).Connected := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := G.mem_edgeFinset.mp heG
      have huPiece : u ∈ pieceVertexSet G s(u, v) C :=
        Or.inl (by simp [deletedSet])
      have hvPiece : v ∈ pieceVertexSet G s(u, v) C :=
        Or.inl (by simp [deletedSet])
      let uPiece : {x : V // x ∈ pieceVertexSet G s(u, v) C} := ⟨u, huPiece⟩
      let vPiece : {x : V // x ∈ pieceVertexSet G s(u, v) C} := ⟨v, hvPiece⟩
      have huvPiece : uPiece ≠ vPiece := by
        intro h
        exact huv.ne (congrArg Subtype.val h)
      have hdelete := pieceDeleteOneGraph_connected
        G hcard hG s(u, v) heG C uPiece
      rw [connected_iff]
      constructor
      · intro x y
        have reachV :
            ∀ z : {x : V // x ∈ pieceVertexSet G s(u, v) C},
              (pieceGraph G s(u, v) C).Reachable z vPiece := by
          intro z
          by_cases hzu : z = uPiece
          · subst z
            apply Adj.reachable
            change G.Adj u v
            exact huv
          · let zDeleted :
                {z : {x : V // x ∈ pieceVertexSet G s(u, v) C} // z ≠ uPiece} :=
              ⟨z, hzu⟩
            let vDeleted :
                {z : {x : V // x ∈ pieceVertexSet G s(u, v) C} // z ≠ uPiece} :=
              ⟨vPiece, huvPiece.symm⟩
            have hzv := hdelete.preconnected zDeleted vDeleted
            exact hzv.map
              (Embedding.induce
                ({z : {x : V // x ∈ pieceVertexSet G s(u, v) C} | z ≠ uPiece})
                (G := pieceGraph G s(u, v) C)).toHom
        exact (reachV x).trans (reachV y).symm
      · exact ⟨uPiece⟩

open Classical in
/-- The standard adjacent-two-cut pieces of a finite 2-connected graph are
themselves 2-connected.  This discharges the structural induction hypothesis
which was still explicit in the earlier ledger. -/
theorem pieceGraph_isKConnected_two
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (C : (edgeGraph G e).ConnectedComponent) :
    (pieceGraph G e C).IsKConnected 2 := by
  have he : ¬e.IsDiag :=
    G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp heG)
  have hpieceCard := pieceVertex_card_ge_three G e C he
  have hpieceConnected := pieceGraph_connected G hcard hG e heG C
  have hVC : (pieceGraph G e C).IsVertexConnected 2 := by
    refine ⟨by omega, ?_⟩
    intro S hS
    interval_cases hScard : S.card
    · have hS : S = ∅ := Finset.card_eq_zero.mp hScard
      subst S
      have hset :
          (((Finset.univ \ ∅ : Finset {x : V // x ∈ pieceVertexSet G e C}) :
            Set {x : V // x ∈ pieceVertexSet G e C})) = Set.univ := by
        ext x
        simp
      rw [hset]
      exact (pieceGraph G e C).induceUnivIso.connected_iff.mpr hpieceConnected
    · rw [Finset.card_eq_one] at hScard
      obtain ⟨a, rfl⟩ := hScard
      have hset :
          (((Finset.univ \ {a} : Finset {x : V // x ∈ pieceVertexSet G e C}) :
            Set {x : V // x ∈ pieceVertexSet G e C})) = {x | x ≠ a} := by
        ext x
        simp
      rw [hset]
      exact pieceDeleteOneGraph_connected G hcard hG e heG C a
  haveI : Nontrivial {x : V // x ∈ pieceVertexSet G e C} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact (pieceGraph G e C).le_vertexConnectivity_of_isVertexConnected hVC

/-- The copy of the chosen separator edge inside a concrete piece. -/
noncomputable def separatorEdgeInPiece
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (heG : e ∈ G.edgeFinset) :
    Sym2 {x : V // x ∈ pieceVertexSet G e C} :=
  liftEdgeToPiece G e C e (separator_mem_pieceAmbientEdges G e C heG)

/-- Deleting the separator ends from one piece leaves precisely the connected
component which indexes that piece.  This graph isomorphism makes that paper
statement literal rather than encoding it as a component-count assumption. -/
noncomputable def deleteSeparatorPieceIso
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (heG : e ∈ G.edgeFinset) :
    edgeGraph (pieceGraph G e C) (separatorEdgeInPiece G e C heG) ≃g
      C.toSimpleGraph where
  toEquiv :=
    { toFun := fun x => by
        have hxNotE : x.val.val ∉ e := by
          intro hxE
          apply x.property
          exact Sym2.mem_toFinset.mpr
            ((mem_liftEdgeToPiece_iff G e C e
              (separator_mem_pieceAmbientEdges G e C heG) x.val).mpr hxE)
        have hxNotDeleted : x.val.val ∉ deletedSet e := by
          intro hx
          exact hxNotE (Sym2.mem_toFinset.mp hx)
        have hxLift : x.val.val ∈ liftedComponentSet G e C :=
          (mem_pieceVertexSet_iff G e C x.val.val).mp x.val.property
            |>.resolve_left hxNotDeleted
        exact ⟨⟨x.val.val, hxLift.choose⟩, hxLift.choose_spec⟩
      invFun := fun y => by
        let yp : {x : V // x ∈ pieceVertexSet G e C} :=
          ⟨y.val.val, (mem_pieceVertexSet_iff G e C y.val.val).mpr
            (Or.inr ⟨y.val.property, y.property⟩)⟩
        refine ⟨yp, ?_⟩
        intro hyLocalFinset
        have hyLocal : yp ∈ separatorEdgeInPiece G e C heG :=
          Sym2.mem_toFinset.mp hyLocalFinset
        have hyAmbient : y.val.val ∈ e :=
          (mem_liftEdgeToPiece_iff G e C e
            (separator_mem_pieceAmbientEdges G e C heG) yp).mp hyLocal
        exact y.val.property (Sym2.mem_toFinset.mpr hyAmbient)
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  map_rel_iff' := by
    intro x y
    rfl

/-- The local split multiplicity of the duplicated separator edge is zero. -/
theorem separatorEdgeInPiece_multiplicity_eq_zero
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (heG : e ∈ G.edgeFinset) :
    edgeMultiplicity (pieceGraph G e C) (separatorEdgeInPiece G e C heG) = 0 := by
  classical
  have hconn :
      (edgeGraph (pieceGraph G e C) (separatorEdgeInPiece G e C heG)).Connected :=
    (deleteSeparatorPieceIso G e C heG).connected_iff.mpr C.connected_toSimpleGraph
  have hcard :
      Nat.card
          (edgeGraph (pieceGraph G e C)
            (separatorEdgeInPiece G e C heG)).ConnectedComponent = 1 := by
    rw [← Fintype.card_eq_nat_card]
    exact connected_card_connectedComponent hconn
  unfold edgeMultiplicity edgeComponentCount
  rw [hcard]

open Classical in
/-- An ambient edge assigned to a piece becomes an actual edge of the induced
piece graph after its endpoints are lifted to the vertex subtype. -/
theorem liftEdgeToPiece_mem_edgeFinset
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (f : Sym2 V) (hf : f ∈ pieceAmbientEdges G e C) :
    liftEdgeToPiece G e C f hf ∈ (pieceGraph G e C).edgeFinset := by
  classical
  let emb := (Function.Embedding.subtype (· ∈ pieceVertexSet G e C)).sym2Map
  have hfMap : f ∈ (pieceGraph G e C).edgeFinset.map emb := by
    rw [map_pieceGraph_edgeFinset G e C]
    exact hf
  obtain ⟨g, hg, hgf⟩ := Finset.mem_map.mp hfMap
  have hEq : g = liftEdgeToPiece G e C f hf := by
    apply emb.injective
    change g.map Subtype.val = (liftEdgeToPiece G e C f hf).map Subtype.val
    rw [map_liftEdgeToPiece G e C f hf]
    exact hgf
  apply SimpleGraph.mem_edgeFinset.mpr
  apply SimpleGraph.mem_edgeFinset.mp
  rw [← hEq]
  exact hg

open Classical in
/-- Mapping a genuine local piece edge back to the ambient vertex type lands
in the finite set of ambient edges assigned to that piece. -/
theorem mapPieceEdge_mem_pieceAmbientEdges
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (g : Sym2 {x : V // x ∈ pieceVertexSet G e C})
    (hg : g ∈ (pieceGraph G e C).edgeFinset) :
    g.map Subtype.val ∈ pieceAmbientEdges G e C := by
  let emb := (Function.Embedding.subtype (· ∈ pieceVertexSet G e C)).sym2Map
  have hgMap : g.map Subtype.val ∈
      (pieceGraph G e C).edgeFinset.map emb :=
    Finset.mem_map.mpr ⟨g, hg, rfl⟩
  have hmap :
      (pieceGraph G e C).edgeFinset.map emb = pieceAmbientEdges G e C := by
    simpa only [emb] using map_pieceGraph_edgeFinset G e C
  rw [hmap] at hgMap
  exact hgMap

open Classical in
/-- The actual edges of a piece are equivalent to their ambient copies.  The
inverse is the proof-carrying `liftEdgeToPiece`; hence later sums can be
reindexed without choosing endpoints or an orientation. -/
noncomputable def pieceEdgeEquiv
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent) :
    {g : Sym2 {x : V // x ∈ pieceVertexSet G e C} //
        g ∈ (pieceGraph G e C).edgeFinset} ≃
      {f : Sym2 V // f ∈ pieceAmbientEdges G e C} where
  toFun g := by
    exact ⟨g.val.map Subtype.val,
      mapPieceEdge_mem_pieceAmbientEdges G e C g.val g.property⟩
  invFun f :=
    ⟨liftEdgeToPiece G e C f.val f.property,
      liftEdgeToPiece_mem_edgeFinset G e C f.val f.property⟩
  left_inv g := by
    apply Subtype.ext
    let emb := (Function.Embedding.subtype (· ∈ pieceVertexSet G e C)).sym2Map
    apply emb.injective
    change
      (liftEdgeToPiece G e C (g.val.map Subtype.val)
        (mapPieceEdge_mem_pieceAmbientEdges G e C g.val g.property)).map Subtype.val =
        g.val.map Subtype.val
    exact map_liftEdgeToPiece G e C (g.val.map Subtype.val)
      (mapPieceEdge_mem_pieceAmbientEdges G e C g.val g.property)
  right_inv f := by
    apply Subtype.ext
    exact map_liftEdgeToPiece G e C f.val f.property

open Classical in
/-- Reindex the concrete split total of a piece by the corresponding ambient
piece edges. -/
theorem pieceSplitTotal_eq_sum_ambient
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent) :
    ConcreteLedger.splitTotal (pieceGraph G e C) =
      ∑ f : {f : Sym2 V // f ∈ pieceAmbientEdges G e C},
        edgeMultiplicity (pieceGraph G e C)
          (liftEdgeToPiece G e C f.val f.property) := by
  classical
  unfold ConcreteLedger.splitTotal
  calc
    (∑ f ∈ (pieceGraph G e C).edgeFinset,
        edgeMultiplicity (pieceGraph G e C) f) =
        ∑ g : {g // g ∈ (pieceGraph G e C).edgeFinset},
          edgeMultiplicity (pieceGraph G e C) g.val := by
      rw [← Finset.sum_attach]
      simp
    _ = ∑ f : {f : Sym2 V // f ∈ pieceAmbientEdges G e C},
          edgeMultiplicity (pieceGraph G e C)
            (liftEdgeToPiece G e C f.val f.property) := by
      refine Fintype.sum_equiv (pieceEdgeEquiv G e C) _ _ ?_
      intro g
      change edgeMultiplicity (pieceGraph G e C) g.val =
        edgeMultiplicity (pieceGraph G e C)
          ((pieceEdgeEquiv G e C).symm ((pieceEdgeEquiv G e C) g)).val
      rw [Equiv.symm_apply_apply]

/-- Local split multiplicity of an ambient unordered pair, extended by zero
outside the edge set of the selected piece.  The total function removes
proof-dependence from subsequent `Finset` sums. -/
noncomputable def localMultiplicityOnAmbient
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (f : Sym2 V) : ℕ :=
  if hf : f ∈ pieceAmbientEdges G e C then
    edgeMultiplicity (pieceGraph G e C) (liftEdgeToPiece G e C f hf)
  else 0

open Classical in
@[simp]
theorem localMultiplicityOnAmbient_of_mem
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (f : Sym2 V) (hf : f ∈ pieceAmbientEdges G e C) :
    localMultiplicityOnAmbient G e C f =
      edgeMultiplicity (pieceGraph G e C) (liftEdgeToPiece G e C f hf) := by
  simp only [localMultiplicityOnAmbient, dif_pos hf]

open Classical in
/-- Finset form of `pieceSplitTotal_eq_sum_ambient`. -/
theorem pieceSplitTotal_eq_sum_localMultiplicity
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent) :
    ConcreteLedger.splitTotal (pieceGraph G e C) =
      ∑ f ∈ pieceAmbientEdges G e C, localMultiplicityOnAmbient G e C f := by
  calc
    ConcreteLedger.splitTotal (pieceGraph G e C) =
        ∑ f : {f : Sym2 V // f ∈ pieceAmbientEdges G e C},
          edgeMultiplicity (pieceGraph G e C)
            (liftEdgeToPiece G e C f.val f.property) :=
      pieceSplitTotal_eq_sum_ambient G e C
    _ = ∑ f : {f : Sym2 V // f ∈ pieceAmbientEdges G e C},
          localMultiplicityOnAmbient G e C f.val := by
      apply Finset.sum_congr rfl
      intro f _
      symm
      exact localMultiplicityOnAmbient_of_mem G e C f.val f.property
    _ = ∑ f ∈ pieceAmbientEdges G e C,
          localMultiplicityOnAmbient G e C f := by
      symm
      calc
        (∑ f ∈ pieceAmbientEdges G e C,
            localMultiplicityOnAmbient G e C f) =
            ∑ f ∈ (pieceAmbientEdges G e C).attach,
              localMultiplicityOnAmbient G e C f.val :=
          (Finset.sum_attach (pieceAmbientEdges G e C)
            (localMultiplicityOnAmbient G e C)).symm
        _ = ∑ f : {f : Sym2 V // f ∈ pieceAmbientEdges G e C},
              localMultiplicityOnAmbient G e C f.val := by simp

open Classical in
/-- The selected separator contributes zero inside every piece. -/
theorem localMultiplicityOnAmbient_separator_eq_zero
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (heG : e ∈ G.edgeFinset) :
    localMultiplicityOnAmbient G e C e = 0 := by
  rw [localMultiplicityOnAmbient_of_mem G e C e
    (separator_mem_pieceAmbientEdges G e C heG)]
  exact separatorEdgeInPiece_multiplicity_eq_zero G e C heG

open Classical in
/-- Therefore the full local split total is already carried by the
non-separator (exclusive) edges of the piece. -/
theorem pieceSplitTotal_eq_sum_exclusive
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (edgeGraph G e).ConnectedComponent)
    (heG : e ∈ G.edgeFinset) :
    ConcreteLedger.splitTotal (pieceGraph G e C) =
      ∑ f ∈ pieceExclusiveEdges G e C, localMultiplicityOnAmbient G e C f := by
  rw [pieceSplitTotal_eq_sum_localMultiplicity G e C]
  unfold pieceExclusiveEdges
  have hePiece := separator_mem_pieceAmbientEdges G e C heG
  have hsum := Finset.sum_erase_add (pieceAmbientEdges G e C)
    (localMultiplicityOnAmbient G e C) hePiece
  rw [localMultiplicityOnAmbient_separator_eq_zero G e C heG, add_zero] at hsum
  exact hsum.symm

open Classical in
/-- Pointwise comparison used in the recurrence: a non-separator edge has no
more split components in the ambient graph than inside its unique piece. -/
theorem edgeMultiplicity_le_localMultiplicityOnAmbient
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (hsplit : 2 ≤ edgeComponentCount G e)
    (C : (edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceExclusiveEdges G e C) :
    edgeMultiplicity G f ≤ localMultiplicityOnAmbient G e C f := by
  obtain ⟨hne, hfPiece⟩ := Finset.mem_erase.mp hf
  rw [localMultiplicityOnAmbient_of_mem G e C f hfPiece]
  exact KID981TopologicalBridge.AdjacentTwoCut.edgeMultiplicity_le_piece_edgeMultiplicity
    G hcard hG e heG hsplit C f hfPiece hne

open Classical in
/-- **Graph-valued split recurrence.**  Splitting a finite 2-connected graph
at an adjacent two-separator gives

`S(G) + 1 ≤ (∑ C, S(piece C)) + cc(G-{u,v})`.

Unlike the earlier numerical ledger, every term here is the actual component
count of an actual `SimpleGraph`. -/
theorem splitTotal_add_one_le_sum_pieceSplitTotal
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (hsplit : 2 ≤ edgeComponentCount G e) :
    ConcreteLedger.splitTotal G + 1 ≤
      (letI : Fintype (edgeGraph G e).ConnectedComponent := SetLike.instFintype
       ∑ C : (edgeGraph G e).ConnectedComponent,
         ConcreteLedger.splitTotal (pieceGraph G e C)) +
        edgeComponentCount G e := by
  let H := edgeGraph G e
  letI : Fintype H.ConnectedComponent := SetLike.instFintype
  let F : H.ConnectedComponent → Finset (Sym2 V) := pieceExclusiveEdges G e
  have hDisj :
      (↑(Finset.univ : Finset H.ConnectedComponent) : Set H.ConnectedComponent).PairwiseDisjoint F := by
    intro C _ D _ hCD
    exact pieceExclusiveEdges_disjoint G e heG hCD
  have hpartition :
      (∑ f ∈ G.edgeFinset.erase e, edgeMultiplicity G f) =
        ∑ C : H.ConnectedComponent, ∑ f ∈ F C, edgeMultiplicity G f := by
    rw [erase_separator_eq_pieceExclusiveUnion G e heG]
    unfold pieceExclusiveUnion
    rw [Finset.sum_biUnion hDisj]
  have hnonseparator :
      (∑ f ∈ G.edgeFinset.erase e, edgeMultiplicity G f) ≤
        ∑ C : H.ConnectedComponent,
          ConcreteLedger.splitTotal (pieceGraph G e C) := by
    rw [hpartition]
    apply Finset.sum_le_sum
    intro C _
    calc
      (∑ f ∈ F C, edgeMultiplicity G f) ≤
          ∑ f ∈ F C, localMultiplicityOnAmbient G e C f := by
        exact Finset.sum_le_sum fun f hf =>
          edgeMultiplicity_le_localMultiplicityOnAmbient
            G hcard hG e heG hsplit C f hf
      _ = ConcreteLedger.splitTotal (pieceGraph G e C) :=
        (pieceSplitTotal_eq_sum_exclusive G e C heG).symm
  have hdecompose := Finset.sum_erase_add G.edgeFinset
    (edgeMultiplicity G) heG
  have hseparator :=
    edgeMultiplicity_add_one_eq G hcard e heG
  have hdecompose' :
      (∑ f ∈ G.edgeFinset.erase e, edgeMultiplicity G f) +
          edgeMultiplicity G e = ConcreteLedger.splitTotal G := by
    simpa only [ConcreteLedger.splitTotal] using hdecompose
  have hresult :
      ConcreteLedger.splitTotal G + 1 ≤
        (∑ C : H.ConnectedComponent,
          ConcreteLedger.splitTotal (pieceGraph G e C)) +
          edgeComponentCount G e := by
    omega
  simpa only [H] using hresult

/-! ### Strong induction for SPLIT-DEFICIT -/

universe u

open Classical in
/-- Strong-induction form of SPLIT-DEFICIT.  The order `n` is explicit so the
induction hypothesis can be instantiated with the different vertex type of
each concrete piece. -/
theorem planar_twoConnected_splitDeficit_aux (n : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n →
      3 ≤ Fintype.card V →
      G.IsPlanar →
      G.IsKConnected 2 →
      ConcreteLedger.Assumptions.SplitDeficit G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V instFintype instDecidableEq G instDecidableAdj
        horder hcard hplanar htwo
      by_cases hzero : ConcreteLedger.splitTotal G = 0
      · exact PlanarAPI.splitDeficit_of_splitTotal_eq_zero G hplanar hcard hzero
      · have hpositive : 0 < ConcreteLedger.splitTotal G := Nat.pos_of_ne_zero hzero
        obtain ⟨e, heG, hsplit⟩ :=
          ConcreteLedger.exists_split_edge_of_splitTotal_pos G hcard hpositive
        have he : ¬e.IsDiag :=
          G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp heG)
        let H := edgeGraph G e
        letI : Fintype H.ConnectedComponent := SetLike.instFintype
        have hpieceCard : ∀ C : H.ConnectedComponent,
            3 ≤ Fintype.card {x : V // x ∈ pieceVertexSet G e C} := by
          intro C
          exact pieceVertex_card_ge_three G e C he
        have hpieceOrder : ∀ C : H.ConnectedComponent,
            Fintype.card {x : V // x ∈ pieceVertexSet G e C} < n := by
          intro C
          rw [← horder]
          exact pieceVertex_card_lt G e C he hsplit
        have hpieceBound : ∀ C : H.ConnectedComponent,
            ConcreteLedger.Assumptions.SplitDeficit (pieceGraph G e C) := by
          intro C
          exact ih
            (Fintype.card {x : V // x ∈ pieceVertexSet G e C})
            (hpieceOrder C) (pieceGraph G e C) rfl
            (hpieceCard C)
            (pieceGraph_isPlanar hplanar e C)
            (pieceGraph_isKConnected_two G hcard htwo e heG C)
        have hpieceIneq : ∀ C : H.ConnectedComponent,
            (pieceGraph G e C).edgeFinset.card +
                ConcreteLedger.splitTotal (pieceGraph G e C) + 6 ≤
              3 * Fintype.card {x : V // x ∈ pieceVertexSet G e C} := by
          intro C
          exact hpieceBound C
        have hvertices :
            (∑ C : H.ConnectedComponent,
                Fintype.card {x : V // x ∈ pieceVertexSet G e C}) + 2 =
              Fintype.card V + 2 * Fintype.card H.ConnectedComponent := by
          have hraw := sum_pieceVertexCount_add_two G e he
          have hsumVertices :
              (∑ C : H.ConnectedComponent,
                Fintype.card {x : V // x ∈ pieceVertexSet G e C}) =
                PairDeletion.pieceVertexTotal G e := by
            unfold PairDeletion.pieceVertexTotal
            apply Finset.sum_congr rfl
            intro C _
            unfold PairDeletion.pieceVertexCount
            rw [Fintype.card_eq_nat_card, natCard_pieceVertexSet G e C he]
          calc
            (∑ C : H.ConnectedComponent,
                Fintype.card {x : V // x ∈ pieceVertexSet G e C}) + 2 =
                PairDeletion.pieceVertexTotal G e + 2 := by rw [hsumVertices]
            _ = Nat.card V + 2 * edgeComponentCount G e := hraw
            _ = Fintype.card V + 2 * Fintype.card H.ConnectedComponent := by
              simp only [H, edgeComponentCount, ← Fintype.card_eq_nat_card]
        have hedges :
            (∑ C : H.ConnectedComponent,
                (pieceGraph G e C).edgeFinset.card) + 1 =
              G.edgeFinset.card + Fintype.card H.ConnectedComponent := by
          have hraw := pieceEdgeTotal_add_one_eq G e heG
          have hsumEdges :
              (∑ C : H.ConnectedComponent,
                (pieceGraph G e C).edgeFinset.card) = pieceEdgeTotal G e := by
            unfold pieceEdgeTotal
            apply Finset.sum_congr rfl
            intro C _
            exact (pieceEdgeCount_eq_card_edgeFinset G e C).symm
          calc
            (∑ C : H.ConnectedComponent,
                (pieceGraph G e C).edgeFinset.card) + 1 =
                pieceEdgeTotal G e + 1 := by rw [hsumEdges]
            _ = G.edgeFinset.card + edgeComponentCount G e := hraw
            _ = G.edgeFinset.card + Fintype.card H.ConnectedComponent := by
              unfold edgeComponentCount
              rw [Fintype.card_eq_nat_card]
        have hsplits :
            ConcreteLedger.splitTotal G + 1 ≤
              (∑ C : H.ConnectedComponent,
                ConcreteLedger.splitTotal (pieceGraph G e C)) +
                Fintype.card H.ConnectedComponent := by
          have hraw := splitTotal_add_one_le_sum_pieceSplitTotal
            G hcard htwo e heG hsplit
          have hcount : edgeComponentCount G e = Fintype.card H.ConnectedComponent := by
            unfold edgeComponentCount
            exact Fintype.card_eq_nat_card.symm
          simpa only [H, hcount] using hraw
        exact FiniteLedger.split_recursion_aggregation_le
          (fun C : H.ConnectedComponent =>
            Fintype.card {x : V // x ∈ pieceVertexSet G e C})
          (fun C : H.ConnectedComponent => (pieceGraph G e C).edgeFinset.card)
          (fun C : H.ConnectedComponent => ConcreteLedger.splitTotal (pieceGraph G e C))
          (Fintype.card V) G.edgeFinset.card (ConcreteLedger.splitTotal G)
          hpieceIneq hvertices hedges hsplits

open Classical in
/-- **SPLIT-DEFICIT for actual finite simple graphs.**  Every finite planar
2-connected graph on at least three vertices satisfies

`|E(G)| + ∑_{uv∈E(G)} (cc(G-{u,v})-1) + 6 ≤ 3|V(G)|`.

The proof is a genuine strong induction over concrete graph pieces; it does
not enumerate graphs and does not appeal to random testing. -/
theorem planar_twoConnected_splitDeficit
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hplanar : G.IsPlanar) (htwo : G.IsKConnected 2) :
    ConcreteLedger.Assumptions.SplitDeficit G :=
  planar_twoConnected_splitDeficit_aux (Fintype.card V)
    G rfl hcard hplanar htwo

#print axioms pieceGraph_isKConnected_two
#print axioms splitTotal_add_one_le_sum_pieceSplitTotal
#print axioms planar_twoConnected_splitDeficit

end PieceFacts

end PlaneTopology.Faces.SplitDeficit
