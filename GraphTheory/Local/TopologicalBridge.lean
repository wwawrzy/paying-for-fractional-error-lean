import GraphTheory.PlanarGirth
import GraphTheory.SimpleGraph.Minor.Closed
import GraphTheory.KLinked

/-!
# A concrete bridge for the topological core of FULL-STAR-CONTACT

This scratch file deliberately separates three layers.

* **Layer A** is finite-sum and articulation algebra.  It knows no planarity.
* **Layer B** defines deletion of a pair of vertices, the actual number of
  connected components after deletion, and the split multiplicity carried by
  an edge.
* **Layer C** records exactly what follows from the repository's planar API.
  Minor/induced-subgraph closure is axiom-free relative to the definition of
  `SimpleGraph.IsPlanar`; the density theorem inherits the already existing
  custom axiom `SimpleGraph.IsPlanar.hasPlanarRotationSystem`.

The missing geometric inputs `LOCAL-OCC` and `SPLIT-DEFICIT` are *not*
declared as axioms or theorems.  They are definitions in the explicit
`Assumptions` namespace.  The final aggregation theorem accepts those
assumptions for the concrete split multiplicities defined from pair deletion.
-/

namespace KID981TopologicalBridge

open scoped BigOperators

/-! ## Layer A: finite-sum and articulation algebra -/

namespace FiniteLedger

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sum the weight of all unordered pairs in `edges` incident with `v`. -/
def incidentWeight (edges : Finset (Sym2 V)) (weight : Sym2 V → ℕ) (v : V) : ℕ :=
  ∑ e ∈ edges, if v ∈ e then weight e else 0

/-- A weighted handshaking identity for an arbitrary finite collection of
non-diagonal unordered pairs.  Each pair contributes its weight at each of its
two distinct endpoints. -/
theorem sum_incidentWeight_eq_two_mul
    (edges : Finset (Sym2 V)) (weight : Sym2 V → ℕ)
    (hnondiag : ∀ e ∈ edges, ¬e.IsDiag) :
    (∑ v : V, incidentWeight edges weight v) =
      2 * ∑ e ∈ edges, weight e := by
  classical
  unfold incidentWeight
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ edges, ∑ v : V, if v ∈ e then weight e else 0)
        = ∑ e ∈ edges, e.toFinset.card * weight e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [← Finset.sum_filter]
          have hfilter : Finset.univ.filter (fun v : V => v ∈ e) = e.toFinset := by
            ext v
            simp [Sym2.mem_toFinset]
          rw [hfilter]
          simp
    _ = ∑ e ∈ edges, 2 * weight e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Sym2.card_toFinset_of_not_isDiag e (hnondiag e he)]
    _ = 2 * ∑ e ∈ edges, weight e := by
          rw [Finset.mul_sum]

/-- Summing local inequalities after both handshake identities have been made
explicit.  This is the exact cancellation step `2|A| ≤ 2m + 2S`. -/
theorem aggregate_local_bounds
    {ι : Type*} [Fintype ι]
    (marked degree incident : ι → ℕ) (edges splitTotal : ℕ)
    (hlocal : ∀ v, 2 * marked v ≤ degree v + incident v)
    (hdegree : (∑ v, degree v) = 2 * edges)
    (hincident : (∑ v, incident v) = 2 * splitTotal) :
    (∑ v, marked v) ≤ edges + splitTotal := by
  have hsum : (∑ v, 2 * marked v) ≤ ∑ v, (degree v + incident v) :=
    Finset.sum_le_sum fun v _ => hlocal v
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hdegree, hincident] at hsum
  omega

/-- Arithmetic core of one adjacent-two-cut induction step for
`SPLIT-DEFICIT`.

For `k` pieces that all contain the two separator vertices and the separator
edge, the exact graph identities are

* `sum n_i + 2 = n + 2k`,
* `sum m_i + 1 = m + k`,
* `S + 1 = sum S_i + k`.

These additive forms avoid truncated subtraction and are equivalent to the
usual `(k-1)` formulas when `k ≥ 1`.

If every piece satisfies `m_i + S_i + 6 ≤ 3n_i`, then the parent satisfies
`m + S + 6 ≤ 3n`.  This theorem proves only that deterministic arithmetic;
constructing the pieces and proving the three identities remains graph work. -/
theorem split_recursion_aggregation
    {ι : Type*} [Fintype ι]
    (pieceVertices pieceEdges pieceSplit : ι → ℕ)
    (vertices edges splitTotal : ℕ)
    (hpiece : ∀ i,
      pieceEdges i + pieceSplit i + 6 ≤ 3 * pieceVertices i)
    (hvertices : (∑ i, pieceVertices i) + 2 =
      vertices + 2 * Fintype.card ι)
    (hedges : (∑ i, pieceEdges i) + 1 =
      edges + Fintype.card ι)
    (hsplit : splitTotal + 1 =
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

/-- Exact articulation ledger over `Int`: local piece gaps of six leave
`3(k-1)` units, while cross marks consume at most `2(k-1)`. -/
theorem articulation_with_slack
    {ι : Type*} [Fintype ι]
    (pieceVertices pieceMarked : ι → ℤ)
    (vertices cross total : ℤ)
    (hpiece : ∀ i, pieceMarked i ≤ 3 * pieceVertices i - 6)
    (hsizes : (∑ i, pieceVertices i) =
      vertices + (Fintype.card ι : ℤ) - 1)
    (hcross : cross ≤ 2 * ((Fintype.card ι : ℤ) - 1))
    (htotal : total = (∑ i, pieceMarked i) + cross) :
    total ≤ 3 * vertices - 6 - ((Fintype.card ι : ℤ) - 1) := by
  have hsum : (∑ i, pieceMarked i) ≤ ∑ i, (3 * pieceVertices i - 6) :=
    Finset.sum_le_sum fun i _ => hpiece i
  have hformula :
      (∑ i, (3 * pieceVertices i - 6)) =
        3 * (∑ i, pieceVertices i) - 6 * (Fintype.card ι : ℤ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
    ring
  rw [hformula, hsizes] at hsum
  omega

end FiniteLedger

/-! ## Layer B: concrete pair deletion and split multiplicity -/

namespace PairDeletion

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Vertex set carried by an unordered pair. -/
def deletedSet (e : Sym2 V) : Set V := e.toFinset

/-- The graph left after deleting the vertices carried by `e`.  Taking the
unordered pair as the primitive input makes endpoint symmetry definitional at
the interface where edge sums use it. -/
def edgeGraph (G : SimpleGraph V) (e : Sym2 V) :
    SimpleGraph {x : V // x ∈ (deletedSet e)ᶜ} :=
  G.induce (deletedSet e)ᶜ

/-- The graph left after deleting the unordered pair `{u,v}`. -/
def graph (G : SimpleGraph V) (u v : V) :=
  edgeGraph G s(u, v)

/-- Number of connected components after deleting the unordered pair `e`. -/
noncomputable def edgeComponentCount (G : SimpleGraph V) (e : Sym2 V) : ℕ :=
  Nat.card (edgeGraph G e).ConnectedComponent

/-- Number of connected components after deleting `{u,v}`.  `Nat.card` avoids
committing the interface to a particular synthesized `Fintype` instance. -/
noncomputable def componentCount (G : SimpleGraph V) (u v : V) : ℕ :=
  edgeComponentCount G s(u, v)

/-- The component count is symmetric in the deleted endpoints. -/
theorem componentCount_comm (G : SimpleGraph V) (u v : V) :
    componentCount G u v = componentCount G v u := by
  unfold componentCount
  rw [Sym2.eq_swap]

/-- Paper multiplicity `s_uv = cc(G-{u,v})-1`, represented in `Nat`. -/
noncomputable def multiplicity (G : SimpleGraph V) (u v : V) : ℕ :=
  componentCount G u v - 1

theorem multiplicity_comm (G : SimpleGraph V) (u v : V) :
    multiplicity G u v = multiplicity G v u := by
  simp only [multiplicity, componentCount_comm G u v]

/-- The split multiplicity attached to an unordered pair. -/
noncomputable def edgeMultiplicity (G : SimpleGraph V) : Sym2 V → ℕ :=
  fun e => edgeComponentCount G e - 1

@[simp]
theorem edgeMultiplicity_mk (G : SimpleGraph V) (u v : V) :
    edgeMultiplicity G s(u, v) = multiplicity G u v :=
  rfl

/-- A non-diagonal unordered pair contains exactly two vertices.  `Nat.card`
keeps this fact independent of a synthesized subtype `Fintype` instance. -/
theorem natCard_deletedSet_of_not_isDiag
    [Fintype V] (e : Sym2 V) (he : ¬e.IsDiag) :
    Nat.card {x : V // x ∈ deletedSet e} = 2 := by
  classical
  change Nat.card {x : V // x ∈ e.toFinset} = 2
  rw [← Fintype.card_eq_nat_card, Fintype.card_coe]
  exact Sym2.card_toFinset_of_not_isDiag e he

/-- Deleting a non-diagonal pair removes exactly two vertices.  The additive
form avoids `Nat` truncation. -/
theorem natCard_edgeGraph_vertices_add_two
    [Fintype V] (e : Sym2 V) (he : ¬e.IsDiag) :
    Nat.card {x : V // x ∈ (deletedSet e)ᶜ} + 2 = Nat.card V := by
  classical
  have hdeletedNat := natCard_deletedSet_of_not_isDiag e he
  have hdeleted : Fintype.card {x : V // x ∈ deletedSet e} = 2 := by
    simpa only [Fintype.card_eq_nat_card] using hdeletedNat
  have hcompl := Fintype.card_subtype_compl (fun x : V => x ∈ deletedSet e)
  rw [hdeleted] at hcompl
  have hcompl' :
      Fintype.card {x : V // x ∈ (deletedSet e)ᶜ} = Fintype.card V - 2 := by
    simpa only [Set.mem_compl_iff] using hcompl
  have hresult :
      Fintype.card {x : V // x ∈ (deletedSet e)ᶜ} + 2 = Fintype.card V := by
    rw [hcompl']
    exact Nat.sub_add_cancel (by
      rw [← hdeleted]
      exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  simpa only [Fintype.card_eq_nat_card] using hresult

/-- After deleting the endpoints of an edge from a graph with at least three
vertices, at least one vertex, and hence at least one connected component,
remains. -/
theorem edgeComponentCount_pos_of_edge
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (e : Sym2 V)
    (heG : e ∈ G.edgeFinset) :
    0 < edgeComponentCount G e := by
  classical
  have he : ¬e.IsDiag :=
    G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp heG)
  have hvertices := natCard_edgeGraph_vertices_add_two (V := V) e he
  have hcardNat : 3 ≤ Nat.card V := by
    simpa only [Fintype.card_eq_nat_card] using hcard
  have hnonemptyCard :
      0 < Nat.card {x : V // x ∈ (deletedSet e)ᶜ} := by
    omega
  haveI : Nonempty {x : V // x ∈ (deletedSet e)ᶜ} :=
    (Nat.card_pos_iff.mp hnonemptyCard).1
  unfold edgeComponentCount
  exact Nat.card_pos

/-- On an actual edge, the truncated definition
`s_e = cc(G-e) - 1` can be used without loss: `s_e + 1 = cc(G-e)`. -/
theorem edgeMultiplicity_add_one_eq
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (e : Sym2 V)
    (heG : e ∈ G.edgeFinset) :
    edgeMultiplicity G e + 1 = edgeComponentCount G e := by
  have hpos := edgeComponentCount_pos_of_edge G hcard e heG
  unfold edgeMultiplicity
  omega

/-- Positive split multiplicity is equivalent to deletion leaving at least
two components. -/
theorem edgeMultiplicity_pos_iff_two_le
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (e : Sym2 V)
    (heG : e ∈ G.edgeFinset) :
    0 < edgeMultiplicity G e ↔ 2 ≤ edgeComponentCount G e := by
  have hpos := edgeComponentCount_pos_of_edge G hcard e heG
  unfold edgeMultiplicity
  omega

open Classical in
/-- In a 2-connected graph, the endpoints of an edge whose deletion leaves
at least two components form a minimal vertex separator.  This is the exact
interface needed to attach every deleted-pair component to both endpoints. -/
theorem deletedSet_isMinSeparator_of_isKConnected_two
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (hsplit : 2 ≤ edgeComponentCount G e) :
    G.IsMinSeparator e.toFinset := by
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have he : ¬e.IsDiag :=
    G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp heG)
  constructor
  · unfold SimpleGraph.IsSeparator
    intro hconnected
    haveI : Subsingleton (edgeGraph G e).ConnectedComponent :=
      hconnected.preconnected.subsingleton_connectedComponent
    have hle : edgeComponentCount G e ≤ 1 := by
      unfold edgeComponentCount
      exact Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  · intro T hT hseparator
    apply hseparator
    have hTcard : T.card < 2 := by
      have hlt := Finset.card_lt_card hT
      rw [Sym2.card_toFinset_of_not_isDiag e he] at hlt
      exact hlt
    have hconnected := hG.isVertexConnected.2 T hTcard
    have hsets :
        ((Finset.univ \ T : Finset V) : Set V) = ((T : Set V)ᶜ) := by
      ext x
      simp
    rw [hsets] at hconnected
    exact hconnected

/-- Number of vertices in the split piece indexed by component `C`: all
vertices of `C` plus the two deleted endpoints. -/
noncomputable def pieceVertexCount
    (G : SimpleGraph V) (e : Sym2 V)
    (C : (edgeGraph G e).ConnectedComponent) : ℕ :=
  Nat.card ↥C + 2

open Classical in
/-- Sum of the concrete piece sizes, using the `SetLike` enumeration of
components also used by `SimpleGraph.sum_card_components_eq`.  Hiding that
enumeration here prevents downstream theorems from depending on a particular
`Fintype` instance for connected components. -/
noncomputable def pieceVertexTotal
    [Fintype V] (G : SimpleGraph V) (e : Sym2 V) : ℕ :=
  letI : Fintype (edgeGraph G e).ConnectedComponent := SetLike.instFintype
  ∑ C : (edgeGraph G e).ConnectedComponent, pieceVertexCount G e C

/-- The exact vertex-cardinality recurrence for the concrete components of
`G-e`: `sum n_i + 2 = n + 2k`. -/
theorem sum_pieceVertexCount_add_two
    [Fintype V] (G : SimpleGraph V) (e : Sym2 V) (he : ¬e.IsDiag) :
    pieceVertexTotal G e + 2 =
      Nat.card V + 2 * edgeComponentCount G e := by
  classical
  letI : Fintype (edgeGraph G e).ConnectedComponent := SetLike.instFintype
  have hpartsF := SimpleGraph.sum_card_components_eq (G := edgeGraph G e)
  have hparts :
      (∑ C : (edgeGraph G e).ConnectedComponent, Nat.card ↥C) =
        Nat.card {x : V // x ∈ (deletedSet e)ᶜ} := by
    simpa only [Fintype.card_eq_nat_card] using hpartsF
  have hvertices := natCard_edgeGraph_vertices_add_two e he
  unfold pieceVertexTotal pieceVertexCount
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    Fintype.card_eq_nat_card]
  rw [hparts]
  unfold edgeComponentCount
  omega

end PairDeletion

/-! ## Concrete pieces at an adjacent two-separator -/

namespace AdjacentTwoCut

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Lift one component of `G-e` back to a set of ambient vertices. -/
def liftedComponentSet (G : SimpleGraph V) (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) : Set V :=
  {x | ∃ hx : x ∈ (PairDeletion.deletedSet e)ᶜ,
    (⟨x, hx⟩ : {x : V // x ∈ (PairDeletion.deletedSet e)ᶜ}) ∈ C.supp}

@[simp]
theorem mem_liftedComponentSet_iff (G : SimpleGraph V) (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (x : V) :
    x ∈ liftedComponentSet G e C ↔
      ∃ hx : x ∈ (PairDeletion.deletedSet e)ᶜ,
        (⟨x, hx⟩ : {x : V // x ∈ (PairDeletion.deletedSet e)ᶜ}) ∈ C.supp :=
  Iff.rfl

/-- Vertex set of the concrete `{u,v}`-piece indexed by `C`: the vertices of
`C` together with both separator endpoints. -/
def pieceVertexSet (G : SimpleGraph V) (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) : Set V :=
  PairDeletion.deletedSet e ∪ liftedComponentSet G e C

@[simp]
theorem mem_pieceVertexSet_iff (G : SimpleGraph V) (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (x : V) :
    x ∈ pieceVertexSet G e C ↔
      x ∈ PairDeletion.deletedSet e ∨ x ∈ liftedComponentSet G e C :=
  Iff.rfl

/-- The concrete piece graph.  When `e ∈ G.edgeFinset`, the separator edge is
already present in this induced graph; no synthetic parallel edge is added. -/
def pieceGraph (G : SimpleGraph V) (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) :
    SimpleGraph {x : V // x ∈ pieceVertexSet G e C} :=
  G.induce (pieceVertexSet G e C)

/-- Every concrete piece inherits minor-defined planarity from the ambient
graph, independently of the rotation-system axiom. -/
theorem pieceGraph_isPlanar {G : SimpleGraph V} (hG : G.IsPlanar) (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) :
    (pieceGraph G e C).IsPlanar :=
  hG.induce _

/-- Use the ambient adjacency decision on a piece.  Keeping this instance
explicit avoids a diamond between induced adjacency and
`Classical.propDecidable` when an `edgeFinset` is formed. -/
instance instDecidableRelPieceGraphAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (C : (PairDeletion.edgeGraph G e).ConnectedComponent) :
    DecidableRel (pieceGraph G e C).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x.val y.val))

open Classical in
/-- Ambient representation of the edges of `pieceGraph`. -/
noncomputable def pieceAmbientEdges [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) : Finset (Sym2 V) :=
  G.edgeFinset ∩ (pieceVertexSet G e C).toFinset.sym2

/-- Concrete edge count of one piece.  The next theorem identifies it with the
actual `edgeFinset.card` of `pieceGraph`. -/
noncomputable def pieceEdgeCount [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) : ℕ :=
  (pieceAmbientEdges G e C).card

open Classical in
/-- Stable sum of concrete piece edge counts. -/
noncomputable def pieceEdgeTotal [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  letI : Fintype (PairDeletion.edgeGraph G e).ConnectedComponent :=
    SetLike.instFintype
  ∑ C : (PairDeletion.edgeGraph G e).ConnectedComponent, pieceEdgeCount G e C

open Classical in
theorem map_pieceGraph_edgeFinset
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) :
    (pieceGraph G e C).edgeFinset.map
        (Function.Embedding.subtype (· ∈ pieceVertexSet G e C)).sym2Map =
      pieceAmbientEdges G e C := by
  have h := SimpleGraph.map_edgeFinset_induce
    (G := G) (s := pieceVertexSet G e C)
  simpa only [pieceGraph, pieceAmbientEdges] using h

open Classical in
theorem pieceEdgeCount_eq_card_edgeFinset
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) :
    pieceEdgeCount G e C = (pieceGraph G e C).edgeFinset.card := by
  unfold pieceEdgeCount
  rw [← map_pieceGraph_edgeFinset G e C, Finset.card_map]

open Classical in
@[simp]
theorem mk_mem_pieceAmbientEdges_iff
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (x y : V) :
    s(x, y) ∈ pieceAmbientEdges G e C ↔
      G.Adj x y ∧ x ∈ pieceVertexSet G e C ∧ y ∈ pieceVertexSet G e C := by
  simp [pieceAmbientEdges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

open Classical in
theorem separator_mem_pieceAmbientEdges
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent)
    (heG : e ∈ G.edgeFinset) :
    e ∈ pieceAmbientEdges G e C := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := G.mem_edgeFinset.mp heG
      simpa [pieceVertexSet, PairDeletion.deletedSet] using
        (show G.Adj u v ∧
            u ∈ pieceVertexSet G s(u, v) C ∧ v ∈ pieceVertexSet G s(u, v) C by
          exact ⟨huv, Or.inl (by simp [PairDeletion.deletedSet]),
            Or.inl (by simp [PairDeletion.deletedSet])⟩)

/-- Two non-diagonal unordered pairs with one contained in the vertex set of
the other are equal. -/
theorem eq_of_subset_deletedSet (f e : Sym2 V)
    (hf : ¬f.IsDiag) (he : ¬e.IsDiag)
    (hsub : (f : Set V) ⊆ PairDeletion.deletedSet e) :
    f = e := by
  classical
  have hfinSub : f.toFinset ⊆ e.toFinset := by
    intro x hx
    have hxf : x ∈ f := Sym2.mem_toFinset.mp hx
    simpa only [PairDeletion.deletedSet, Set.mem_setOf_eq] using hsub hxf
  have hcardLe : e.toFinset.card ≤ f.toFinset.card := by
    rw [Sym2.card_toFinset_of_not_isDiag e he,
      Sym2.card_toFinset_of_not_isDiag f hf]
  have hfin : f.toFinset = e.toFinset :=
    Finset.eq_of_subset_of_card_le hfinSub hcardLe
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hfin]

/-- If two non-diagonal pairs are different, one endpoint of the first lies
outside the second. -/
theorem exists_mem_not_mem_deletedSet_of_ne (f e : Sym2 V)
    (hf : ¬f.IsDiag) (he : ¬e.IsDiag) (hne : f ≠ e) :
    ∃ x, x ∈ f ∧ x ∉ PairDeletion.deletedSet e := by
  classical
  by_contra h
  apply hne
  apply eq_of_subset_deletedSet f e hf he
  intro x hxf
  by_contra hx
  exact h ⟨x, hxf, hx⟩

/-- Edges of one piece other than the duplicated separator edge. -/
noncomputable def pieceExclusiveEdges [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) : Finset (Sym2 V) :=
  (pieceAmbientEdges G e C).erase e

open Classical in
/-- Union of all non-separator piece edges, with the same stable component
enumeration used by the earlier component-cardinality theorem. -/
noncomputable def pieceExclusiveUnion [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : Finset (Sym2 V) :=
  letI : Fintype (PairDeletion.edgeGraph G e).ConnectedComponent :=
    SetLike.instFintype
  Finset.univ.biUnion (pieceExclusiveEdges G e)

open Classical in
theorem erase_separator_eq_pieceExclusiveUnion
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (heG : e ∈ G.edgeFinset) :
    G.edgeFinset.erase e = pieceExclusiveUnion G e := by
  let H := PairDeletion.edgeGraph G e
  letI : Fintype H.ConnectedComponent := SetLike.instFintype
  unfold pieceExclusiveUnion
  ext f
  rw [Finset.mem_erase, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hfG⟩
    have hf : ¬f.IsDiag :=
      G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp hfG)
    have he : ¬e.IsDiag :=
      G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp heG)
    obtain ⟨x, hxf, hxout⟩ :=
      exists_mem_not_mem_deletedSet_of_ne f e hf he hne
    obtain ⟨z, hfEq⟩ := Sym2.mem_iff_exists.mp hxf
    subst f
    let xv : {x : V // x ∈ (PairDeletion.deletedSet e)ᶜ} := ⟨x, hxout⟩
    let C : H.ConnectedComponent := H.connectedComponentMk xv
    refine ⟨C, Finset.mem_erase.mpr ⟨hne, ?_⟩⟩
    apply (mk_mem_pieceAmbientEdges_iff G e C x z).mpr
    have hxPiece : x ∈ pieceVertexSet G e C := by
      apply Or.inr
      exact ⟨hxout, ConnectedComponent.connectedComponentMk_mem⟩
    have hzPiece : z ∈ pieceVertexSet G e C := by
      by_cases hz : z ∈ PairDeletion.deletedSet e
      · exact Or.inl hz
      · apply Or.inr
        refine ⟨hz, ?_⟩
        rw [ConnectedComponent.mem_supp_iff]
        apply (ConnectedComponent.connectedComponentMk_eq_of_adj ?_).symm
        exact G.mem_edgeFinset.mp hfG
    exact ⟨G.mem_edgeFinset.mp hfG, hxPiece, hzPiece⟩
  · rintro ⟨C, hfC⟩
    obtain ⟨hne, hfPiece⟩ := Finset.mem_erase.mp hfC
    refine ⟨hne, ?_⟩
    exact (Finset.mem_inter.mp hfPiece).1

open Classical in
theorem pieceExclusiveEdges_disjoint
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (heG : e ∈ G.edgeFinset)
    {C D : (PairDeletion.edgeGraph G e).ConnectedComponent} (hCD : C ≠ D) :
    Disjoint (pieceExclusiveEdges G e C) (pieceExclusiveEdges G e D) := by
  rw [Finset.disjoint_left]
  intro f hfC hfD
  obtain ⟨hne, hfPieceC⟩ := Finset.mem_erase.mp hfC
  obtain ⟨_, hfPieceD⟩ := Finset.mem_erase.mp hfD
  have hfG : f ∈ G.edgeFinset := (Finset.mem_inter.mp hfPieceC).1
  have hf : ¬f.IsDiag :=
    G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp hfG)
  have he : ¬e.IsDiag :=
    G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp heG)
  obtain ⟨x, hxf, hxout⟩ :=
    exists_mem_not_mem_deletedSet_of_ne f e hf he hne
  obtain ⟨z, hfEq⟩ := Sym2.mem_iff_exists.mp hxf
  subst f
  have hxPieceC : x ∈ pieceVertexSet G e C :=
    ((mk_mem_pieceAmbientEdges_iff G e C x z).mp hfPieceC).2.1
  have hxPieceD : x ∈ pieceVertexSet G e D :=
    ((mk_mem_pieceAmbientEdges_iff G e D x z).mp hfPieceD).2.1
  have hxLiftC : x ∈ liftedComponentSet G e C :=
    (mem_pieceVertexSet_iff G e C x).mp hxPieceC |>.resolve_left hxout
  have hxLiftD : x ∈ liftedComponentSet G e D :=
    (mem_pieceVertexSet_iff G e D x).mp hxPieceD |>.resolve_left hxout
  obtain ⟨hxC, hxSuppC⟩ := (mem_liftedComponentSet_iff G e C x).mp hxLiftC
  obtain ⟨hxD, hxSuppD⟩ := (mem_liftedComponentSet_iff G e D x).mp hxLiftD
  have hmkC :
      (PairDeletion.edgeGraph G e).connectedComponentMk ⟨x, hxC⟩ = C :=
    (ConnectedComponent.mem_supp_iff C _).mp hxSuppC
  have hmkD :
      (PairDeletion.edgeGraph G e).connectedComponentMk ⟨x, hxD⟩ = D :=
    (ConnectedComponent.mem_supp_iff D _).mp hxSuppD
  apply hCD
  calc
    C = (PairDeletion.edgeGraph G e).connectedComponentMk ⟨x, hxC⟩ := hmkC.symm
    _ = (PairDeletion.edgeGraph G e).connectedComponentMk ⟨x, hxD⟩ := by
      congr 1
    _ = D := hmkD

open Classical in
/-- Exact edge recurrence for the concrete pieces:
`sum m_i + 1 = m + k`. -/
theorem pieceEdgeTotal_add_one_eq
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (heG : e ∈ G.edgeFinset) :
    pieceEdgeTotal G e + 1 =
      G.edgeFinset.card + PairDeletion.edgeComponentCount G e := by
  let H := PairDeletion.edgeGraph G e
  letI : Fintype H.ConnectedComponent := SetLike.instFintype
  let F : H.ConnectedComponent → Finset (Sym2 V) := pieceExclusiveEdges G e
  have hDisj :
      (↑(Finset.univ : Finset H.ConnectedComponent) : Set H.ConnectedComponent).PairwiseDisjoint F := by
    intro C _ D _ hCD
    exact pieceExclusiveEdges_disjoint G e heG hCD
  have hsumExclusive :
      (∑ C : H.ConnectedComponent, (F C).card) =
        (G.edgeFinset.erase e).card := by
    calc
      (∑ C : H.ConnectedComponent, (F C).card) =
          (Finset.univ.biUnion F).card := (Finset.card_biUnion hDisj).symm
      _ = (pieceExclusiveUnion G e).card := rfl
      _ = (G.edgeFinset.erase e).card := by
        rw [← erase_separator_eq_pieceExclusiveUnion G e heG]
  have hsumPieces :
      pieceEdgeTotal G e =
        (∑ C : H.ConnectedComponent, (F C).card) + Fintype.card H.ConnectedComponent := by
    unfold pieceEdgeTotal pieceEdgeCount
    calc
      (∑ C : H.ConnectedComponent, (pieceAmbientEdges G e C).card) =
          ∑ C : H.ConnectedComponent, ((F C).card + 1) := by
        apply Finset.sum_congr rfl
        intro C _
        exact (Finset.card_erase_add_one (separator_mem_pieceAmbientEdges G e C heG)).symm
      _ = (∑ C : H.ConnectedComponent, (F C).card) +
          Fintype.card H.ConnectedComponent := by
        rw [Finset.sum_add_distrib]
        simp
  have hcount :
      Fintype.card H.ConnectedComponent = PairDeletion.edgeComponentCount G e := by
    unfold PairDeletion.edgeComponentCount
    exact Fintype.card_eq_nat_card
  have herase := Finset.card_erase_add_one heG
  rw [hsumPieces, hsumExclusive, hcount]
  omega

/-! ### Comparing pair deletion inside one piece with ambient pair deletion -/

open Classical in
/-- Every endpoint of an ambient edge assigned to a piece is a vertex of that
piece.  This is the endpoint-level bridge needed to regard the same unordered
pair as an edge of `pieceGraph`. -/
theorem forall_mem_pieceVertexSet_of_mem_pieceAmbientEdges
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) {f : Sym2 V}
    (hf : f ∈ pieceAmbientEdges G e C) :
    ∀ x ∈ f, x ∈ pieceVertexSet G e C := by
  induction f using Sym2.inductionOn with
  | _ x y =>
      have hxy := (mk_mem_pieceAmbientEdges_iff G e C x y).mp hf
      intro z hz
      simp only [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact hxy.2.1
      · exact hxy.2.2

open Classical in
/-- The copy of an ambient piece edge on the subtype of piece vertices. -/
noncomputable def liftEdgeToPiece
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) :
    Sym2 {x : V // x ∈ pieceVertexSet G e C} :=
  f.pmap Subtype.mk
    (forall_mem_pieceVertexSet_of_mem_pieceAmbientEdges G e C hf)

open Classical in
@[simp]
theorem map_liftEdgeToPiece
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) :
    (liftEdgeToPiece G e C f hf).map Subtype.val = f := by
  exact Sym2.pmap_subtype_map_subtypeVal f
    (forall_mem_pieceVertexSet_of_mem_pieceAmbientEdges G e C hf)

open Classical in
@[simp]
theorem mem_liftEdgeToPiece_iff
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C)
    (x : {x : V // x ∈ pieceVertexSet G e C}) :
    x ∈ liftEdgeToPiece G e C f hf ↔ x.val ∈ f := by
  unfold liftEdgeToPiece
  rw [Sym2.mem_pmap_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hval : x.val = y := congr_arg Subtype.val hxy
    simpa only [hval] using hy
  · intro hx
    exact ⟨x.val, hx, Subtype.ext rfl⟩

open Classical in
/-- Inclusion of the vertices surviving local deletion in a piece into the
vertices surviving the same ambient pair deletion. -/
noncomputable def localDeleteVertexEmbedding
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) :
    {x : {x : V // x ∈ pieceVertexSet G e C} //
        x ∈ (PairDeletion.deletedSet (liftEdgeToPiece G e C f hf))ᶜ} ↪
      {x : V // x ∈ (PairDeletion.deletedSet f)ᶜ} where
  toFun x := ⟨x.val.val, by
    have hxLocalFinset :
        x.val ∉ (liftEdgeToPiece G e C f hf).toFinset := by
      simpa only [PairDeletion.deletedSet, Set.mem_compl_iff,
        Set.mem_setOf_eq] using x.property
    have hxLocal : x.val ∉ liftEdgeToPiece G e C f hf := by
      intro hx
      exact hxLocalFinset (Sym2.mem_toFinset.mpr hx)
    have hxAmbient : x.val.val ∉ f := by
      intro hxf
      exact hxLocal ((mem_liftEdgeToPiece_iff G e C f hf x.val).mpr hxf)
    show x.val.val ∉ f.toFinset
    intro hx
    exact hxAmbient (Sym2.mem_toFinset.mp hx)⟩
  inj' := by
    intro x y hxy
    have hAmbient : x.val.val = y.val.val :=
      congr_arg
        (fun z : {z : V // z ∈ (PairDeletion.deletedSet f)ᶜ} => z.val) hxy
    exact Subtype.ext (Subtype.ext hAmbient)

open Classical in
/-- The local pair-deletion graph is an induced subgraph of the ambient
pair-deletion graph.  The embedding remembers both nested subtype layers. -/
noncomputable def localDeleteGraphEmbedding
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) :
    PairDeletion.edgeGraph (pieceGraph G e C) (liftEdgeToPiece G e C f hf) ↪g
      PairDeletion.edgeGraph G f where
  toEmbedding := localDeleteVertexEmbedding G e C f hf
  map_rel_iff' := Iff.rfl

open Classical in
/-- Any path surviving deletion inside a piece remains a path after the same
pair is deleted from the ambient graph. -/
theorem localDelete_reachable_globalDelete
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C)
    {x y : {z : {z : V // z ∈ pieceVertexSet G e C} //
      z ∈ (PairDeletion.deletedSet (liftEdgeToPiece G e C f hf))ᶜ}}
    (hxy : (PairDeletion.edgeGraph (pieceGraph G e C)
      (liftEdgeToPiece G e C f hf)).Reachable x y) :
    (PairDeletion.edgeGraph G f).Reachable
      (localDeleteGraphEmbedding G e C f hf x)
      (localDeleteGraphEmbedding G e C f hf y) :=
  hxy.map (localDeleteGraphEmbedding G e C f hf).toHom

open Classical in
/-- The canonical map from components of local pair deletion to components of
ambient pair deletion.  Injectivity and surjectivity are the two remaining
topological obligations for transporting `s_f`. -/
noncomputable def localDeleteComponentMap
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) :
    (PairDeletion.edgeGraph (pieceGraph G e C)
      (liftEdgeToPiece G e C f hf)).ConnectedComponent →
      (PairDeletion.edgeGraph G f).ConnectedComponent :=
  ConnectedComponent.map (localDeleteGraphEmbedding G e C f hf).toHom

open Classical in
@[simp]
theorem localDeleteComponentMap_mk
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C)
    (x : {z : {z : V // z ∈ pieceVertexSet G e C} //
      z ∈ (PairDeletion.deletedSet (liftEdgeToPiece G e C f hf))ᶜ}) :
    localDeleteComponentMap G e C f hf
        ((PairDeletion.edgeGraph (pieceGraph G e C)
          (liftEdgeToPiece G e C f hf)).connectedComponentMk x) =
      (PairDeletion.edgeGraph G f).connectedComponentMk
        (localDeleteGraphEmbedding G e C f hf x) :=
  rfl

open Classical in
/-- A vertex in a component of `G-e` different from the selected piece
component cannot be an endpoint of an edge carried by that piece. -/
theorem not_mem_pieceEdge_of_mem_component_ne
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C D : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) (hDC : D ≠ C)
    {x : {x : V // x ∈ (PairDeletion.deletedSet e)ᶜ}}
    (hxD : (PairDeletion.edgeGraph G e).connectedComponentMk x = D) :
    x.val ∉ f := by
  intro hxf
  have hxPiece : x.val ∈ pieceVertexSet G e C :=
    forall_mem_pieceVertexSet_of_mem_pieceAmbientEdges G e C hf x.val hxf
  have hxLift : x.val ∈ liftedComponentSet G e C :=
    (mem_pieceVertexSet_iff G e C x.val).mp hxPiece |>.resolve_left x.property
  obtain ⟨hxout, hxSupp⟩ :=
    (mem_liftedComponentSet_iff G e C x.val).mp hxLift
  have hxC :
      (PairDeletion.edgeGraph G e).connectedComponentMk ⟨x.val, hxout⟩ = C :=
    (ConnectedComponent.mem_supp_iff C _).mp hxSupp
  apply hDC
  exact hxD.symm.trans (by simpa using hxC)

open Classical in
/-- Inclusion of a component of `G-e` outside the selected piece into
`G-f`.  All its vertices survive deletion of the endpoints of `f`. -/
noncomputable def outsideComponentToGlobalDeleteEmbedding
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C D : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) (hDC : D ≠ C) :
    D.toSimpleGraph ↪g PairDeletion.edgeGraph G f where
  toEmbedding :=
    { toFun := fun x => ⟨x.val.val, by
        have hnot : x.val.val ∉ f :=
          not_mem_pieceEdge_of_mem_component_ne G e C D f hf hDC x.property
        show x.val.val ∉ f.toFinset
        intro hx
        exact hnot (Sym2.mem_toFinset.mp hx)⟩
      inj' := by
        intro x y hxy
        have hval : x.val.val = y.val.val :=
          congr_arg
            (fun z : {z : V // z ∈ (PairDeletion.deletedSet f)ᶜ} => z.val) hxy
        exact Subtype.ext (Subtype.ext hval) }
  map_rel_iff' := Iff.rfl

open Classical in
/-- Vertices in the same non-selected component of `G-e` remain connected
after deleting the endpoints of a piece edge `f`. -/
theorem outsideComponent_reachable_globalDelete
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C D : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) (hDC : D ≠ C)
    {x y : {z : V // z ∈ (PairDeletion.deletedSet e)ᶜ}}
    (hxD : (PairDeletion.edgeGraph G e).connectedComponentMk x = D)
    (hyD : (PairDeletion.edgeGraph G e).connectedComponentMk y = D) :
    (PairDeletion.edgeGraph G f).Reachable
      (outsideComponentToGlobalDeleteEmbedding G e C D f hf hDC ⟨x, hxD⟩)
      (outsideComponentToGlobalDeleteEmbedding G e C D f hf hDC ⟨y, hyD⟩) := by
  exact (D.reachable_toSimpleGraph hxD hyD).map
    (outsideComponentToGlobalDeleteEmbedding G e C D f hf hDC).toHom

open Classical in
/-- Regard a surviving ambient vertex which belongs to a piece as a vertex
of the local pair-deletion graph. -/
noncomputable def globalDeleteVertexToLocalOfMem
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C)
    (z : {x : V // x ∈ (PairDeletion.deletedSet f)ᶜ})
    (hzPiece : z.val ∈ pieceVertexSet G e C) :
    {x : {x : V // x ∈ pieceVertexSet G e C} //
      x ∈ (PairDeletion.deletedSet (liftEdgeToPiece G e C f hf))ᶜ} :=
  ⟨⟨z.val, hzPiece⟩, by
    show (⟨z.val, hzPiece⟩ : {x : V // x ∈ pieceVertexSet G e C}) ∉
      (liftEdgeToPiece G e C f hf).toFinset
    intro hz
    have hzLocal :
        (⟨z.val, hzPiece⟩ : {x : V // x ∈ pieceVertexSet G e C}) ∈
          liftEdgeToPiece G e C f hf :=
      Sym2.mem_toFinset.mp hz
    have hzAmbient : z.val ∈ f :=
      (mem_liftEdgeToPiece_iff G e C f hf ⟨z.val, hzPiece⟩).mp hzLocal
    exact z.property (Sym2.mem_toFinset.mpr hzAmbient)⟩

open Classical in
@[simp]
theorem localDeleteGraphEmbedding_globalDeleteVertexToLocalOfMem
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C)
    (z : {x : V // x ∈ (PairDeletion.deletedSet f)ᶜ})
    (hzPiece : z.val ∈ pieceVertexSet G e C) :
    localDeleteGraphEmbedding G e C f hf
        (globalDeleteVertexToLocalOfMem G e C f hf z hzPiece) = z := by
  apply Subtype.ext
  rfl

open Classical in
/-- The inclusion map on components is surjective for every piece edge
distinct from the chosen separator edge.  Equivalently, adding all the other
`{u,v}`-pieces creates no new component after deleting the endpoints of `f`.

The only genuine connectivity input is that the positive split edge `e`
is a minimal separator in the ambient 2-connected graph: every component
of `G-e` has a neighbour at each endpoint of `e`. -/
theorem localDeleteComponentMap_surjective_of_isKConnected_two
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (hsplit : 2 ≤ PairDeletion.edgeComponentCount G e)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) (hne : f ≠ e) :
    Function.Surjective (localDeleteComponentMap G e C f hf) := by
  have he : ¬e.IsDiag :=
    G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp heG)
  have hfG : f ∈ G.edgeFinset := (Finset.mem_inter.mp hf).1
  have hfNonDiag : ¬f.IsDiag :=
    G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp hfG)
  obtain ⟨w, hwE, hwF⟩ :=
    exists_mem_not_mem_deletedSet_of_ne e f he hfNonDiag hne.symm
  have hwPiece : w ∈ pieceVertexSet G e C := by
    apply Or.inl
    exact Sym2.mem_toFinset.mpr hwE
  let wGlobal : {x : V // x ∈ (PairDeletion.deletedSet f)ᶜ} := ⟨w, hwF⟩
  let wLocal := globalDeleteVertexToLocalOfMem G e C f hf wGlobal hwPiece
  have hmin : G.IsMinSeparator e.toFinset :=
    PairDeletion.deletedSet_isMinSeparator_of_isKConnected_two
      G hcard hG e heG hsplit
  intro K
  refine K.ind ?_
  intro z
  by_cases hzPiece : z.val ∈ pieceVertexSet G e C
  · let zLocal := globalDeleteVertexToLocalOfMem G e C f hf z hzPiece
    refine ⟨(PairDeletion.edgeGraph (pieceGraph G e C)
      (liftEdgeToPiece G e C f hf)).connectedComponentMk zLocal, ?_⟩
    rw [localDeleteComponentMap_mk]
    congr 1
  · have hzE : z.val ∈ (PairDeletion.deletedSet e)ᶜ := by
      intro hz
      exact hzPiece (Or.inl hz)
    let zE : {x : V // x ∈ (PairDeletion.deletedSet e)ᶜ} := ⟨z.val, hzE⟩
    let D : (PairDeletion.edgeGraph G e).ConnectedComponent :=
      (PairDeletion.edgeGraph G e).connectedComponentMk zE
    have hDC : D ≠ C := by
      intro hEq
      apply hzPiece
      apply Or.inr
      refine ⟨hzE, ?_⟩
      rw [ConnectedComponent.mem_supp_iff]
      simpa only [D] using hEq
    obtain ⟨c, hcE, hcD, hwc⟩ :=
      hmin.exists_neighbor_in_component (Sym2.mem_toFinset.mpr hwE) D
    let cE : {x : V // x ∈ (PairDeletion.deletedSet e)ᶜ} := ⟨c, hcE⟩
    have hcNotF : c ∉ f :=
      not_mem_pieceEdge_of_mem_component_ne G e C D f hf hDC hcD
    have hcF : c ∈ (PairDeletion.deletedSet f)ᶜ := by
      show c ∉ f.toFinset
      intro hc
      exact hcNotF (Sym2.mem_toFinset.mp hc)
    let cGlobal : {x : V // x ∈ (PairDeletion.deletedSet f)ᶜ} := ⟨c, hcF⟩
    have hzcRaw := outsideComponent_reachable_globalDelete
      G e C D f hf hDC (x := zE) (y := cE) (by rfl) hcD
    have hzc : (PairDeletion.edgeGraph G f).Reachable z cGlobal := by
      simpa only [outsideComponentToGlobalDeleteEmbedding, zE, cE, cGlobal] using hzcRaw
    have hcw : (PairDeletion.edgeGraph G f).Reachable cGlobal wGlobal := by
      apply SimpleGraph.Adj.reachable
      change G.Adj c w
      exact hwc.symm
    have hzw : (PairDeletion.edgeGraph G f).Reachable z wGlobal := hzc.trans hcw
    refine ⟨(PairDeletion.edgeGraph (pieceGraph G e C)
      (liftEdgeToPiece G e C f hf)).connectedComponentMk wLocal, ?_⟩
    rw [localDeleteComponentMap_mk]
    apply ConnectedComponent.eq.mpr
    simpa only [
      localDeleteGraphEmbedding_globalDeleteVertexToLocalOfMem] using hzw.symm

open Classical in
/-- The component count after deleting a piece edge distinct from the chosen
separator edge in the ambient graph is at most the corresponding count inside
the piece.  This is the precise cardinal inequality needed for the upper-bound
direction of the `S` recurrence. -/
theorem edgeComponentCount_le_piece_edgeComponentCount
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (hsplit : 2 ≤ PairDeletion.edgeComponentCount G e)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) (hne : f ≠ e) :
    PairDeletion.edgeComponentCount G f ≤
      PairDeletion.edgeComponentCount (pieceGraph G e C)
        (liftEdgeToPiece G e C f hf) := by
  unfold PairDeletion.edgeComponentCount
  exact Nat.card_le_card_of_surjective
    (localDeleteComponentMap G e C f hf)
    (localDeleteComponentMap_surjective_of_isKConnected_two
      G hcard hG e heG hsplit C f hf hne)

open Classical in
/-- Consequently the ambient split multiplicity of a non-separator piece
edge is at most its local split multiplicity. -/
theorem edgeMultiplicity_le_piece_edgeMultiplicity
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G.IsKConnected 2)
    (e : Sym2 V) (heG : e ∈ G.edgeFinset)
    (hsplit : 2 ≤ PairDeletion.edgeComponentCount G e)
    (C : (PairDeletion.edgeGraph G e).ConnectedComponent) (f : Sym2 V)
    (hf : f ∈ pieceAmbientEdges G e C) (hne : f ≠ e) :
    PairDeletion.edgeMultiplicity G f ≤
      PairDeletion.edgeMultiplicity (pieceGraph G e C)
        (liftEdgeToPiece G e C f hf) := by
  unfold PairDeletion.edgeMultiplicity
  exact Nat.sub_le_sub_right
    (edgeComponentCount_le_piece_edgeComponentCount
      G hcard hG e heG hsplit C f hf hne) 1

end AdjacentTwoCut

/-! ## Concrete graph ledger and explicit geometric assumptions -/

namespace ConcreteLedger

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Sum of the concrete pair-deletion multiplicities over graph edges. -/
noncomputable def splitTotal : ℕ :=
  ∑ e ∈ G.edgeFinset, PairDeletion.edgeMultiplicity G e

/-- Concrete split budget incident with a vertex. -/
noncomputable def incidentSplit (v : V) : ℕ :=
  FiniteLedger.incidentWeight G.edgeFinset (PairDeletion.edgeMultiplicity G) v

/-- The concrete weighted handshake for `s_uv`. -/
theorem sum_incidentSplit_eq_two_mul_splitTotal :
    (∑ v : V, incidentSplit G v) = 2 * splitTotal G := by
  classical
  apply FiniteLedger.sum_incidentWeight_eq_two_mul
  intro e he
  exact G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp he)

/-- A finite sum of concrete edge multiplicities vanishes exactly when every
edge multiplicity vanishes.  This exposes the precise base case used by the
planar density lemma below. -/
theorem splitTotal_eq_zero_iff :
    splitTotal G = 0 ↔
      ∀ e ∈ G.edgeFinset, PairDeletion.edgeMultiplicity G e = 0 := by
  classical
  simp [splitTotal]

/-- If the total split budget is positive, some graph edge is an adjacent
two-separator and leaves at least two components after deleting its ends. -/
theorem exists_split_edge_of_splitTotal_pos
    (hcard : 3 ≤ Fintype.card V) (hpos : 0 < splitTotal G) :
    ∃ e ∈ G.edgeFinset, 2 ≤ PairDeletion.edgeComponentCount G e := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : splitTotal G = 0 := (splitTotal_eq_zero_iff G).2 (by
    intro e heG
    have hnotTwo := hnone e heG
    have hiff := PairDeletion.edgeMultiplicity_pos_iff_two_le G hcard e heG
    exact Nat.eq_zero_of_not_pos (fun hpositive => by
      have htwo := hiff.mp hpositive
      omega))
  omega

namespace Assumptions

/-- **Assumption interface for LOCAL-OCC.**  It says that the marked vertices
owned by `v` obey the facial occurrence inequality with the *concrete*
pair-deletion split budget.  No theorem in this file manufactures this
assumption. -/
def LocalOccurrence (marked : V → ℕ) : Prop :=
  ∀ v, 2 * marked v ≤ G.degree v + incidentSplit G v

/-- **Assumption interface for SPLIT-DEFICIT**, in additive form
`m + S + 6 ≤ 3n`.  `S` is the concrete edge sum of
`cc(G-{u,v})-1`.  No theorem in this file asserts this for all planar graphs. -/
def SplitDeficit : Prop :=
  G.edgeFinset.card + splitTotal G + 6 ≤ 3 * Fintype.card V

end Assumptions

/-- The graph-level deterministic bridge.  Given `LOCAL-OCC` and
`SPLIT-DEFICIT` for the actual pair-deletion multiplicities, the marked count
has the additive full-star gap. -/
theorem marked_add_six_le_three_mul_card
    (marked : V → ℕ)
    (hlocal : Assumptions.LocalOccurrence G marked)
    (hsplit : Assumptions.SplitDeficit G) :
    (∑ v, marked v) + 6 ≤ 3 * Fintype.card V := by
  have hmarked : (∑ v, marked v) ≤ G.edgeFinset.card + splitTotal G := by
    apply FiniteLedger.aggregate_local_bounds marked (fun v => G.degree v) (incidentSplit G)
    · exact hlocal
    · exact G.sum_degrees_eq_twice_card_edges
    · exact sum_incidentSplit_eq_two_mul_splitTotal G
  unfold Assumptions.SplitDeficit at hsplit
  omega

/-- Truncated-subtraction presentation used in the paper. -/
theorem marked_le_three_mul_card_sub_six
    (marked : V → ℕ)
    (hlocal : Assumptions.LocalOccurrence G marked)
    (hsplit : Assumptions.SplitDeficit G) :
    (∑ v, marked v) ≤ 3 * Fintype.card V - 6 := by
  have h := marked_add_six_le_three_mul_card G marked hlocal hsplit
  omega

end ConcreteLedger

/-! ## Layer C: what the current planar API really supplies -/

namespace PlanarAPI

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Deleting a pair preserves the repository's minor-defined planarity.  This
uses only minor/induced-subgraph closure, not a rotation-system axiom. -/
theorem pairDeletion_isPlanar {G : SimpleGraph V} (hG : G.IsPlanar) (u v : V) :
    (PairDeletion.graph G u v).IsPlanar :=
  hG.induce _

/-- Base case for SPLIT-DEFICIT: when all concrete split multiplicities sum
to zero, the ordinary planar edge bound supplies the deficit inequality.

This theorem introduces no new axiom, but its `#print axioms` intentionally
shows the repository's existing topological axiom
`IsPlanar.hasPlanarRotationSystem`, inherited through
`IsPlanar.edgeFinset_card_le`. -/
theorem splitDeficit_of_splitTotal_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V)
    (hzero : ConcreteLedger.splitTotal G = 0) :
    ConcreteLedger.Assumptions.SplitDeficit G := by
  have hedge := hG.edgeFinset_card_le G hcard
  unfold ConcreteLedger.Assumptions.SplitDeficit
  rw [hzero]
  omega

end PlanarAPI

/-! ## API provenance checks

These commands make the imported revision visible in the compiler output.
They are checks, not additional assumptions. -/

#check SimpleGraph.IsPlanar
#check SimpleGraph.IsPlanar.induce
#check SimpleGraph.IsPlanar.minor
#check SimpleGraph.IsPlanar.hasPlanarRotationSystem
#check SimpleGraph.IsPlanar.edgeFinset_card_le
#check SimpleGraph.RotationSystem.facePerm
#check SimpleGraph.RotationSystem.IsPlanarEmbedding
#check SimpleGraph.RotationSystem.HasCyclicFaces
#check SimpleGraph.ConnectedComponent
#check SimpleGraph.ConnectedComponent.toSimpleGraph
#check SimpleGraph.Block
#check SimpleGraph.blocks
#check SimpleGraph.BlockTree

#print axioms FiniteLedger.sum_incidentWeight_eq_two_mul
#print axioms FiniteLedger.aggregate_local_bounds
#print axioms FiniteLedger.split_recursion_aggregation
#print axioms FiniteLedger.articulation_with_slack
#print axioms PairDeletion.componentCount_comm
#print axioms PairDeletion.multiplicity_comm
#print axioms PairDeletion.natCard_deletedSet_of_not_isDiag
#print axioms PairDeletion.natCard_edgeGraph_vertices_add_two
#print axioms PairDeletion.edgeComponentCount_pos_of_edge
#print axioms PairDeletion.edgeMultiplicity_add_one_eq
#print axioms PairDeletion.edgeMultiplicity_pos_iff_two_le
#print axioms PairDeletion.deletedSet_isMinSeparator_of_isKConnected_two
#print axioms PairDeletion.sum_pieceVertexCount_add_two
#print axioms AdjacentTwoCut.map_pieceGraph_edgeFinset
#print axioms AdjacentTwoCut.pieceEdgeCount_eq_card_edgeFinset
#print axioms AdjacentTwoCut.erase_separator_eq_pieceExclusiveUnion
#print axioms AdjacentTwoCut.pieceEdgeTotal_add_one_eq
#print axioms AdjacentTwoCut.forall_mem_pieceVertexSet_of_mem_pieceAmbientEdges
#print axioms AdjacentTwoCut.map_liftEdgeToPiece
#print axioms AdjacentTwoCut.mem_liftEdgeToPiece_iff
#print axioms AdjacentTwoCut.localDeleteVertexEmbedding
#print axioms AdjacentTwoCut.localDeleteGraphEmbedding
#print axioms AdjacentTwoCut.localDelete_reachable_globalDelete
#print axioms AdjacentTwoCut.localDeleteComponentMap
#print axioms AdjacentTwoCut.localDeleteComponentMap_mk
#print axioms AdjacentTwoCut.not_mem_pieceEdge_of_mem_component_ne
#print axioms AdjacentTwoCut.outsideComponentToGlobalDeleteEmbedding
#print axioms AdjacentTwoCut.outsideComponent_reachable_globalDelete
#print axioms AdjacentTwoCut.globalDeleteVertexToLocalOfMem
#print axioms AdjacentTwoCut.localDeleteGraphEmbedding_globalDeleteVertexToLocalOfMem
#print axioms AdjacentTwoCut.localDeleteComponentMap_surjective_of_isKConnected_two
#print axioms AdjacentTwoCut.edgeComponentCount_le_piece_edgeComponentCount
#print axioms AdjacentTwoCut.edgeMultiplicity_le_piece_edgeMultiplicity
#print axioms AdjacentTwoCut.pieceGraph_isPlanar
#print axioms ConcreteLedger.sum_incidentSplit_eq_two_mul_splitTotal
#print axioms ConcreteLedger.splitTotal_eq_zero_iff
#print axioms ConcreteLedger.exists_split_edge_of_splitTotal_pos
#print axioms ConcreteLedger.marked_add_six_le_three_mul_card
#print axioms ConcreteLedger.marked_le_three_mul_card_sub_six
#print axioms PlanarAPI.pairDeletion_isPlanar
#print axioms PlanarAPI.splitDeficit_of_splitTotal_eq_zero

end KID981TopologicalBridge
