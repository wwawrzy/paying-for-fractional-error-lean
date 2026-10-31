import GraphTheory.PlanarGirth
import GraphTheory.Faces.SplitDeficit

/-!
# Four-contact ledger for planar graphs

This file formalizes the arithmetic and the concrete `SimpleGraph` bridge used
by the four-foreign-contact bound.  In contrast with a purely numerical test,
the graph layer below uses the actual components of the graph obtained after
deleting the two endpoints of an edge.

The basic aggregation theorem deliberately names two graph-valued inputs:

* `GraphLedger.LocalOccurrenceFour G marked` is LOCAL-OCC with coefficient
  three (four foreign contacts);
* `GraphLedger.SplitDeficit G` is SPLIT-DEFICIT for the concrete component
  counts.

No axiom is introduced here. The split-deficit module discharges the second input
for every finite planar 2-connected graph. Consequently the planar endpoint
in this file assumes only LOCAL-OCC. The companion
`GraphTheory.Faces.FourContactLocalOcc` replaces that remaining numerical surface by
an explicitly constructed port graph and component embeddings. This layering
keeps the still-open faithful facial-disk surgery visible rather than hiding
it inside the finite ledger.
-/

namespace PlaneTopology.Faces.FourContactLedger

open scoped BigOperators

/-! ## 1. Finite weighted handshake and contact-parameter aggregation -/

namespace FiniteLedger

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sum the weights of all unordered pairs in `edges` incident with `v`. -/
def incidentWeight (edges : Finset (Sym2 V)) (weight : Sym2 V → ℕ) (v : V) : ℕ :=
  ∑ e ∈ edges, if v ∈ e then weight e else 0

/-- Every non-diagonal unordered pair contributes its weight at exactly two
ends.  This statement is independent of the number of contacts. -/
theorem sum_incidentWeight_eq_two_mul
    (edges : Finset (Sym2 V)) (weight : Sym2 V → ℕ)
    (hnondiag : ∀ e ∈ edges, ¬e.IsDiag) :
    (∑ v : V, incidentWeight edges weight v) =
      2 * ∑ e ∈ edges, weight e := by
  classical
  unfold incidentWeight
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ edges, ∑ v : V, if v ∈ e then weight e else 0) =
        ∑ e ∈ edges, e.toFinset.card * weight e := by
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

/-- Parameterized local aggregation.  For `contacts = 4`, the coefficient is
`contacts - 1 = 3`. -/
theorem sum_local_occ_contact_count
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (contacts : ℕ) (marked incident : ι → ℕ) (component : ε → ℕ)
    (hlocal : ∀ d, (contacts - 1) * marked d ≤ incident d)
    (hhandshake : (∑ d, incident d) = 2 * ∑ e, component e) :
    (contacts - 1) * (∑ d, marked d) ≤ 2 * ∑ e, component e := by
  calc
    (contacts - 1) * (∑ d, marked d) =
        ∑ d, (contacts - 1) * marked d := by rw [Finset.mul_sum]
    _ ≤ ∑ d, incident d := Finset.sum_le_sum fun d _ => hlocal d
    _ = 2 * ∑ e, component e := hhandshake

end FiniteLedger

/-! ## 1b. A genuine finite marked set and its owner fibers -/

namespace OwnerPartition

variable {X D : Type*} [Fintype D] [DecidableEq D]

/-- Number of marked objects whose owner is `d`.  In the paper, `X` is the
vertex type of the original graph and `D` is the vertex type of the contact
graph. -/
def markedFiberCount (marked : Finset X) (owner : X → D) (d : D) : ℕ :=
  (marked.filter fun x => owner x = d).card

/-- The owner fibers form an honest partition of the finite marked set. -/
theorem sum_markedFiberCount_eq_card
    (marked : Finset X) (owner : X → D) :
    (∑ d : D, markedFiberCount marked owner d) = marked.card := by
  classical
  symm
  simpa [markedFiberCount] using
    (Finset.card_eq_sum_card_fiberwise
      (f := owner) (s := marked) (t := Finset.univ)
      (by
        intro x hx
        simp))

end OwnerPartition

/-! ## 2. Actual pair deletion in a finite simple graph -/

namespace PairDeletion

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The two vertices represented by an unordered pair. -/
def deletedSet (e : Sym2 V) : Set V := e.toFinset

/-- The induced graph after deleting the endpoints of `e`. -/
def edgeGraph (G : SimpleGraph V) (e : Sym2 V) :
    SimpleGraph {x : V // x ∈ (deletedSet e)ᶜ} :=
  G.induce (deletedSet e)ᶜ

/-- The actual number of connected components after deleting `e`. -/
noncomputable def edgeComponentCount (G : SimpleGraph V) (e : Sym2 V) : ℕ :=
  Nat.card (edgeGraph G e).ConnectedComponent

/-- Endpoint notation for the same component count. -/
noncomputable def componentCount (G : SimpleGraph V) (u v : V) : ℕ :=
  edgeComponentCount G s(u, v)

/-- Concrete split multiplicity `cc(G-e)-1`. -/
noncomputable def edgeMultiplicity (G : SimpleGraph V) (e : Sym2 V) : ℕ :=
  edgeComponentCount G e - 1

theorem natCard_deletedSet_of_not_isDiag
    [Fintype V] (e : Sym2 V) (he : ¬e.IsDiag) :
    Nat.card {x : V // x ∈ deletedSet e} = 2 := by
  classical
  change Nat.card {x : V // x ∈ e.toFinset} = 2
  rw [← Fintype.card_eq_nat_card, Fintype.card_coe]
  exact Sym2.card_toFinset_of_not_isDiag e he

/-- A non-diagonal pair deletes exactly two vertices. -/
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

/-- An edge in a graph with at least three vertices leaves a nonempty graph
after its endpoints are deleted, hence at least one component. -/
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

end PairDeletion

/-! ## 3. Four-contact statements on `SimpleGraph` -/

namespace GraphLedger

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Sum of the actual component counts `cc(G-e)` over graph edges. -/
noncomputable def componentTotal : ℕ :=
  ∑ e ∈ G.edgeFinset, PairDeletion.edgeComponentCount G e

/-- Sum of the actual split multiplicities `cc(G-e)-1`. -/
noncomputable def splitTotal : ℕ :=
  ∑ e ∈ G.edgeFinset, PairDeletion.edgeMultiplicity G e

/-- Component budget incident with `v`, in unordered-edge form. -/
noncomputable def incidentComponents (v : V) : ℕ :=
  FiniteLedger.incidentWeight G.edgeFinset
    (PairDeletion.edgeComponentCount G) v

/-- The same local budget in the paper's neighbor notation. -/
noncomputable def neighborComponentSum (v : V) : ℕ :=
  ∑ c ∈ G.neighborFinset v, PairDeletion.componentCount G v c

/-- Reindex the paper's sum over neighbors as a sum over incident unordered
edges. -/
theorem neighborComponentSum_eq_incidentComponents (v : V) :
    neighborComponentSum G v = incidentComponents G v := by
  classical
  unfold neighborComponentSum incidentComponents FiniteLedger.incidentWeight
  rw [← Finset.sum_filter]
  rw [← G.incidenceFinset_eq_filter]
  refine Finset.sum_bij (fun c _ => s(v, c)) ?_ ?_ ?_ ?_
  · intro c hc
    exact (G.mem_incidenceFinset v s(v, c)).mpr
      (G.mem_incidence_iff_neighbor.mpr ((G.mem_neighborFinset v c).mp hc))
  · intro c₁ hc₁ c₂ hc₂ h
    exact Sym2.congr_right.mp h
  · intro e he
    have heInc : e ∈ G.incidenceSet v := by
      exact (G.mem_incidenceFinset v e).mp he
    let c := G.otherVertexOfIncident heInc
    have hc : c ∈ G.neighborFinset v := by
      exact (G.mem_neighborFinset v c).mpr (G.incidence_other_prop heInc)
    refine ⟨c, hc, ?_⟩
    exact Sym2.other_spec' heInc.2
  · intro c hc
    rfl

/-- Weighted handshake for the concrete component counts. -/
theorem sum_incidentComponents_eq_two_mul_componentTotal :
    (∑ v : V, incidentComponents G v) = 2 * componentTotal G := by
  classical
  apply FiniteLedger.sum_incidentWeight_eq_two_mul
  intro e he
  exact G.not_isDiag_of_mem_edgeSet ((SimpleGraph.mem_edgeFinset).mp he)

/-- LOCAL-OCC for four contacts, stated with the actual graph and actual
pair-deletion component counts. -/
def LocalOccurrenceFour (marked : V → ℕ) : Prop :=
  ∀ v, 3 * marked v ≤ neighborComponentSum G v

/-- SPLIT-DEFICIT for the actual graph multiplicities, in additive `Nat`
form to avoid truncated subtraction. -/
def SplitDeficit : Prop :=
  G.edgeFinset.card + splitTotal G + 6 ≤ 3 * Fintype.card V

/-- Target finite-sum ledger: summing
`3 |A_d| ≤ ∑_{c∈N(d)} cc(G-{d,c})` counts every edge twice. -/
theorem sum_local_occ_four
    (marked : V → ℕ) (hlocal : LocalOccurrenceFour G marked) :
    3 * (∑ v, marked v) ≤ 2 * componentTotal G := by
  calc
    3 * (∑ v, marked v) = ∑ v, 3 * marked v := by
      rw [Finset.mul_sum]
    _ ≤ ∑ v, neighborComponentSum G v :=
      Finset.sum_le_sum fun v _ => hlocal v
    _ = ∑ v, incidentComponents G v := by
      apply Finset.sum_congr rfl
      intro v _
      exact neighborComponentSum_eq_incidentComponents G v
    _ = 2 * componentTotal G :=
      sum_incidentComponents_eq_two_mul_componentTotal G

/-- On graphs with at least three vertices, the sum of component counts is
exactly `|E| + S`. -/
theorem componentTotal_eq_card_edges_add_splitTotal
    (hcard : 3 ≤ Fintype.card V) :
    componentTotal G = G.edgeFinset.card + splitTotal G := by
  classical
  unfold componentTotal splitTotal PairDeletion.edgeMultiplicity
  calc
    (∑ e ∈ G.edgeFinset, PairDeletion.edgeComponentCount G e) =
        ∑ e ∈ G.edgeFinset,
          (1 + (PairDeletion.edgeComponentCount G e - 1)) := by
      apply Finset.sum_congr rfl
      intro e he
      have hpos := PairDeletion.edgeComponentCount_pos_of_edge G hcard e he
      omega
    _ = G.edgeFinset.card +
        ∑ e ∈ G.edgeFinset, (PairDeletion.edgeComponentCount G e - 1) := by
      rw [Finset.sum_add_distrib]
      simp

/-- Four-contact two-connected aggregation on the concrete graph.  The name
describes the paper use; formally, two-connectivity is used upstream to prove
the two explicit hypotheses. -/
theorem twoConnected_aggregation_four
    (marked : V → ℕ) (hcard : 3 ≤ Fintype.card V)
    (hlocal : LocalOccurrenceFour G marked)
    (hsplit : SplitDeficit G) :
    (∑ v, marked v) + 4 ≤ 2 * Fintype.card V := by
  have hsum := sum_local_occ_four G marked hlocal
  have hcomponents := componentTotal_eq_card_edges_add_splitTotal G hcard
  unfold SplitDeficit at hsplit
  omega

/-- Truncated-subtraction presentation `|A| ≤ 2|V|-4` used in the paper. -/
theorem twoConnected_aggregation_four_paper_form
    (marked : V → ℕ) (hcard : 3 ≤ Fintype.card V)
    (hlocal : LocalOccurrenceFour G marked)
    (hsplit : SplitDeficit G) :
    (∑ v, marked v) ≤ 2 * Fintype.card V - 4 := by
  have h := twoConnected_aggregation_four G marked hcard hlocal hsplit
  omega

/-- The same graph theorem for a concrete finite marked set partitioned by
an owner map into the vertices of the contact graph.  Thus the conclusion is
about `marked.card`, rather than an unrelated numerical sum. -/
theorem twoConnected_markedSet_bound
    {X : Type*}
    (marked : Finset X) (owner : X → V)
    (hcard : 3 ≤ Fintype.card V)
    (hlocal : ∀ d,
      3 * OwnerPartition.markedFiberCount marked owner d ≤
        neighborComponentSum G d)
    (hsplit : SplitDeficit G) :
    marked.card ≤ 2 * Fintype.card V - 4 := by
  have h := twoConnected_aggregation_four_paper_form G
    (fun d => OwnerPartition.markedFiberCount marked owner d)
    hcard hlocal hsplit
  rw [OwnerPartition.sum_markedFiberCount_eq_card] at h
  exact h

/-- Genuine planar base case of SPLIT-DEFICIT when no edge has positive split
multiplicity.  It uses the repository's planar edge bound. -/
theorem splitDeficit_of_splitTotal_eq_zero
    (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V)
    (hzero : splitTotal G = 0) :
    SplitDeficit G := by
  have hedge := hG.edgeFinset_card_le G hcard
  unfold SplitDeficit
  rw [hzero]
  omega

/-- General graph-valued SPLIT-DEFICIT.  The strong induction, concrete
adjacent-two-cut pieces, component-count recurrence, and proof that every piece
is again 2-connected are supplied by the split-deficit module; no graph enumeration
or random test enters this theorem. -/
theorem splitDeficit_of_planar_twoConnected
    (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V)
    (htwo : G.IsKConnected 2) :
    SplitDeficit G := by
  have h := PlaneTopology.Faces.SplitDeficit.PieceFacts.planar_twoConnected_splitDeficit
    G hcard hG htwo
  unfold SplitDeficit splitTotal PairDeletion.edgeMultiplicity
    PairDeletion.edgeComponentCount PairDeletion.edgeGraph PairDeletion.deletedSet
  unfold KID981TopologicalBridge.ConcreteLedger.Assumptions.SplitDeficit
    KID981TopologicalBridge.ConcreteLedger.splitTotal
    KID981TopologicalBridge.PairDeletion.edgeMultiplicity
    KID981TopologicalBridge.PairDeletion.edgeComponentCount
    KID981TopologicalBridge.PairDeletion.edgeGraph
    KID981TopologicalBridge.PairDeletion.deletedSet at h
  exact h

/-- The four-contact aggregation with SPLIT-DEFICIT now discharged for every
finite planar 2-connected graph.  LOCAL-OCC remains the sole geometric input. -/
theorem planar_twoConnected_four_contact_bound
    (marked : V → ℕ) (hG : G.IsPlanar)
    (hcard : 3 ≤ Fintype.card V) (htwo : G.IsKConnected 2)
    (hlocal : LocalOccurrenceFour G marked) :
    (∑ v, marked v) + 4 ≤ 2 * Fintype.card V := by
  exact twoConnected_aggregation_four G marked hcard hlocal
    (splitDeficit_of_planar_twoConnected G hG hcard htwo)

/-- Marked-set form of the full planar 2-connected four-contact theorem. -/
theorem planar_twoConnected_markedSet_bound
    {X : Type*}
    (marked : Finset X) (owner : X → V)
    (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V)
    (htwo : G.IsKConnected 2)
    (hlocal : ∀ d,
      3 * OwnerPartition.markedFiberCount marked owner d ≤
        neighborComponentSum G d) :
    marked.card ≤ 2 * Fintype.card V - 4 := by
  exact twoConnected_markedSet_bound G marked owner hcard hlocal
    (splitDeficit_of_planar_twoConnected G hG hcard htwo)

/-- A graph-level, planar four-contact theorem for the no-split base case. -/
theorem planar_no_split_four_contact_bound
    (marked : V → ℕ) (hG : G.IsPlanar)
    (hcard : 3 ≤ Fintype.card V)
    (hzero : splitTotal G = 0)
    (hlocal : LocalOccurrenceFour G marked) :
    (∑ v, marked v) + 4 ≤ 2 * Fintype.card V := by
  exact twoConnected_aggregation_four G marked hcard hlocal
    (splitDeficit_of_splitTotal_eq_zero G hG hcard hzero)

/-- A concrete marked-set version of the genuine planar no-split base case. -/
theorem planar_no_split_markedSet_bound
    {X : Type*}
    (marked : Finset X) (owner : X → V)
    (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V)
    (hzero : splitTotal G = 0)
    (hlocal : ∀ d,
      3 * OwnerPartition.markedFiberCount marked owner d ≤
        neighborComponentSum G d) :
    marked.card + 4 ≤ 2 * Fintype.card V := by
  have h := planar_no_split_four_contact_bound G
    (fun d => OwnerPartition.markedFiberCount marked owner d)
    hG hcard hzero hlocal
  rw [OwnerPartition.sum_markedFiberCount_eq_card] at h
  exact h

end GraphLedger

/-! ## 4. Articulation ledger for coefficient two -/

/-- Summing the inductive four-contact bounds over articulation pieces leaves
exactly `2(k-1)` units for cross marks. -/
theorem sum_piece_bounds_four
    {ι : Type*} [Fintype ι]
    (pieceVertices pieceMarked : ι → ℤ) (vertices : ℤ)
    (hpiece : ∀ i, pieceMarked i ≤ 2 * pieceVertices i - 4)
    (hsizes : (∑ i, pieceVertices i) =
      vertices + (Fintype.card ι : ℤ) - 1) :
    (∑ i, pieceMarked i) ≤
      2 * vertices - 4 - 2 * ((Fintype.card ι : ℤ) - 1) := by
  have hsum :
      (∑ i, pieceMarked i) ≤ ∑ i, (2 * pieceVertices i - 4) :=
    Finset.sum_le_sum fun i _ => hpiece i
  have hformula :
      (∑ i, (2 * pieceVertices i - 4)) =
        2 * (∑ i, pieceVertices i) - 4 * (Fintype.card ι : ℤ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
    ring
  rw [hformula, hsizes] at hsum
  omega

/-- Exact cutvertex aggregation for four contacts:
`∑n_i=n+k-1`, `|Z_i|≤2n_i-4`, and `cross≤2(k-1)` imply
`|A|≤2n-4`. -/
theorem cutvertex_aggregation_four
    {ι : Type*} [Fintype ι]
    (pieceVertices pieceMarked : ι → ℤ)
    (vertices cross total : ℤ)
    (hpiece : ∀ i, pieceMarked i ≤ 2 * pieceVertices i - 4)
    (hsizes : (∑ i, pieceVertices i) =
      vertices + (Fintype.card ι : ℤ) - 1)
    (hcross : cross ≤ 2 * ((Fintype.card ι : ℤ) - 1))
    (htotal : total = (∑ i, pieceMarked i) + cross) :
    total ≤ 2 * vertices - 4 := by
  have hlocal :=
    sum_piece_bounds_four pieceVertices pieceMarked vertices hpiece hsizes
  omega

/-! ## 5. Active components -/

/-- Summing `2n_j-4` over nonempty active contact components retains one
additive gap of four globally. -/
theorem activeComponents_four_contact_gap
    (marked activeVertices vertices activeComponents : ℤ)
    (hactive : 1 ≤ activeComponents)
    (hvertices : activeVertices ≤ vertices)
    (hmarked : marked ≤ 2 * activeVertices - 4 * activeComponents) :
    marked ≤ 2 * vertices - 4 := by
  omega

/-- The additive four-contact gap implies the pointwise strict inequality
`marked < 2 * vertices`.  It does not claim a uniform multiplicative gap
below two on unbounded graph orders. -/
theorem pointwise_lt_two
    (marked vertices : ℤ) (hgap : marked ≤ 2 * vertices - 4) :
    marked < 2 * vertices := by
  omega

#print axioms FiniteLedger.sum_incidentWeight_eq_two_mul
#print axioms FiniteLedger.sum_local_occ_contact_count
#print axioms OwnerPartition.sum_markedFiberCount_eq_card
#print axioms PairDeletion.natCard_deletedSet_of_not_isDiag
#print axioms PairDeletion.natCard_edgeGraph_vertices_add_two
#print axioms PairDeletion.edgeComponentCount_pos_of_edge
#print axioms GraphLedger.neighborComponentSum_eq_incidentComponents
#print axioms GraphLedger.sum_incidentComponents_eq_two_mul_componentTotal
#print axioms GraphLedger.sum_local_occ_four
#print axioms GraphLedger.componentTotal_eq_card_edges_add_splitTotal
#print axioms GraphLedger.twoConnected_aggregation_four
#print axioms GraphLedger.twoConnected_aggregation_four_paper_form
#print axioms GraphLedger.twoConnected_markedSet_bound
#print axioms GraphLedger.splitDeficit_of_splitTotal_eq_zero
#print axioms GraphLedger.splitDeficit_of_planar_twoConnected
#print axioms GraphLedger.planar_twoConnected_four_contact_bound
#print axioms GraphLedger.planar_twoConnected_markedSet_bound
#print axioms GraphLedger.planar_no_split_four_contact_bound
#print axioms GraphLedger.planar_no_split_markedSet_bound
#print axioms sum_piece_bounds_four
#print axioms cutvertex_aggregation_four
#print axioms activeComponents_four_contact_gap
#print axioms pointwise_lt_two
end PlaneTopology.Faces.FourContactLedger
