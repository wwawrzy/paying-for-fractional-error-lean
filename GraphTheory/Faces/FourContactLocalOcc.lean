import GraphTheory.Faces.FourContactLedger

/-!
# Four-contact local-occurrence certificate

This file replaces the numerical LOCAL-OCC assumption by two concrete pieces
of data:

* a finite incidence structure with four distinct ports per marked object and
  its explicitly constructed bipartite port graph;
* an injection from the ports centred at each neighbour `c` into the actual
  connected components of `G - {d,c}`.

The only geometric boundary left visible is planarity of the constructed port
graph.  Producing that planarity proof from a faithful plane embedding and a
single facial disk is the topological surgery lemma; it is not disguised here
as a numerical inequality.
-/

namespace PlaneTopology.Faces.FourContactLocalOccurrence

open SimpleGraph
open scoped BigOperators

/-! ## 1. The concrete four-port graph -/

/-- Four distinct ports are assigned to every marked object.  Different
objects may share ports.  `used` records that no dummy port was declared. -/
structure FourPortIncidence (X P : Type*) where
  port : X → Fin 4 → P
  port_injective : ∀ x, Function.Injective (port x)
  used : ∀ p, ∃ x i, port x i = p

/-- Vertices of the auxiliary graph: apex and markers on the left, owner and
ports on the right. -/
abbrev PortVertex (X P : Type*) := Option X ⊕ Option P

namespace FourPortIncidence

variable {X P : Type*} (D : FourPortIncidence X P)

def apex (_D : FourPortIncidence X P) : PortVertex X P := Sum.inl none
def marker (_D : FourPortIncidence X P) (x : X) : PortVertex X P := Sum.inl (some x)
def owner (_D : FourPortIncidence X P) : PortVertex X P := Sum.inr none
def portVertex (_D : FourPortIncidence X P) (p : P) : PortVertex X P := Sum.inr (some p)

/-- Oriented left-to-right incidence relation.  `SimpleGraph.fromRel` below
adds the reverse orientations and removes loops. -/
def portRel : PortVertex X P → PortVertex X P → Prop
  | Sum.inl none, Sum.inr (some _) => True
  | Sum.inl (some _), Sum.inr none => True
  | Sum.inl (some x), Sum.inr (some p) => ∃ i, D.port x i = p
  | _, _ => False

/-- The concrete graph used in the facial-port Euler count. -/
def portGraph : SimpleGraph (PortVertex X P) :=
  SimpleGraph.fromRel D.portRel

/-- A stable decidability instance for all finite-set operations on the port
graph.  It is noncomputable only because the incidence relation is Prop-valued. -/
noncomputable instance portGraphDecidableAdj : DecidableRel D.portGraph.Adj :=
  Classical.decRel _

def leftFinset [Fintype X] [DecidableEq X] [DecidableEq P] :
    Finset (PortVertex X P) :=
  insert D.apex (Finset.univ.image D.marker)

def rightFinset [Fintype P] [DecidableEq X] [DecidableEq P] :
    Finset (PortVertex X P) :=
  insert D.owner (Finset.univ.image D.portVertex)

theorem marker_injective : Function.Injective D.marker := by
  intro x y h
  simpa [marker] using h

theorem portVertex_injective : Function.Injective D.portVertex := by
  intro p q h
  simpa [portVertex] using h

theorem portRel_parts
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P]
    {v w : PortVertex X P} (h : D.portRel v w) :
    v ∈ D.leftFinset ∧ w ∈ D.rightFinset := by
  rcases v with a | b
  · rcases a with _ | x
    · rcases w with c | d
      · simp [portRel] at h
      · rcases d with _ | p
        · simp [portRel] at h
        · simp [leftFinset, rightFinset, apex, portVertex]
    · rcases w with c | d
      · simp [portRel] at h
      · rcases d with _ | p
        · simp [leftFinset, rightFinset, marker, owner]
        · simp [leftFinset, rightFinset, marker, portVertex]
  · simp [portRel] at h

/-- The displayed left/right sets are a genuine bipartition of the concrete
port graph. -/
theorem portGraph_isBipartiteWith
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P] :
    D.portGraph.IsBipartiteWith (D.leftFinset : Set (PortVertex X P))
      (D.rightFinset : Set (PortVertex X P)) := by
  constructor
  · rw [Set.disjoint_left]
    intro z hzLeft hzRight
    rcases z with a | b <;>
      simp [leftFinset, rightFinset, apex, marker, owner, portVertex] at hzLeft hzRight
  · intro v w hadj
    rw [portGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · exact Or.inl (D.portRel_parts h)
    · have hp := D.portRel_parts h
      exact Or.inr ⟨hp.2, hp.1⟩

/-- Bipartiteness rules out triangles. -/
theorem portGraph_cliqueFree_three
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P] :
    D.portGraph.CliqueFree 3 := by
  exact D.portGraph_isBipartiteWith.isBipartite.cliqueFree (by omega)

/-- The vertex count is literal; the two extra vertices are apex and owner. -/
theorem card_portVertex (_D : FourPortIncidence X P) [Fintype X] [Fintype P] :
    Fintype.card (PortVertex X P) = Fintype.card X + Fintype.card P + 2 := by
  simp [PortVertex]
  omega

def markerNeighborFinset [Fintype P] [DecidableEq X] [DecidableEq P]
    (x : X) : Finset (PortVertex X P) :=
  insert D.owner (Finset.univ.image fun i : Fin 4 => D.portVertex (D.port x i))

def apexNeighborFinset [Fintype P] [DecidableEq X] [DecidableEq P] :
    Finset (PortVertex X P) :=
  Finset.univ.image D.portVertex

theorem neighborFinset_marker
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P]
    (x : X) :
    D.portGraph.neighborFinset (D.marker x) = D.markerNeighborFinset x := by
  ext w
  rcases w with a | b
  · rcases a with _ | y <;>
      simp [portGraph, portRel, markerNeighborFinset, marker, owner, portVertex]
  · rcases b with _ | p
    · simp [portGraph, portRel, markerNeighborFinset, marker, owner, portVertex]
    · simp [portGraph, portRel, markerNeighborFinset, marker, owner, portVertex]

theorem neighborFinset_apex
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P] :
    D.portGraph.neighborFinset D.apex = D.apexNeighborFinset := by
  ext w
  rcases w with a | b
  · rcases a with _ | x <;>
      simp [portGraph, portRel, apexNeighborFinset, apex, portVertex]
  · rcases b with _ | p <;>
      simp [portGraph, portRel, apexNeighborFinset, apex, portVertex]

theorem degree_marker
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P]
    (x : X) : D.portGraph.degree (D.marker x) = 5 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, D.neighborFinset_marker]
  have howner : D.owner ∉
      (Finset.univ.image fun i : Fin 4 => D.portVertex (D.port x i)) := by
    simp [owner, portVertex]
  have hinj : Function.Injective
      (fun i : Fin 4 => D.portVertex (D.port x i)) :=
    D.portVertex_injective.comp (D.port_injective x)
  rw [markerNeighborFinset]
  calc
    (insert D.owner
        (Finset.univ.image fun i : Fin 4 => D.portVertex (D.port x i))).card =
        (Finset.univ.image fun i : Fin 4 => D.portVertex (D.port x i)).card + 1 :=
      Finset.card_insert_of_notMem howner
    _ = Finset.univ.card + 1 := by
      rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin 4)) hinj]
    _ = 5 := by simp

theorem degree_apex
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P] :
    D.portGraph.degree D.apex = Fintype.card P := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, D.neighborFinset_apex,
    apexNeighborFinset]
  exact Finset.card_image_of_injective Finset.univ D.portVertex_injective

/-- Exact edge count.  It is obtained from the bipartite degree-sum theorem,
not from graph enumeration. -/
theorem card_edges_portGraph
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P] :
    Nat.card D.portGraph.edgeSet = 5 * Fintype.card X + Fintype.card P := by
  classical
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    D.portGraph_isBipartiteWith
  have hapex : D.apex ∉ Finset.univ.image D.marker := by
    simp [apex, marker]
  rw [leftFinset, Finset.sum_insert hapex, D.degree_apex,
      Finset.sum_image D.marker_injective.injOn] at hsum
  simp_rw [D.degree_marker] at hsum
  have hedge :
      D.portGraph.edgeFinset.card =
        5 * Fintype.card X + Fintype.card P := by
    simp [Finset.sum_const, Finset.card_univ] at hsum
    omega
  calc
    Nat.card D.portGraph.edgeSet = Fintype.card D.portGraph.edgeSet :=
      Nat.card_eq_fintype_card
    _ = D.portGraph.edgeFinset.card := D.portGraph.edgeFinset_card.symm
    _ = 5 * Fintype.card X + Fintype.card P := hedge

/-- Euler's bipartite planar bound applied to the concrete port graph. -/
theorem three_mul_card_le_card_of_isPlanar
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P]
    (hplanar : D.portGraph.IsPlanar) :
    3 * Fintype.card X ≤ Fintype.card P := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      haveI := hX
      simp
  | inr hX =>
      haveI := hX
      have hcard : 3 ≤ Fintype.card (PortVertex X P) := by
        rw [D.card_portVertex]
        have : 1 ≤ Fintype.card X := Fintype.card_pos
        omega
      have hbound := hplanar.edgeFinset_card_le_triangle_free D.portGraph
        D.portGraph_cliqueFree_three hcard
      have hboundNat :
          Nat.card D.portGraph.edgeSet ≤
            2 * Fintype.card (PortVertex X P) - 4 := by
        calc
          Nat.card D.portGraph.edgeSet = Fintype.card D.portGraph.edgeSet :=
            Nat.card_eq_fintype_card
          _ = D.portGraph.edgeFinset.card := D.portGraph.edgeFinset_card.symm
          _ ≤ 2 * Fintype.card (PortVertex X P) - 4 := by
            convert hbound
      have hbound' :
          5 * Fintype.card X + Fintype.card P ≤
            2 * (Fintype.card X + Fintype.card P + 2) - 4 := by
        calc
          5 * Fintype.card X + Fintype.card P =
              Nat.card D.portGraph.edgeSet := D.card_edges_portGraph.symm
          _ ≤ 2 * Fintype.card (PortVertex X P) - 4 := by
            exact hboundNat
          _ = 2 * (Fintype.card X + Fintype.card P + 2) - 4 := by
            rw [D.card_portVertex]
      omega

end FourPortIncidence

/-! ## 2. Ports inject into actual pair-deletion components -/

namespace ComponentPorts

variable {V P : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (d : V)

/-- The finite/topological occurrence certificate needed after the port-graph
count.  Every port has a neighbouring centre.  For each fixed centre `c`, the
ports with that centre inject into the genuine connected components of
`G - {d,c}`.

The injection is deliberately data, not a cardinal inequality: it is the
precise output expected from the facial-occurrence separation lemma. -/
structure ComponentPortCertificate (P : Type*) [Fintype P] where
  center : P → V
  center_adj : ∀ p, G.Adj d (center p)
  componentEmbedding : ∀ c : V, G.Adj d c →
    {p : P // center p = c} ↪
      (PlaneTopology.Faces.FourContactLedger.PairDeletion.edgeGraph G s(d, c)).ConnectedComponent

variable [Fintype P]

/-- Fibrewise port/component injections add up to the paper's actual
`sum_{c in N(d)} cc(G-{d,c})`. -/
theorem card_ports_le_neighborComponentSum
    (C : ComponentPortCertificate G d P) :
    Fintype.card P ≤
      PlaneTopology.Faces.FourContactLedger.GraphLedger.neighborComponentSum G d := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (f := C.center) (s := (Finset.univ : Finset P))
    (t := G.neighborFinset d)
    (by
      intro p hp
      exact (G.mem_neighborFinset d (C.center p)).mpr (C.center_adj p))
  unfold PlaneTopology.Faces.FourContactLedger.GraphLedger.neighborComponentSum
  calc
    Fintype.card P =
        ∑ c ∈ G.neighborFinset d,
          ((Finset.univ : Finset P).filter fun p => C.center p = c).card := by
      simpa using hpartition
    _ = ∑ c ∈ G.neighborFinset d,
          Fintype.card {p : P // C.center p = c} := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Fintype.card_subtype]
    _ ≤ ∑ c ∈ G.neighborFinset d,
          PlaneTopology.Faces.FourContactLedger.PairDeletion.componentCount G d c := by
      apply Finset.sum_le_sum
      intro c hc
      unfold PlaneTopology.Faces.FourContactLedger.PairDeletion.componentCount
        PlaneTopology.Faces.FourContactLedger.PairDeletion.edgeComponentCount
      rw [Nat.card_eq_fintype_card]
      have hadj : G.Adj d c := (G.mem_neighborFinset d c).mp hc
      exact Fintype.card_le_of_injective (C.componentEmbedding c hadj)
        (C.componentEmbedding c hadj).injective

end ComponentPorts

/-! ## 3. Conditional LOCAL-OCC and full graph theorem -/

section LocalOccurrence

variable {V X P : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (d : V) [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P]

/-- The complete finite part of LOCAL-OCC at one owner.  The only planar input
is planarity of the concrete graph `D.portGraph`; the right-hand side contains
the actual graph-deletion components. -/
theorem localOccurrenceAt_of_certificates
    (D : FourPortIncidence X P)
    (hplanar : D.portGraph.IsPlanar)
    (C : ComponentPorts.ComponentPortCertificate G d P) :
    3 * Fintype.card X ≤
      PlaneTopology.Faces.FourContactLedger.GraphLedger.neighborComponentSum G d := by
  exact le_trans (D.three_mul_card_le_card_of_isPlanar hplanar)
    (ComponentPorts.card_ports_le_neighborComponentSum G d C)

end LocalOccurrence

/-- The marked objects owned by `d`, as an actual finite type. -/
abbrev OwnerFiber {X V : Type*} [DecidableEq V]
    (marked : Finset X) (owner : X → V) (d : V) :=
  ↥(marked.filter fun x => owner x = d)

/-- All data needed to prove LOCAL-OCC for one owner fibre.  The port type may
depend on the owner. -/
structure OwnerLocalFourCertificate
    {V X : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (marked : Finset X) (ownerMap : X → V) (d : V) where
  Port : Type
  [portFintype : Fintype Port]
  [portDecidableEq : DecidableEq Port]
  incidence : FourPortIncidence (OwnerFiber marked ownerMap d) Port
  portGraph_planar : incidence.portGraph.IsPlanar
  componentPorts : ComponentPorts.ComponentPortCertificate G d Port

namespace OwnerLocalFourCertificate

variable {V X : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (marked : Finset X) (ownerMap : X → V)

/-- Owner-by-owner certificates imply the graph-valued LOCAL-OCC predicate,
with no numerical LOCAL-OCC assumption. -/
theorem localOccurrenceFour_of_certificates
    (cert : ∀ d, OwnerLocalFourCertificate G marked ownerMap d) :
    PlaneTopology.Faces.FourContactLedger.GraphLedger.LocalOccurrenceFour G
      (fun d => PlaneTopology.Faces.FourContactLedger.OwnerPartition.markedFiberCount
        marked ownerMap d) := by
  intro d
  let C := cert d
  letI : Fintype C.Port := C.portFintype
  letI : DecidableEq C.Port := C.portDecidableEq
  have h := localOccurrenceAt_of_certificates G d C.incidence
    C.portGraph_planar C.componentPorts
  simpa [OwnerFiber,
    PlaneTopology.Faces.FourContactLedger.OwnerPartition.markedFiberCount] using h

/-- End-to-end finite planar 2-connected four-contact bound.  SPLIT-DEFICIT is
proved internally by strong induction; LOCAL-OCC is supplied by concrete port
graphs and component embeddings, not by a cardinal inequality hypothesis. -/
theorem planar_twoConnected_markedSet_bound_of_certificates
    (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V)
    (htwo : G.IsKConnected 2)
    (cert : ∀ d, OwnerLocalFourCertificate G marked ownerMap d) :
    marked.card ≤ 2 * Fintype.card V - 4 := by
  exact PlaneTopology.Faces.FourContactLedger.GraphLedger.planar_twoConnected_markedSet_bound
    G marked ownerMap hG hcard htwo
      (localOccurrenceFour_of_certificates G marked ownerMap cert)

end OwnerLocalFourCertificate

#print axioms FourPortIncidence.portGraph_isBipartiteWith
#print axioms FourPortIncidence.card_edges_portGraph
#print axioms FourPortIncidence.three_mul_card_le_card_of_isPlanar
#print axioms ComponentPorts.card_ports_le_neighborComponentSum
#print axioms localOccurrenceAt_of_certificates
#print axioms OwnerLocalFourCertificate.localOccurrenceFour_of_certificates
#print axioms OwnerLocalFourCertificate.planar_twoConnected_markedSet_bound_of_certificates

end PlaneTopology.Faces.FourContactLocalOccurrence
