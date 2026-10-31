import GraphTheory.Faces.FaithfulPlaneMap

/-!
# Face-boundary algebra over `ZMod 2`

For a faithful finite rotation map, a face chain assigns a bit to every actual
face-permutation cycle.  Its boundary assigns to an edge the sum of the bits
on its two dart sides.  This file proves the first half of the algebraic
separation route: on a connected faithful map, a face chain has zero boundary
exactly when it is constant.  In particular the kernel has dimension one.
-/

namespace PlaneTopology.Faces.FaceBoundaryAlgebra

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra

open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## 1. The boundary linear map -/

/-- A face chain is a `ZMod 2` coefficient on each actual face cycle. -/
abbrev FaceChain (r : G.RotationSystem) := FaceIndex r → ZMod 2

/-- Choose one of the two orientations of an undirected graph edge.  All
subsequent definitions are symmetric under dart reversal. -/
noncomputable def dartOfEdge (e : G.edgeFinset) : G.Dart := by
  let p : V × V := e.1.out
  have hedge : e.1 ∈ G.edgeSet := G.mem_edgeFinset.mp e.2
  have hp : s(p.1, p.2) ∈ G.edgeSet := by
    simpa [p, Sym2.mk] using (e.1.out_eq ▸ hedge)
  exact ⟨p, hp⟩

omit [DecidableEq V] in
theorem dartOfEdge_edge (e : G.edgeFinset) :
    (dartOfEdge e).edge = e.1 := by
  unfold dartOfEdge
  simp only [SimpleGraph.Dart.edge_mk]
  exact e.1.out_eq

/-- Boundary of a face chain: an edge sees the sum of the coefficients of its
two oriented sides. -/
noncomputable def faceBoundary (r : G.RotationSystem) :
    FaceChain r →ₗ[ZMod 2] EdgeSpace G where
  toFun a e :=
    a (faceIndex r (dartOfEdge e)) +
      a (faceIndex r (dartOfEdge e).symm)
  map_add' := by
    intro a b
    funext e
    simp only [Pi.add_apply]
    abel
  map_smul' := by
    intro z a
    funext e
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (mul_add z _ _).symm

@[simp]
theorem faceBoundary_apply (r : G.RotationSystem)
    (a : FaceChain r) (e : G.edgeFinset) :
    faceBoundary r a e =
      a (faceIndex r (dartOfEdge e)) +
        a (faceIndex r (dartOfEdge e).symm) :=
  rfl

/-- The boundary does not depend on which orientation of an edge is chosen. -/
theorem faceBoundary_eq_dart_sum (r : G.RotationSystem)
    (a : FaceChain r) (d : G.Dart) :
    faceBoundary r a ⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ =
      a (faceIndex r d) + a (faceIndex r d.symm) := by
  rw [faceBoundary_apply]
  have hedge := dartOfEdge_edge
    (⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ : G.edgeFinset)
  have horient :
      dartOfEdge (⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ : G.edgeFinset) = d ∨
        dartOfEdge (⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ : G.edgeFinset) = d.symm :=
    (SimpleGraph.dart_edge_eq_iff _ _).mp hedge
  rcases horient with h | h
  · rw [h]
  · rw [h, SimpleGraph.Dart.symm_symm, add_comm]

/-- A constant face chain has zero boundary in characteristic two. -/
theorem faceBoundary_const (r : G.RotationSystem) (z : ZMod 2) :
    faceBoundary r (fun _ => z) = 0 := by
  funext e
  simp [faceBoundary, ZModModule.add_self]

/-! ## 2. Reindexing incident edges by outgoing darts -/

/-- An outgoing dart based at `v` is the same finite datum as a neighbour of
`v`.  We keep the equality of sources in the type because this is the form
preserved by a rotation system. -/
def outDartEquivNeighborSet (v : V) :
    ↥(outDartsAt G v) ≃ G.neighborSet v where
  toFun d := ⟨d.1.snd, by
    change G.Adj v d.1.snd
    have hd : d.1.fst = v := d.2
    exact (G.adj_congr_of_sym2
      (congrArg (fun x => s(x, d.1.snd)) hd)).mp d.1.adj⟩
  invFun w := ⟨G.dartOfNeighborSet v w, rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact d.2.symm
    · rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- Edges of `edgeFinset` incident with `v` are canonically the subtype of
the graph's incidence set at `v`. -/
def incidentEdgeEquivIncidenceSet (v : V) :
    {e : G.edgeFinset // v ∈ (e.1 : Sym2 V)} ≃ G.incidenceSet v where
  toFun e := ⟨e.1.1, G.mem_edgeFinset.mp e.1.2, e.2⟩
  invFun e := ⟨⟨e.1, G.mem_edgeFinset.mpr e.2.1⟩, e.2.2⟩
  left_inv e := by
    rfl
  right_inv e := by
    rfl

/-- Reindex the edges incident with `v` by their unique orientation whose
source is `v`. -/
def outDartEquivIncidentEdge (v : V) :
    ↥(outDartsAt G v) ≃ {e : G.edgeFinset // v ∈ (e.1 : Sym2 V)} :=
  (outDartEquivNeighborSet (G := G) v).trans
    ((G.incidenceSetEquivNeighborSet v).symm.trans
      (incidentEdgeEquivIncidenceSet (G := G) v).symm)

theorem outDartEquivIncidentEdge_val (v : V) (d : ↥(outDartsAt G v)) :
    ((outDartEquivIncidentEdge (G := G) v d).1 : Sym2 V) = d.1.edge := by
  change s(v, d.1.snd) = s(d.1.fst, d.1.snd)
  rw [d.2]

theorem faceBoundary_outDartEquivIncidentEdge
    (r : G.RotationSystem) (a : FaceChain r) (v : V)
    (d : ↥(outDartsAt G v)) :
    faceBoundary r a (outDartEquivIncidentEdge (G := G) v d).1 =
      a (faceIndex r d.1) + a (faceIndex r d.1.symm) := by
  have hedge :
      (outDartEquivIncidentEdge (G := G) v d).1 =
        (⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ : G.edgeFinset) := by
    apply Subtype.ext
    exact outDartEquivIncidentEdge_val (G := G) v d
  rw [hedge, faceBoundary_eq_dart_sum]

/-- The vertex permutation restricted to one source fibre. -/
noncomputable def sigmaOutDartEquiv (r : G.RotationSystem) (v : V) :
    ↥(outDartsAt G v) ≃ ↥(outDartsAt G v) :=
  Set.BijOn.equiv r.σ (RotationSystem.sigma_bijOn_outDartsAt r v)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem sigmaOutDartEquiv_apply (r : G.RotationSystem) (v : V)
    (d : ↥(outDartsAt G v)) :
    (sigmaOutDartEquiv r v d).1 = r.σ d.1 :=
  rfl

/-! ## 3. Zero boundary forces equal coefficients -/

/-- The two sides of every edge have equal coefficients in a zero-boundary
face chain. -/
theorem eq_symm_of_mem_ker (r : G.RotationSystem)
    {a : FaceChain r} (ha : a ∈ LinearMap.ker (faceBoundary r))
    (d : G.Dart) :
    a (faceIndex r d) = a (faceIndex r d.symm) := by
  rw [LinearMap.mem_ker] at ha
  have hz := congrFun ha
    (⟨d.edge, G.mem_edgeFinset.mpr d.edge_mem⟩ : G.edgeFinset)
  rw [Pi.zero_apply, faceBoundary_eq_dart_sum] at hz
  have hneg : a (faceIndex r d) = -a (faceIndex r d.symm) :=
    eq_neg_of_add_eq_zero_left hz
  simpa only [ZMod.neg_eq_self_mod_two] using hneg

/-- Moving one step in the vertex rotation preserves a zero-boundary face
coefficient. -/
theorem eq_sigma_of_mem_ker (r : G.RotationSystem)
    {a : FaceChain r} (ha : a ∈ LinearMap.ker (faceBoundary r))
    (d : G.Dart) :
    a (faceIndex r (r.σ d)) = a (faceIndex r d) := by
  calc
    a (faceIndex r (r.σ d)) = a (faceIndex r d.symm) := by
      rw [faceIndex_sigma_eq_symm]
    _ = a (faceIndex r d) := (eq_symm_of_mem_ker r ha d).symm

/-- A zero-boundary coefficient is invariant under every natural power of the
vertex permutation. -/
theorem eq_sigma_pow_of_mem_ker (r : G.RotationSystem)
    {a : FaceChain r} (ha : a ∈ LinearMap.ker (faceBoundary r))
    (d : G.Dart) (n : ℕ) :
    a (faceIndex r ((r.σ ^ n) d)) = a (faceIndex r d) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (eq_sigma_of_mem_ker r ha ((r.σ ^ n) d)).trans ih

/-- Vertex faithfulness makes all face corners at the same source carry the
same coefficient when the boundary vanishes. -/
theorem eq_of_same_source_of_mem_ker
    (R : FaithfulRotationSystem G)
    {a : FaceChain R.toRotationSystem}
    (ha : a ∈ LinearMap.ker (faceBoundary R.toRotationSystem))
    (d e : G.Dart) (hsource : d.fst = e.fst) :
    a (faceIndex R.toRotationSystem d) =
      a (faceIndex R.toRotationSystem e) := by
  obtain ⟨n, hn⟩ := (R.sameCycle_at_source hsource).exists_nat_pow_eq
  rw [← hn]
  exact (eq_sigma_pow_of_mem_ker R.toRotationSystem ha d n).symm

/-- Equality propagates along a graph walk, using vertex rotation within a
source fibre and zero boundary across each traversed edge. -/
theorem eq_of_walk_of_mem_ker
    (R : FaithfulRotationSystem G)
    {a : FaceChain R.toRotationSystem}
    (ha : a ∈ LinearMap.ker (faceBoundary R.toRotationSystem))
    {u v : V} (p : G.Walk u v)
    (d e : G.Dart) (hd : d.fst = u) (he : e.fst = v) :
    a (faceIndex R.toRotationSystem d) =
      a (faceIndex R.toRotationSystem e) := by
  induction p generalizing d with
  | nil =>
      exact eq_of_same_source_of_mem_ker R ha d e (hd.trans he.symm)
  | @cons u w v huw p ih =>
      let step : G.Dart := ⟨(u, w), huw⟩
      calc
        a (faceIndex R.toRotationSystem d) =
            a (faceIndex R.toRotationSystem step) :=
          eq_of_same_source_of_mem_ker R ha d step hd
        _ = a (faceIndex R.toRotationSystem step.symm) :=
          eq_symm_of_mem_ker R.toRotationSystem ha step
        _ = a (faceIndex R.toRotationSystem e) :=
          ih step.symm rfl he

/-- On a connected faithful map, a zero-boundary face chain takes the same
value on the face indices of any two darts. -/
theorem eq_on_darts_of_mem_ker
    (M : ConnectedCellularMap G)
    {a : FaceChain M.rotation.toRotationSystem}
    (ha : a ∈ LinearMap.ker (faceBoundary M.rotation.toRotationSystem))
    (d e : G.Dart) :
    a (faceIndex M.rotation.toRotationSystem d) =
      a (faceIndex M.rotation.toRotationSystem e) := by
  let p : G.Walk d.fst e.fst :=
    Classical.choice (M.connected d.fst e.fst)
  exact eq_of_walk_of_mem_ker M.rotation ha p d e rfl rfl

/-- Equivalently, every zero-boundary face chain is constant on all face
cycles. -/
theorem eq_on_faces_of_mem_ker
    (M : ConnectedCellularMap G)
    {a : FaceChain M.rotation.toRotationSystem}
    (ha : a ∈ LinearMap.ker (faceBoundary M.rotation.toRotationSystem))
    (F H : FaceIndex M.rotation.toRotationSystem) :
    a F = a H := by
  rw [← faceIndex_representative M.rotation.toRotationSystem F,
    ← faceIndex_representative M.rotation.toRotationSystem H]
  exact eq_on_darts_of_mem_ker M ha _ _

/-! ## 4. Exact kernel dimension -/

/-- The kernel of the face-boundary map of a connected edgeful faithful map
has dimension one: its elements are exactly the two constant face chains. -/
theorem finrank_ker_faceBoundary_eq_one
    (M : ConnectedCellularMap G) :
    Module.finrank (ZMod 2)
      (LinearMap.ker (faceBoundary M.rotation.toRotationSystem)) = 1 := by
  let d0 : G.Dart := Classical.choice M.dartNonempty
  let F0 : FaceIndex M.rotation.toRotationSystem :=
    faceIndex M.rotation.toRotationSystem d0
  let E : LinearMap.ker (faceBoundary M.rotation.toRotationSystem) ≃ₗ[ZMod 2]
      ZMod 2 :=
    { toFun := fun a => a.1 F0
      invFun := fun z => ⟨fun _ => z,
        faceBoundary_const M.rotation.toRotationSystem z⟩
      left_inv := by
        intro a
        apply Subtype.ext
        funext F
        exact (eq_on_faces_of_mem_ker M a.2 F F0).symm
      right_inv := by
        intro z
        rfl
      map_add' := by
        intro a b
        rfl
      map_smul' := by
        intro z a
        rfl }
  rw [LinearEquiv.finrank_eq E]
  simp

/-! ## 5. Face boundaries are graph cycles -/

/-- The incidence boundary of a face boundary vanishes at every vertex. -/
theorem graphBoundary_faceBoundary_apply (r : G.RotationSystem)
    (a : FaceChain r) (v : V) :
    G.boundary (faceBoundary r a) v = 0 := by
  classical
  unfold SimpleGraph.boundary
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    SimpleGraph.incidenceMatrix, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp only [Finset.subtype_univ]
  rw [← (outDartEquivIncidentEdge (G := G) v).sum_comp]
  simp_rw [faceBoundary_outDartEquivIncidentEdge]
  simp_rw [← faceIndex_sigma_eq_symm]
  rw [Finset.sum_add_distrib]
  have hsigma :
      (∑ d : ↥(outDartsAt G v),
          a (faceIndex r (r.σ d.1))) =
        ∑ d : ↥(outDartsAt G v), a (faceIndex r d.1) := by
    simpa using (sigmaOutDartEquiv r v).sum_comp
      (fun d : ↥(outDartsAt G v) => a (faceIndex r d.1))
  rw [hsigma]
  exact ZModModule.add_self _

/-- Every face boundary is a cycle-space vector. -/
theorem faceBoundary_mem_cycleSpace (r : G.RotationSystem)
    (a : FaceChain r) :
    faceBoundary r a ∈ G.CycleSpace := by
  change G.boundary (faceBoundary r a) = 0
  funext v
  exact graphBoundary_faceBoundary_apply r a v

/-- Hence the entire range of the face-boundary operator lies in the graph's
cycle space. -/
theorem range_faceBoundary_le_cycleSpace (r : G.RotationSystem) :
    LinearMap.range (faceBoundary r) ≤ G.CycleSpace := by
  rintro _ ⟨a, rfl⟩
  exact faceBoundary_mem_cycleSpace r a

/-! ## 6. Exact plane duality by dimensions -/

/-- For a connected plane map, rank-nullity for face boundaries and Euler's
equation give exactly the dimension of the graph cycle space. -/
theorem finrank_range_faceBoundary_eq_cycleSpace
    (M : ConnectedPlaneMap G) :
    Module.finrank (ZMod 2)
        (LinearMap.range (faceBoundary M.rawRotation)) =
      Module.finrank (ZMod 2) G.CycleSpace := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrankNull :=
    LinearMap.finrank_range_add_finrank_ker (faceBoundary M.rawRotation)
  have hdomain :
      Module.finrank (ZMod 2) (FaceChain M.rawRotation) =
        Fintype.card (FaceIndex M.rawRotation) := by
    exact Module.finrank_pi (ZMod 2)
  have hker :
      Module.finrank (ZMod 2)
          (LinearMap.ker (faceBoundary M.rawRotation)) = 1 := by
    exact finrank_ker_faceBoundary_eq_one M.toConnectedCellularMap
  rw [hdomain, hker, card_faceIndex_eq_numFaces] at hrankNull
  have hcycle :=
    G.finrank_cycleSpace_eq_edges_add_one_sub_vertices M.connected
  have heuler := M.euler
  change Fintype.card V + M.rawRotation.numFaces =
    G.edgeFinset.card + 2 at heuler
  omega

/-- The facial boundaries span *all* graph cycles for a supplied connected
plane map.  This is the algebraic sphere-duality theorem needed by the
separation argument. -/
theorem range_faceBoundary_eq_cycleSpace (M : ConnectedPlaneMap G) :
    LinearMap.range (faceBoundary M.rawRotation) = G.CycleSpace :=
  Submodule.eq_of_le_of_finrank_eq
    (range_faceBoundary_le_cycleSpace M.rawRotation)
    (finrank_range_faceBoundary_eq_cycleSpace M)

#print axioms eq_on_faces_of_mem_ker
#print axioms finrank_ker_faceBoundary_eq_one
#print axioms range_faceBoundary_le_cycleSpace
#print axioms range_faceBoundary_eq_cycleSpace

end PlaneTopology.Faces.FaceBoundaryAlgebra
