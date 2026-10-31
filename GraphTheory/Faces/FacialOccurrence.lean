import GraphTheory.Faces.FourContactLocalOcc

/-!
# Facial occurrences and iterated vertex deletion

This file isolates the part of the LOCAL-OCC topological bridge which does not
need a Jordan-curve argument.

* A face based at a dart is represented by the actual orbit list of the face
  permutation.  A `FacialOccurrence` remembers a dart occurrence whose source
  is a prescribed vertex; repeated visits of the same vertex therefore remain
  distinct when they use distinct darts.
* Every such occurrence has a canonical target vertex, hence a canonical
  connected component after deleting its source.
* Deleting `d` and then the surviving copy of `c` is graph-isomorphic to
  deleting the unordered pair `{d,c}` in one step.  Thus the component count
  used by the facial argument is definitionally connected to the concrete
  `PairDeletion.edgeComponentCount` from the four-contact ledger.

The only deliberately exposed hypothesis is injectivity of the map from facial
occurrences to components.  Proving that injectivity is precisely the faithful
plane-disk separation lemma; no rotation-system-only substitute is assumed.
-/

namespace PlaneTopology.Faces.FacialOccurrence

open SimpleGraph

/-! ## 1. Face-orbit lists and occurrences -/

namespace FaceBoundary

variable {V : Type*} {G : SimpleGraph V}

/-- Darts on the face containing `base`, kept as a subtype so that a face
corner is a concrete occurrence rather than only its source vertex. -/
def FaceCorner (r : G.RotationSystem) (base : G.Dart) :=
  {e : G.Dart // r.SameFace base e}

/-- Boundary darts in cyclic order, starting at `base`.  Face permutations of
simple graphs have no fixed points, so this list is never empty. -/
def faceDarts [Fintype G.Dart] [DecidableEq G.Dart]
    (r : G.RotationSystem) (base : G.Dart) : List G.Dart :=
  r.facePerm.toList base

theorem mem_faceDarts_iff
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : G.RotationSystem) (base e : G.Dart) :
    e ∈ faceDarts r base ↔ r.SameFace base e := by
  rw [faceDarts, Equiv.Perm.mem_toList_iff]
  exact and_iff_left (Equiv.Perm.mem_support.mpr (r.facePerm_ne_self base))

theorem faceDarts_nodup
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : G.RotationSystem) (base : G.Dart) :
    (faceDarts r base).Nodup :=
  Equiv.Perm.nodup_toList _ _

theorem faceDarts_ne_nil
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : G.RotationSystem) (base : G.Dart) :
    faceDarts r base ≠ [] := by
  intro hnil
  have hnot : base ∉ r.facePerm.support :=
    Equiv.Perm.toList_eq_nil_iff.mp hnil
  exact hnot (Equiv.Perm.mem_support.mpr (r.facePerm_ne_self base))

theorem faceDarts_isRotated_of_sameFace
    [Fintype G.Dart] [DecidableEq G.Dart]
    (r : G.RotationSystem) {base base' : G.Dart}
    (h : r.SameFace base base') :
    faceDarts r base ~r faceDarts r base' :=
  Equiv.Perm.SameCycle.toList_isRotated h

/-- Change the base dart of a face without changing any of its concrete dart
occurrences. -/
def faceCornerEquivOfSameFace
    (r : G.RotationSystem) {base base' : G.Dart}
    (h : r.SameFace base base') :
    FaceCorner r base ≃ FaceCorner r base' where
  toFun := fun q =>
    ⟨q.1, r.sameFace_equivalence.trans
      (r.sameFace_equivalence.symm h) q.2⟩
  invFun := fun q =>
    ⟨q.1, r.sameFace_equivalence.trans h q.2⟩
  left_inv := by
    intro q
    exact Subtype.ext rfl
  right_inv := by
    intro q
    exact Subtype.ext rfl

/-- Occurrences of the vertex `c` on the chosen face.  Two visits to `c` are
different exactly when their outgoing face darts are different. -/
def FacialOccurrence (r : G.RotationSystem) (base : G.Dart) (c : V) :=
  {q : FaceCorner r base // q.1.fst = c}

/-- Facial occurrences are independent, up to equivalence, of the dart chosen
as the start of the same face. -/
def facialOccurrenceEquivOfSameFace
    (r : G.RotationSystem) {base base' : G.Dart}
    (h : r.SameFace base base') (c : V) :
    FacialOccurrence r base c ≃ FacialOccurrence r base' c where
  toFun := fun q => ⟨faceCornerEquivOfSameFace r h q.1, q.2⟩
  invFun := fun q => ⟨(faceCornerEquivOfSameFace r h).symm q.1, q.2⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl

end FaceBoundary

/-! ## 2. The canonical component selected by an occurrence -/

namespace ComponentMap

open FaceBoundary

variable {V : Type*}

/-- Vertex type left after deleting one named vertex. -/
abbrev Away (V : Type*) (c : V) := {v : V // v ≠ c}

/-- The graph induced away from one named vertex. -/
def induceAway (K : SimpleGraph V) (c : V) : SimpleGraph (Away V c) :=
  K.induce {v | v ≠ c}

/-- The target of a dart occurrence survives deletion of its source. -/
def occurrenceTargetAway
    {K : SimpleGraph V} {r : K.RotationSystem} {base : K.Dart} {c : V}
    (q : FacialOccurrence r base c) : Away V c :=
  ⟨q.1.1.snd, by
    intro hsnd
    exact q.1.1.fst_ne_snd (q.2.trans hsnd.symm)⟩

/-- Canonical connected component reached immediately after an occurrence of
`c` on the facial boundary, in the graph with `c` deleted. -/
noncomputable def componentAfterDelete
    {K : SimpleGraph V} {r : K.RotationSystem} {base : K.Dart} {c : V}
    (q : FacialOccurrence r base c) :
    (induceAway K c).ConnectedComponent :=
  (induceAway K c).connectedComponentMk (occurrenceTargetAway q)

/-- Once distinct facial occurrences are known to select distinct components,
their number is bounded by the actual component count. -/
theorem card_facialOccurrence_le_components
    [Fintype V]
    {K : SimpleGraph V} {r : K.RotationSystem} {base : K.Dart} {c : V}
    (hinj : Function.Injective
      (componentAfterDelete (K := K) (r := r) (base := base) (c := c))) :
    Nat.card (FacialOccurrence r base c) ≤
      Nat.card (induceAway K c).ConnectedComponent :=
  Nat.card_le_card_of_injective _ hinj

end ComponentMap

/-! ## 3. Iterated deletion equals unordered-pair deletion -/

namespace IteratedDeletion

open ComponentMap
open PlaneTopology.Faces.FourContactLedger.PairDeletion

variable {V : Type*}

/-- The copy of `c` which survives the first deletion of `d`. -/
def awayVertex (d c : V) (hcd : c ≠ d) : Away V d :=
  ⟨c, hcd⟩

/-- The two nested subtype layers from successive deletion are equivalent to
the one subtype layer used for deletion of the unordered pair. -/
noncomputable def iteratedAwayEquivPairDeletion
    [DecidableEq V] (d c : V) (hcd : c ≠ d) :
    Away (Away V d) (awayVertex d c hcd) ≃
      {v : V // v ∈ (deletedSet s(d, c))ᶜ} where
  toFun := fun z => by
    have hneD : z.1.1 ≠ d := z.1.2
    have hneC : z.1.1 ≠ c := by
      intro heq
      apply z.2
      apply Subtype.ext
      exact heq
    refine ⟨z.1.1, ?_⟩
    show z.1.1 ∉ deletedSet s(d, c)
    intro hmem
    have hp : z.1.1 = d ∨ z.1.1 = c :=
      Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hmem)
    exact hp.elim hneD hneC
  invFun := fun x => by
    have hnot : x.1 ∉ deletedSet s(d, c) := x.2
    have hneD : x.1 ≠ d := by
      intro heq
      apply hnot
      exact Sym2.mem_toFinset.mpr (Sym2.mem_iff.mpr (Or.inl heq))
    have hneC : x.1 ≠ c := by
      intro heq
      apply hnot
      exact Sym2.mem_toFinset.mpr (Sym2.mem_iff.mpr (Or.inr heq))
    let y : Away V d := ⟨x.1, hneD⟩
    refine ⟨y, ?_⟩
    intro hy
    apply hneC
    exact congrArg Subtype.val hy
  left_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- Successive induced deletion and one-step pair deletion have exactly the
same vertices and adjacency, modulo the preceding subtype equivalence. -/
noncomputable def induceAwayInduceAwayIsoPairDeletion
    [DecidableEq V] (K : SimpleGraph V) (d c : V) (hcd : c ≠ d) :
    induceAway (induceAway K d) (awayVertex d c hcd) ≃g
      edgeGraph K s(d, c) where
  toEquiv := iteratedAwayEquivPairDeletion d c hcd
  map_rel_iff' := by
    intro x y
    rfl

/-- The graph isomorphism transports connected components bijectively. -/
noncomputable def iteratedComponentEquivPairDeletion
    [DecidableEq V] (K : SimpleGraph V) (d c : V) (hcd : c ≠ d) :
    (induceAway (induceAway K d) (awayVertex d c hcd)).ConnectedComponent ≃
      (edgeGraph K s(d, c)).ConnectedComponent :=
  (induceAwayInduceAwayIsoPairDeletion K d c hcd).connectedComponentEquiv

/-- Consequently the successive-deletion component count is literally the
ledger's concrete pair-deletion count. -/
theorem natCard_iteratedComponents_eq_pairDeletion
    [DecidableEq V] (K : SimpleGraph V) (d c : V) (hcd : c ≠ d) :
    Nat.card
        (induceAway (induceAway K d) (awayVertex d c hcd)).ConnectedComponent =
      edgeComponentCount K s(d, c) := by
  unfold edgeComponentCount
  exact Nat.card_congr (iteratedComponentEquivPairDeletion K d c hcd)

/-- Core reduction for LOCAL-OCC: an injective separation of occurrences on a
face of `K-d` gives the required bound by components of `K-{d,c}`. -/
theorem card_facialOccurrence_le_pairDeletion
    [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (d c : V) (hcd : c ≠ d)
    (r : (induceAway K d).RotationSystem)
    (base : (induceAway K d).Dart)
    (hinj : Function.Injective
      (ComponentMap.componentAfterDelete
        (K := induceAway K d) (r := r) (base := base)
        (c := awayVertex d c hcd))) :
    Nat.card (FaceBoundary.FacialOccurrence r base (awayVertex d c hcd)) ≤
      edgeComponentCount K s(d, c) := by
  calc
    Nat.card (FaceBoundary.FacialOccurrence r base (awayVertex d c hcd)) ≤
        Nat.card
          (induceAway (induceAway K d) (awayVertex d c hcd)).ConnectedComponent :=
      ComponentMap.card_facialOccurrence_le_components hinj
    _ = edgeComponentCount K s(d, c) :=
      natCard_iteratedComponents_eq_pairDeletion K d c hcd

end IteratedDeletion

/-! ## 4. Facial ports produce the ledger's component certificates -/

namespace FacialPorts

open FaceBoundary ComponentMap IteratedDeletion
open PlaneTopology.Faces.FourContactLocalOccurrence

variable {V : Type*}

/-- A finite port is realized by a concrete corner of one face of `G-d`.
Injectivity of `corner` is important: distinct ports are distinct dart
occurrences even if their centre vertex occurs several times on the face. -/
structure FacialPortData
    [DecidableEq V] (G : SimpleGraph V) (d : V)
    (r : (induceAway G d).RotationSystem)
    (base : (induceAway G d).Dart) (P : Type*) where
  corner : P ↪ FaceCorner r base
  center_adj : ∀ p, G.Adj d (corner p).1.fst.1

namespace FacialPortData

variable {P : Type*} [DecidableEq V] {G : SimpleGraph V} {d : V}
  {r : (induceAway G d).RotationSystem}
  {base : (induceAway G d).Dart}
  (S : FacialPortData G d r base P)

/-- Ambient vertex at which a facial port is centred. -/
def center (p : P) : V :=
  (S.corner p).1.fst.1

theorem center_isAdjacent (p : P) : G.Adj d (S.center p) :=
  S.center_adj p

/-- Restricting ports to one centre embeds them into the corresponding type of
facial occurrences. -/
noncomputable def portOccurrenceEmbedding (c : V) (hadj : G.Adj d c) :
    {p : P // S.center p = c} ↪
      FacialOccurrence r base (awayVertex d c hadj.ne.symm) where
  toFun := fun p => by
    refine ⟨S.corner p.1, ?_⟩
    apply Subtype.ext
    exact p.2
  inj' := by
    intro p q hpq
    apply Subtype.ext
    apply S.corner.injective
    exact congrArg Subtype.val hpq

/-- If the plane-disk separation map is injective at `c`, then the ports at
`c` inject into the ledger's actual components of `G-{d,c}`. -/
noncomputable def portComponentEmbedding
    (c : V) (hadj : G.Adj d c)
    (hsep : Function.Injective
      (ComponentMap.componentAfterDelete
        (K := induceAway G d) (r := r) (base := base)
        (c := awayVertex d c hadj.ne.symm))) :
    {p : P // S.center p = c} ↪
      (PlaneTopology.Faces.FourContactLedger.PairDeletion.edgeGraph G s(d, c)).ConnectedComponent where
  toFun := fun p =>
    iteratedComponentEquivPairDeletion G d c hadj.ne.symm
      (ComponentMap.componentAfterDelete (S.portOccurrenceEmbedding c hadj p))
  inj' := by
    intro p q hpq
    apply (S.portOccurrenceEmbedding c hadj).injective
    apply hsep
    apply (iteratedComponentEquivPairDeletion G d c hadj.ne.symm).injective
    exact hpq

/-- The facial realization and the single geometric separation obligation
assemble the exact `ComponentPortCertificate` consumed by LOCAL-OCC. -/
noncomputable def componentPortCertificate
    [Fintype V] [Fintype P]
    (hsep : ∀ (c : V) (hadj : G.Adj d c), Function.Injective
      (ComponentMap.componentAfterDelete
        (K := induceAway G d) (r := r) (base := base)
        (c := awayVertex d c hadj.ne.symm))) :
    ComponentPorts.ComponentPortCertificate G d P where
  center := S.center
  center_adj := S.center_adj
  componentEmbedding := fun c hadj =>
    S.portComponentEmbedding c hadj (hsep c hadj)

end FacialPortData

/-- Four ports per marked object, together with a faithful realization of every
port as a distinct dart occurrence on one face of `G-d`. -/
structure FacialFourPortSystem
    [DecidableEq V] (G : SimpleGraph V) (d : V)
    (r : (induceAway G d).RotationSystem)
    (base : (induceAway G d).Dart) (X P : Type*) where
  incidence : FourPortIncidence X P
  facial : FacialPortData G d r base P

/-- LOCAL-OCC now exposes exactly its two genuinely geometric inputs:
planarity of the concrete port graph and injectivity of facial separation.
All component bookkeeping is derived. -/
theorem localOccurrenceAt_of_facialFourPorts
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V)
    [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P]
    (r : (induceAway G d).RotationSystem)
    (base : (induceAway G d).Dart)
    (S : FacialFourPortSystem G d r base X P)
    (hplanar : S.incidence.portGraph.IsPlanar)
    (hsep : ∀ (c : V) (hadj : G.Adj d c), Function.Injective
      (ComponentMap.componentAfterDelete
        (K := induceAway G d) (r := r) (base := base)
        (c := awayVertex d c hadj.ne.symm))) :
    3 * Fintype.card X ≤
      PlaneTopology.Faces.FourContactLedger.GraphLedger.neighborComponentSum G d := by
  exact localOccurrenceAt_of_certificates G d S.incidence hplanar
    (S.facial.componentPortCertificate hsep)

end FacialPorts

#print axioms FaceBoundary.mem_faceDarts_iff
#print axioms FaceBoundary.faceDarts_nodup
#print axioms ComponentMap.card_facialOccurrence_le_components
#print axioms IteratedDeletion.induceAwayInduceAwayIsoPairDeletion
#print axioms IteratedDeletion.card_facialOccurrence_le_pairDeletion
#print axioms FacialPorts.localOccurrenceAt_of_facialFourPorts

end PlaneTopology.Faces.FacialOccurrence
