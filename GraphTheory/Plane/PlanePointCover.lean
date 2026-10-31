import GraphTheory.Plane.PlaneVertexGluingCover

/-! # Actual plane-map gluing for ambient sets meeting in one vertex -/

namespace PlaneTopology.PlanePointCover

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneVertexGluingGraph PlaneTopology.PlaneVertexGluingCover

variable {V : Type*} [DecidableEq V]

/-- Private vertices of one side after its common point is removed. -/
abbrev Private (S : Set V) (v : V) (hv : v ∈ S) := {w : S // w ≠ ⟨v, hv⟩}

/-- Put the common point first in the side's exact vertex type. -/
def sideEquiv (S : Set V) (v : V) (hv : v ∈ S) : Option (Private S v hv) ≃ S :=
  Equiv.optionSubtypeNe (⟨v, hv⟩ : S)

/-- The exact side embedding into the original ambient vertex set. -/
def sideEmbedding (S : Set V) (v : V) (hv : v ∈ S) : Option (Private S v hv) ↪ V :=
  (sideEquiv S v hv).toEmbedding.trans (Function.Embedding.subtype (· ∈ S))

/-- Reparametrize an arbitrary side graph, without changing any edge. -/
def sideGraph (S : Set V) (v : V) (hv : v ∈ S) (L : SimpleGraph S) :
    SimpleGraph (Option (Private S v hv)) := L.comap (sideEquiv S v hv).toEmbedding

/-- Decidable adjacency of the explicitly reparametrized side graph. -/
instance sideGraphDecidableRel (S : Set V) (v : V) (hv : v ∈ S) (L : SimpleGraph S)
    [DecidableRel L.Adj] : DecidableRel (sideGraph S v hv L).Adj := by
  intro x y
  change Decidable (L.Adj (sideEquiv S v hv x) (sideEquiv S v hv y))
  infer_instance

/-- The exact ambient union of the two side graphs. -/
def coverGraph {S T : Set V} (L : SimpleGraph S) (R : SimpleGraph T) : SimpleGraph V :=
  L.map (Function.Embedding.subtype (· ∈ S)) ⊔ R.map (Function.Embedding.subtype (· ∈ T))

/-- The canonical point-gluing graph is exactly the ambient union of graphs
on any two covering sets whose intersection is one specified vertex. -/
noncomputable def coverIso (S T : Set V) (v : V) (hvS : v ∈ S) (hvT : v ∈ T)
    (hcover : S ∪ T = Set.univ) (hmeet : S ∩ T = {v})
    (L : SimpleGraph S) (R : SimpleGraph T) :
    gluedGraph (sideGraph S v hvS L) (sideGraph T v hvT R) ≃g coverGraph L R := by
  let f := sideEmbedding S v hvS
  let g := sideEmbedding T v hvT
  have hfg : f none = g none := rfl
  have hm : ∀ a b, f a = g b → a = none ∧ b = none := by
    intro a b hab
    have hs : f a ∈ S := (sideEquiv S v hvS a).property
    have ht : f a ∈ T := hab.symm ▸ (sideEquiv T v hvT b).property
    have hp : f a ∈ S ∩ T := ⟨hs, ht⟩
    rw [hmeet] at hp
    have ha : f a = v := hp
    have hb : g b = v := hab.symm.trans ha
    exact ⟨(sideEquiv S v hvS).injective (Subtype.ext ha),
      (sideEquiv T v hvT).injective (Subtype.ext hb)⟩
  have hc : ∀ w, (∃ a, f a = w) ∨ ∃ b, g b = w := by
    intro w
    have hw : w ∈ S ∪ T := by rw [hcover]; trivial
    rcases hw with hw | hw
    · refine Or.inl ⟨(sideEquiv S v hvS).symm ⟨w, hw⟩, ?_⟩
      change ((sideEquiv S v hvS) ((sideEquiv S v hvS).symm ⟨w, hw⟩)).val = w
      rw [Equiv.apply_symm_apply]
    · refine Or.inr ⟨(sideEquiv T v hvT).symm ⟨w, hw⟩, ?_⟩
      change ((sideEquiv T v hvT) ((sideEquiv T v hvT).symm ⟨w, hw⟩)).val = w
      rw [Equiv.apply_symm_apply]
  have E := unionIso (sideGraph S v hvS L) (sideGraph T v hvT R) f g hfg hm hc
  have heq : imageUnion (sideGraph S v hvS L) (sideGraph T v hvT R) f g = coverGraph L R := by
    change (L.comap (sideEquiv S v hvS).toEmbedding).map
        ((sideEquiv S v hvS).toEmbedding.trans (Function.Embedding.subtype (· ∈ S))) ⊔
      (R.comap (sideEquiv T v hvT).toEmbedding).map
        ((sideEquiv T v hvT).toEmbedding.trans (Function.Embedding.subtype (· ∈ T))) = _
    rw [map_comap_equiv, map_comap_equiv]
    rfl
  rw [heq] at E
  exact E

/-- A singleton side has no private vertices. -/
instance privateIsEmpty (S : Set V) (v : V) (hv : v ∈ S) [Subsingleton S] :
    IsEmpty (Private S v hv) := ⟨fun x => x.property (Subsingleton.elim _ _)⟩

variable [Fintype V] (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
variable (L : SimpleGraph S) (R : SimpleGraph T) [DecidableRel L.Adj] [DecidableRel R.Adj]

instance coverGraphDecidableRel : DecidableRel (coverGraph L R).Adj := by
  intro x y
  unfold coverGraph
  infer_instance

/-- Glue arbitrary actual side maps on a singleton-intersection ambient cover. -/
noncomputable def coverPlaneMap (v : V) (hvS : v ∈ S) (hvT : v ∈ T)
    (hcover : S ∪ T = Set.univ) (hmeet : S ∩ T = {v})
    (M : ConnectedPlaneMap L) (N : ConnectedPlaneMap R) : ConnectedPlaneMap (coverGraph L R) := by
  let M' : ConnectedPlaneMap (sideGraph S v hvS L) := PlaneTopology.PlaneGeneralTransport.planeMap
    (SimpleGraph.Iso.comap (sideEquiv S v hvS) L).symm M
  let N' : ConnectedPlaneMap (sideGraph T v hvT R) := PlaneTopology.PlaneGeneralTransport.planeMap
    (SimpleGraph.Iso.comap (sideEquiv T v hvT) R).symm N
  exact PlaneTopology.PlaneGeneralTransport.planeMap (coverIso S T v hvS hvT hcover hmeet L R)
    (PlaneTopology.PlaneVertexGluing.gluedPlaneMap _ _ M' N')

/-- A singleton left side needs only the actual right-side map. -/
noncomputable def rightSingletonCoverPlaneMap [Subsingleton S]
    (v : V) (hvS : v ∈ S) (hvT : v ∈ T)
    (hcover : S ∪ T = Set.univ) (hmeet : S ∩ T = {v})
    (N : ConnectedPlaneMap R) : ConnectedPlaneMap (coverGraph L R) := by
  let N' : ConnectedPlaneMap (sideGraph T v hvT R) := PlaneTopology.PlaneGeneralTransport.planeMap
    (SimpleGraph.Iso.comap (sideEquiv T v hvT) R).symm N
  exact PlaneTopology.PlaneGeneralTransport.planeMap (coverIso S T v hvS hvT hcover hmeet L R)
    (PlaneTopology.PlaneVertexGluing.rightSingletonPlaneMap (sideGraph S v hvS L) (sideGraph T v hvT R) N')

/-- A singleton right side needs only the actual left-side map. -/
noncomputable def leftSingletonCoverPlaneMap [Subsingleton T]
    (v : V) (hvS : v ∈ S) (hvT : v ∈ T)
    (hcover : S ∪ T = Set.univ) (hmeet : S ∩ T = {v})
    (M : ConnectedPlaneMap L) : ConnectedPlaneMap (coverGraph L R) := by
  let M' : ConnectedPlaneMap (sideGraph S v hvS L) := PlaneTopology.PlaneGeneralTransport.planeMap
    (SimpleGraph.Iso.comap (sideEquiv S v hvS) L).symm M
  exact PlaneTopology.PlaneGeneralTransport.planeMap (coverIso S T v hvS hvT hcover hmeet L R)
    (PlaneTopology.PlaneVertexGluing.leftSingletonPlaneMap (sideGraph S v hvS L) (sideGraph T v hvT R) M')

end PlaneTopology.PlanePointCover

#print axioms PlaneTopology.PlanePointCover.coverPlaneMap
#print axioms PlaneTopology.PlanePointCover.rightSingletonCoverPlaneMap
