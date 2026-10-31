/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Minor.Defs
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Antisymmetry of the finite graph-minor relation (Diestel §1.7)

The minor relation is a preorder on labelled graphs. On finite graphs it is
antisymmetric up to graph isomorphism: if each of `H` and `G` is a minor of the
other, then `H ≃g G`.

The proof uses representatives of the branch sets. Mutual minor models force
the two finite vertex types to have the same cardinality, hence each family of
branch-set representatives is a bijection. Every branch set is consequently
a singleton. Both minor models then give copies in opposite directions; their
edge-set embeddings force equality of the finite edge counts. The first copy,
transported along its vertex equivalence, is therefore the whole target graph.

## Main results

* `MinorModel.representative` chooses one vertex from every branch set.
* `MinorModel.toCopyOfRepresentativeBijective` turns a saturated finite minor
  model into a graph copy.
* `IsMinor.antisymm_iso` proves antisymmetry modulo graph isomorphism.

## References

* R. Diestel, *Graph Theory*, 5th ed., Proposition 1.7.3.
-/

namespace SimpleGraph

universe u v

namespace MinorModel

variable {VH : Type u} {VG : Type v} {H : SimpleGraph VH} {G : SimpleGraph VG}

/-- A chosen representative of each nonempty branch set of a minor model. -/
noncomputable def representative (m : MinorModel H G) (x : VH) : VG :=
  (m.nonempty x).choose

/-- The chosen representative belongs to its branch set. -/
theorem representative_mem (m : MinorModel H G) (x : VH) :
    m.representative x ∈ m.branchSet x :=
  (m.nonempty x).choose_spec

/-- Representatives of distinct branch sets are distinct. -/
theorem representative_injective (m : MinorModel H G) :
    Function.Injective m.representative := by
  intro x y hxy
  by_contra hne
  have hdisj := m.disjoint x y hne
  exact Set.disjoint_left.mp hdisj
    (by simpa [hxy] using m.representative_mem x)
    (m.representative_mem y)

/-- A finite minor cannot have more vertices than its host graph. -/
theorem natCard_le (m : MinorModel H G) [Finite VG] :
    Nat.card VH ≤ Nat.card VG :=
  Nat.card_le_card_of_injective m.representative m.representative_injective

/-- If the representative map is onto, every branch set is its representative singleton. -/
theorem mem_branchSet_eq_representative (m : MinorModel H G)
    (hsurj : Function.Surjective m.representative) {x : VH} {v : VG}
    (hv : v ∈ m.branchSet x) : v = m.representative x := by
  obtain ⟨y, rfl⟩ := hsurj v
  have hxy : x = y := by
    by_contra hne
    exact Set.disjoint_left.mp (m.disjoint x y hne) hv (m.representative_mem y)
  subst y
  rfl

/-- A minor model whose representatives exhaust the host vertices is a copy. -/
noncomputable def toCopyOfRepresentativeBijective (m : MinorModel H G)
    (hbij : Function.Bijective m.representative) : Copy H G where
  toHom :=
    { toFun := m.representative
      map_rel' := by
        intro x y hxy
        obtain ⟨a, ha, b, hb, hab⟩ := m.adjacent x y hxy
        simpa [m.mem_branchSet_eq_representative hbij.2 ha,
          m.mem_branchSet_eq_representative hbij.2 hb] using hab }
  injective' := hbij.1

end MinorModel

namespace IsMinor

variable {VH : Type u} {VG : Type v} {H : SimpleGraph VH} {G : SimpleGraph VG}

/-- **Diestel 1.7.3 (minor part).** On finite graphs, mutual minor containment
implies graph isomorphism. Thus the minor relation is antisymmetric after
identifying isomorphic finite graphs. -/
theorem antisymm_iso [Finite VH] [Finite VG]
    (hHG : H ≤m G) (hGH : G ≤m H) : Nonempty (H ≃g G) := by
  classical
  letI := Fintype.ofFinite VH
  letI := Fintype.ofFinite VG
  let mHG : MinorModel H G := hHG.some
  let mGH : MinorModel G H := hGH.some
  have hvertexHG : Fintype.card VH ≤ Fintype.card VG :=
    Fintype.card_le_of_injective mHG.representative mHG.representative_injective
  have hvertexGH : Fintype.card VG ≤ Fintype.card VH :=
    Fintype.card_le_of_injective mGH.representative mGH.representative_injective
  have hvertex : Fintype.card VH = Fintype.card VG :=
    Nat.le_antisymm hvertexHG hvertexGH
  have hbijHG : Function.Bijective mHG.representative :=
    (Fintype.bijective_iff_injective_and_card mHG.representative).2
      ⟨mHG.representative_injective, hvertex⟩
  have hbijGH : Function.Bijective mGH.representative :=
    (Fintype.bijective_iff_injective_and_card mGH.representative).2
      ⟨mGH.representative_injective, hvertex.symm⟩
  let cHG : Copy H G := mHG.toCopyOfRepresentativeBijective hbijHG
  let cGH : Copy G H := mGH.toCopyOfRepresentativeBijective hbijGH
  have hedgeHG : Fintype.card H.edgeSet ≤ Fintype.card G.edgeSet :=
    Fintype.card_le_of_injective cHG.mapEdgeSet cHG.mapEdgeSet.injective
  have hedgeGH : Fintype.card G.edgeSet ≤ Fintype.card H.edgeSet :=
    Fintype.card_le_of_injective cGH.mapEdgeSet cGH.mapEdgeSet.injective
  have hedge : H.edgeFinset.card = G.edgeFinset.card := by
    rw [edgeFinset_card, edgeFinset_card]
    exact Nat.le_antisymm hedgeHG hedgeGH
  let e : VH ≃ VG := Equiv.ofBijective mHG.representative hbijHG
  have hmap_le : H.map e.toEmbedding ≤ G := by
    rw [map_le_iff_le_comap]
    intro x y hxy
    exact cHG.toHom.map_rel hxy
  have hmap_card : (H.map e.toEmbedding).edgeFinset.card = G.edgeFinset.card := by
    rw [card_edgeFinset_map]
    exact hedge
  have hmap_eq : H.map e.toEmbedding = G := by
    rw [← edgeFinset_inj]
    exact Finset.eq_of_subset_of_card_le (edgeFinset_mono hmap_le) hmap_card.ge
  exact ⟨hmap_eq ▸ SimpleGraph.Iso.map e H⟩

end IsMinor

end SimpleGraph
