import GraphTheory.SimpleGraph.Connectivity.Whitney

/-!
# Vertex deletion lowers vertex connectivity by at most one

The proof transports actual induced graphs after lifting each separator.
This supplies the two-connected residual graph in the Wagner contraction step.
-/

namespace PlaneTopology.ConnectivityVertexDeletion

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Deleting v and then a separator S is the same actual induced graph as
deleting v together with the image of S in the original vertex type. -/
def deleteSeparatorIso (v : V) (S : Finset {w : V // w ≠ v}) :
    (G.induce {w | w ≠ v}).induce
      ((Finset.univ \ S : Finset {w : V // w ≠ v}) : Set {w : V // w ≠ v}) ≃g
    G.induce ((Finset.univ \ insert v (S.image Subtype.val) : Finset V) : Set V) where
  toEquiv :=
    { toFun := fun w => ⟨w.val.val, by
        have hw : w.val ∉ S := by simpa using w.property
        simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ,
          Finset.mem_insert, true_and, not_or]
        refine ⟨w.val.property, ?_⟩
        intro himage
        obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp himage
        exact hw ((Subtype.ext heq : z = w.val) ▸ hz)⟩
      invFun := fun w => by
        have hw : w.val ≠ v ∧ w.val ∉ S.image Subtype.val := by
          simpa using w.property
        refine ⟨⟨w.val, hw.1⟩, ?_⟩
        simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro h
        exact hw.2 (Finset.mem_image.mpr ⟨⟨w.val, hw.1⟩, h, rfl⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro a b; rfl

/-- Removing one vertex from a (k+1)-vertex-connected graph leaves a
k-vertex-connected graph, proved by lifting every smaller separator. -/
theorem isVertexConnected_delete (v : V) {k : ℕ}
    (hG : G.IsVertexConnected (k + 1)) :
    (G.induce {w | w ≠ v}).IsVertexConnected k := by
  have hcard : Fintype.card ↥({w : V | w ≠ v} : Set V) = Fintype.card V - 1 := by
    calc
      _ = Fintype.card {w : V // w ≠ v} := Fintype.card_congr (Equiv.refl _)
      _ = _ := by simp
  refine ⟨by rw [hcard]; have := hG.1; omega, ?_⟩
  intro S hS
  have hT : (insert v (S.image Subtype.val)).card < k + 1 := by
    have h1 := Finset.card_insert_le v (S.image Subtype.val)
    have h2 := Finset.card_image_le (s := S) (f := Subtype.val)
    omega
  exact (deleteSeparatorIso G v S).connected_iff.mpr (hG.2 _ hT)

/-- The standard k-connectivity number version, for positive remaining
connectivity. No assertion about a plane embedding is involved. -/
theorem isKConnected_delete [Nontrivial V] (v : V) {k : ℕ} (hk : 1 ≤ k)
    (hG : G.IsKConnected (k + 1)) :
    (G.induce {w | w ≠ v}).IsKConnected k := by
  have hvc := isVertexConnected_delete G v
    (SimpleGraph.IsKConnected.isVertexConnected G hG)
  haveI : Nontrivial ↥({w : V | w ≠ v} : Set V) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := hvc.1; omega)
  exact le_vertexConnectivity_of_isVertexConnected _ hvc

#print axioms deleteSeparatorIso
#print axioms isVertexConnected_delete
#print axioms isKConnected_delete

end PlaneTopology.ConnectivityVertexDeletion
