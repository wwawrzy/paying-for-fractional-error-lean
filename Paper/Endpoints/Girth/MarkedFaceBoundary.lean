import GraphTheory.Faces.FacialSeparation

/-!
# Short facial boundaries meet the marked set

This is the cycle-extraction step in the proof of `sc:face`, stated for a
supplied faithful plane-map certificate.  It applies to connected maps with
cut vertices and bridges: the existing cycle-space argument extracts a cycle
from every face boundary when the graph is non-acyclic, without claiming that
the entire face boundary is itself a cycle.
-/

namespace Paper.GirthFaceBoundary

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap

variable {V : Type*} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A face of degree less than `g` contains a graph cycle of length less than
`g`; if the induced graph outside `A` has girth at least `g`, this cycle must
meet `A`.

The non-acyclicity assumption is essential for cycle extraction and is supplied
in the paper's argument after its low-degree-vertex induction. The result is
valid for cut vertices and bridges, since it extracts a cycle from the
face-boundary cycle-space support rather than asserting that the boundary walk
is a simple cycle. -/
theorem short_face_cycle_meets_marked
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic)
    (A : Finset V) (g : ℕ)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length)
    (d : G.Dart)
    (hshort : M.rawRotation.faceDegree d < g) :
    ∃ (v : V) (c : G.Walk v v),
      c.IsCycle ∧ c.length ≤ M.rawRotation.faceDegree d ∧
        ∃ x ∈ c.support, x ∈ A := by
  obtain ⟨v, c, hc, hlen⟩ :=
    PlaneTopology.Faces.FacialSeparation.exists_cycle_le_faceDegree_of_not_isAcyclic M hna d
  have hshortCycle : c.length < g := hlen.trans_lt hshort
  by_contra hmiss
  have havoid : ∀ x ∈ c.support, x ∉ A := by
    intro x hx
    by_contra hxA
    exact hmiss ⟨v, c, hc, hlen, x, hx, hxA⟩
  let S : Set V := {x | x ∉ A}
  have hsupport : ∀ x ∈ c.support, x ∈ S := by
    intro x hx
    exact havoid x hx
  let cOutside := Walk.induce S c hsupport
  have hmap : cOutside.map (Embedding.induce S).toHom = c := by
    exact Walk.map_induce (s := S) c hsupport
  have hcycleMap : (cOutside.map (Embedding.induce S).toHom).IsCycle := by
    simpa [hmap] using hc
  have hcycleOutside : cOutside.IsCycle :=
    (Walk.map_isCycle_iff_of_injective
      (f := (Embedding.induce S).toHom) Subtype.val_injective).mp hcycleMap
  have hlengthOutside : cOutside.length = c.length := by
    exact (Walk.length_map (Embedding.induce S).toHom cOutside).symm.trans
      (congrArg (fun w : G.Walk v v => w.length) hmap)
  have hgirthOutside := hgirth _ cOutside hcycleOutside
  rw [hlengthOutside] at hgirthOutside
  omega

end Paper.GirthFaceBoundary
