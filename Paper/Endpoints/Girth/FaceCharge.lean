import GraphTheory.Faces.FacialSeparation

/-!
# Local marked-edge charge for short faces

For a supplied faithful plane map, this file retains the cycle-space support
of the particular face while extracting a short cycle.  That support
containment supplies two distinct edges incident with the marked set on that
same face.  The final theorem bounds its deficit by those local marked-edge
occurrences.  A separate global double-count of face-side occurrences is
still needed to sum these local bounds to the paper's `(g-3) p` budget.
-/

namespace Paper.GirthFaceCharge

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra

variable {V : Type*} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The mod-two boundary support of the face indexed by `d`. -/
noncomputable def faceSupport (M : ConnectedPlaneMap G) (d : G.Dart) :
    Finset G.edgeFinset :=
  PlaneTopology.Faces.FacialSeparation.faceBoundarySupport M (faceIndex M.rawRotation d)

/-- Edges of the chosen face boundary support incident with the marked set. -/
noncomputable def markedFaceEdges (M : ConnectedPlaneMap G)
    (A : Finset V) (d : G.Dart) : Finset G.edgeFinset := by
  classical
  exact (faceSupport M d).filter fun e =>
    ∃ x, x ∈ A ∧ x ∈ (e.1 : Sym2 V)

/-- The cycle-space decomposition gives a cycle whose edges all lie in the
mod-two boundary support of this exact face, not just somewhere in the graph.
The support containment is the important strengthening over the coarser
cycle-length lemma. -/
theorem exists_cycle_in_face_support
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic) (d : G.Dart) :
    ∃ (v : V) (c : G.Walk v v),
      c.IsCycle ∧ c.edgeFinset ⊆ faceSupport M d ∧
        c.length ≤ M.rawRotation.faceDegree d := by
  let F := faceSupport M d
  have hmem : G.edgeIndicator F ∈ G.CycleSpace := by
    rw [show G.edgeIndicator F =
        PlaneTopology.Faces.FaceBoundaryAlgebra.faceBoundary M.rawRotation
          (PlaneTopology.Faces.FacialSeparation.faceUnit M.rawRotation
            (faceIndex M.rawRotation d)) by
      simpa [F, faceSupport] using
        PlaneTopology.Faces.FacialSeparation.edgeIndicator_faceBoundarySupport M
          (faceIndex M.rawRotation d)]
    exact PlaneTopology.Faces.FaceBoundaryAlgebra.faceBoundary_mem_cycleSpace M.rawRotation
      (PlaneTopology.Faces.FacialSeparation.faceUnit M.rawRotation
        (faceIndex M.rawRotation d))
  rcases
      (G.edgeIndicator_mem_cycleSpace_iff_hasEdgeDisjointCycleDecomposition F).mp
        hmem with
    ⟨n, v, p, hcycle, hdisjoint, hunion⟩
  have hn : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    subst n
    have hFempty : F = ∅ := by simpa using hunion.symm
    exact (PlaneTopology.Faces.FacialSeparation.faceBoundarySupport_nonempty M hna
      (faceIndex M.rawRotation d)).ne_empty (by simpa [F, faceSupport] using hFempty)
  let i : Fin n := ⟨0, hn⟩
  refine ⟨v i, p i, hcycle i, ?_, ?_⟩
  · intro e he
    change e ∈ F
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩
  · rw [← PlaneTopology.Faces.FacialSeparation.card_edgeFinset_eq_length_of_isTrail
      (p i) (hcycle i).isTrail]
    apply (Finset.card_le_card ?_).trans
      (PlaneTopology.Faces.FacialSeparation.card_faceBoundarySupport_le_faceDegree M d)
    intro e he
    change e ∈ F
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩

/-- A non-acyclic face has degree at least three, including in maps with
bridges or cut vertices. -/
theorem faceDegree_ge_three
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic) (d : G.Dart) :
    3 ≤ M.rawRotation.faceDegree d := by
  obtain ⟨_, c, hc, hlen⟩ :=
    PlaneTopology.Faces.FacialSeparation.exists_cycle_le_faceDegree_of_not_isAcyclic M hna d
  exact hc.three_le_length.trans hlen

/-- Every short face meets the marked set in a cycle lying in that face's
boundary support. -/
theorem short_face_cycle_in_support_meets_marked
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic)
    (A : Finset V) (g : ℕ)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length)
    (d : G.Dart)
    (hshort : M.rawRotation.faceDegree d < g) :
    ∃ (v : V) (c : G.Walk v v),
      c.IsCycle ∧ c.edgeFinset ⊆ faceSupport M d ∧
        c.length ≤ M.rawRotation.faceDegree d ∧
        ∃ x ∈ c.support, x ∈ A := by
  obtain ⟨v, c, hc, hEdges, hlen⟩ :=
    exists_cycle_in_face_support M hna d
  have hshortCycle : c.length < g := hlen.trans_lt hshort
  by_contra hmiss
  have havoid : ∀ x ∈ c.support, x ∉ A := by
    intro x hx
    by_contra hxA
    exact hmiss ⟨v, c, hc, hEdges, hlen, x, hx, hxA⟩
  let S : Set V := {x | x ∉ A}
  have hsupport : ∀ x ∈ c.support, x ∈ S := fun x hx => havoid x hx
  let cOutside := Walk.induce S c hsupport
  have hmap : cOutside.map (Embedding.induce S).toHom = c :=
    Walk.map_induce (s := S) c hsupport
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

/-- Every short face has at least two distinct marked incident edges in its
own boundary support.  The cycle is rotated to a marked vertex; its first and
last edges are distinct by the cycle property. -/
theorem two_marked_edges_on_short_face
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic)
    (A : Finset V) (g : ℕ)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length)
    (d : G.Dart)
    (hshort : M.rawRotation.faceDegree d < g) :
    2 ≤ (markedFaceEdges M A d).card := by
  classical
  obtain ⟨v, c, hc, hEdges, hlen, x, hx, hxA⟩ :=
    short_face_cycle_in_support_meets_marked M hna A g hgirth d hshort
  let c' := c.rotate x hx
  have hc' : c'.IsCycle := hc.rotate hx
  have hrotateEdges : c'.edgeFinset ⊆ faceSupport M d := by
    intro e he
    apply hEdges
    apply (Walk.mem_edgeFinset (G := G) c e).mpr
    have he' : (e.1 : Sym2 V) ∈ c'.edges :=
      (Walk.mem_edgeFinset (G := G) c' e).mp he
    exact (c.rotate_edges x hx).mem_iff.mp he'
  have hfirst : s(x, c'.snd) ∈ c'.edges :=
    c'.mk_start_snd_mem_edges hc'.not_nil
  have hlast : s(c'.penultimate, x) ∈ c'.edges :=
    c'.mk_penultimate_end_mem_edges hc'.not_nil
  have hadjFirst : G.Adj x c'.snd := c'.adj_of_mem_edges hfirst
  have hadjLast : G.Adj c'.penultimate x := c'.adj_of_mem_edges hlast
  let eFirst : G.edgeFinset :=
    ⟨s(x, c'.snd), G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadjFirst)⟩
  let eLast : G.edgeFinset :=
    ⟨s(c'.penultimate, x), G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadjLast)⟩
  have hFirstSupport : eFirst ∈ faceSupport M d :=
    hrotateEdges ((Walk.mem_edgeFinset (G := G) c' eFirst).mpr hfirst)
  have hLastSupport : eLast ∈ faceSupport M d :=
    hrotateEdges ((Walk.mem_edgeFinset (G := G) c' eLast).mpr hlast)
  have hne : eFirst ≠ eLast := by
    intro he
    have he' : s(x, c'.snd) = s(c'.penultimate, x) := congrArg Subtype.val he
    rw [Sym2.eq_iff] at he'
    have hsn : c'.snd ≠ c'.penultimate := hc'.snd_ne_penultimate
    rcases he' with ⟨hxp, hsx⟩ | ⟨_, hsp⟩
    · exact hsn (hsx.trans hxp)
    · exact hsn hsp
  have hFirstMarked : eFirst ∈ markedFaceEdges M A d := by
    refine Finset.mem_filter.mpr ⟨hFirstSupport, ?_⟩
    exact ⟨x, hxA, Sym2.mem_iff.mpr (Or.inl rfl)⟩
  have hLastMarked : eLast ∈ markedFaceEdges M A d := by
    refine Finset.mem_filter.mpr ⟨hLastSupport, ?_⟩
    exact ⟨x, hxA, Sym2.mem_iff.mpr (Or.inr rfl)⟩
  have hpair : ({eFirst, eLast} : Finset G.edgeFinset).card = 2 := by
    simp [hne]
  have hsubset : ({eFirst, eLast} : Finset G.edgeFinset) ⊆
      markedFaceEdges M A d := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he
    · simpa [he] using hFirstMarked
    · simpa [he] using hLastMarked
  calc
    2 = ({eFirst, eLast} : Finset G.edgeFinset).card := hpair.symm
    _ ≤ (markedFaceEdges M A d).card := Finset.card_le_card hsubset

/-- Natural-number deficit of a face of length `j` below girth `g`. -/
def faceDeficit (g j : ℕ) : ℕ := if j < g then g - j else 0

/-- The local deficit is paid by two marked edge occurrences on the face.
Since the two edges are distinct, each can pay at most `(g-3)/2` in the
doubled integer inequality. -/
theorem twice_faceDeficit_le_marked_edges
    (g j markedEdges : ℕ)
    (hg : 3 ≤ g) (hj : 3 ≤ j) (hmarked : 2 ≤ markedEdges) :
    2 * faceDeficit g j ≤ (g - 3) * markedEdges := by
  by_cases hshort : j < g
  · have hdef : faceDeficit g j ≤ g - 3 := by
      simp [faceDeficit, hshort]
      omega
    calc
      2 * faceDeficit g j ≤ 2 * (g - 3) := Nat.mul_le_mul_left 2 hdef
      _ = (g - 3) * 2 := by omega
      _ ≤ (g - 3) * markedEdges := Nat.mul_le_mul_left (g - 3) hmarked
  · simp [faceDeficit, hshort]

/-- The graph-specific per-face charge bound. `markedFaceEdges` consists only
of marked edges in this face's mod-two boundary support; each such edge has
at least one side on this face. -/
theorem face_deficit_paid_by_marked_edges
    (M : ConnectedPlaneMap G) (hna : ¬ G.IsAcyclic)
    (A : Finset V) (g : ℕ)
    (hgirth : ∀ (v : {x : V // x ∉ A})
      (c : (G.induce {x : V | x ∉ A}).Walk v v),
      c.IsCycle → g ≤ c.length)
    (d : G.Dart) (hg : 3 ≤ g) :
    2 * faceDeficit g (M.rawRotation.faceDegree d) ≤
      (g - 3) * (markedFaceEdges M A d).card := by
  have hj := faceDegree_ge_three M hna d
  have hmarked := two_marked_edges_on_short_face M hna A g hgirth d
  by_cases hshort : M.rawRotation.faceDegree d < g
  · have hmarked' := hmarked hshort
    exact twice_faceDeficit_le_marked_edges g
      (M.rawRotation.faceDegree d) (markedFaceEdges M A d).card hg hj hmarked'
  · simp [faceDeficit, hshort]

/-- Abstract aggregation of the proved local inequality.  The only global
input is the incidence budget saying that the total marked side/edge
occurrences over all faces are at most twice the number `p` of marked edges. -/
theorem sum_faceDeficit_le_of_occurrence_budget
    {F S : Type*} [DecidableEq F] [DecidableEq S]
    (faces : Finset F) (length : F → ℕ) (markedOccurrences : F → Finset S)
    (g p : ℕ) (hg : 3 ≤ g)
    (hlen : ∀ f ∈ faces, 3 ≤ length f)
    (hshort : ∀ f ∈ faces, length f < g → 2 ≤ (markedOccurrences f).card)
    (hbudget : (∑ f ∈ faces, (markedOccurrences f).card) ≤ 2 * p) :
    (∑ f ∈ faces, faceDeficit g (length f)) ≤ (g - 3) * p := by
  have hpoint : ∀ f ∈ faces,
      2 * faceDeficit g (length f) ≤
        (g - 3) * (markedOccurrences f).card := by
    intro f hf
    by_cases hs : length f < g
    · exact twice_faceDeficit_le_marked_edges g (length f)
        (markedOccurrences f).card hg (hlen f hf) (hshort f hf hs)
    · simp [faceDeficit, hs]
  have hsum := Finset.sum_le_sum hpoint
  have hdouble :
      2 * (∑ f ∈ faces, faceDeficit g (length f)) ≤
        (g - 3) * ∑ f ∈ faces, (markedOccurrences f).card := by
    calc
      2 * (∑ f ∈ faces, faceDeficit g (length f)) =
          ∑ f ∈ faces, 2 * faceDeficit g (length f) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ f ∈ faces, (g - 3) * (markedOccurrences f).card := hsum
      _ = (g - 3) * ∑ f ∈ faces, (markedOccurrences f).card := by
        rw [Finset.mul_sum]
  have hsumBudget := Nat.mul_le_mul_left (g - 3) hbudget
  nlinarith

end Paper.GirthFaceCharge
