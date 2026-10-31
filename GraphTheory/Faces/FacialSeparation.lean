import GraphTheory.Faces.FaceBoundaryAlgebra
import GraphTheory.SimpleGraph.CycleSpaceInduced
import GraphTheory.SimpleGraph.Block.TwoConnectedCycle

/-!
# Facial-occurrence separation for a faithful plane map

This file develops the second half of the algebraic route to the topological
separation lemma shared by facial-occurrence and owner-contact arguments. The face-boundary spanning theorem
is already in `PlaneTopology.Faces.FaceBoundaryAlgebra`; here we analyse a cycle which enters a
vertex through exactly two rotation darts.
-/

namespace PlaneTopology.Faces.FacialSeparation

open SimpleGraph
open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open PlaneTopology.Faces.FaceBoundaryAlgebra

/-! ## A two-toggle lemma on one cyclic order -/

/-- Along a permutation orbit, if the discrete `ZMod 2` boundary toggles at
the first point and vanishes strictly until `f`, then the coefficients at the
first point and at `f` differ. -/
theorem coeff_ne_of_first_toggle
    {X : Type*} (σ : Equiv.Perm X) (a z : X → ZMod 2)
    (hz : ∀ x, z x = a x + a (σ x))
    {e f : X} (n : ℕ) (hn : 0 < n) (hpow : (σ ^ n) e = f)
    (hfirst : z e = 1)
    (hmiddle : ∀ i : ℕ, 0 < i → i < n → z ((σ ^ i) e) = 0) :
    a e ≠ a f := by
  have hstepFirst : a (σ e) = a e + 1 := by
    have hsum : (1 : ZMod 2) = a e + a (σ e) :=
      hfirst.symm.trans (hz e)
    calc
      a (σ e) = 1 - a e :=
        eq_sub_of_add_eq (by simpa [add_comm] using hsum.symm)
      _ = a e + 1 := by
        simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]
  have hprop : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      a ((σ ^ k) e) = a e + 1 := by
    intro k hkpos hkn
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hkzero : k = 0
        · subst k
          simpa using hstepFirst
        · have hkpos' : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkzero
          have hkle : k ≤ n := Nat.le_trans (Nat.le_succ k) hkn
          have hik := ih hkpos' hkle
          have hkmid : z ((σ ^ k) e) = 0 :=
            hmiddle k (Nat.pos_of_ne_zero hkzero) (by omega)
          have hsum :
              a ((σ ^ k) e) + a (σ ((σ ^ k) e)) = 0 := by
            rw [← hz, hkmid]
          have hsame : a (σ ((σ ^ k) e)) = a ((σ ^ k) e) := by
            have hneg := eq_neg_of_add_eq_zero_left hsum
            simpa only [ZMod.neg_eq_self_mod_two] using hneg.symm
          rw [pow_succ', Equiv.Perm.mul_apply, hsame, hik]
  have hfinal := hprop n (Nat.one_le_iff_ne_zero.mpr hn.ne') (Nat.le_refl n)
  rw [hpow] at hfinal
  intro hef
  rw [← hef] at hfinal
  have : (0 : ZMod 2) = 1 := by
    apply add_left_cancel (a := a e)
    rw [add_zero]
    exact hfinal
  exact zero_ne_one this

/-- Orbit-invariant form of `coeff_ne_of_first_toggle`: if the discrete
boundary is supported exactly at two distinct points of one permutation
cycle, the coefficients at those points are different. -/
theorem coeff_ne_of_two_toggles_on_cycle
    {X : Type*} [Finite X] (σ : Equiv.Perm X) (a z : X → ZMod 2)
    (hz : ∀ x, z x = a x + a (σ x))
    {e f : X} (hef : e ≠ f) (hcycle : σ.SameCycle e f)
    (he : z e = 1)
    (hzero : ∀ x, x ≠ e → x ≠ f → z x = 0) :
    a e ≠ a f := by
  classical
  let hex : ∃ n : ℕ, (σ ^ n) e = f := hcycle.exists_nat_pow_eq
  let n := Nat.find hex
  have hpow : (σ ^ n) e = f := Nat.find_spec hex
  have hn : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    apply hef
    simpa [hnzero] using hpow
  apply coeff_ne_of_first_toggle σ a z hz n hn hpow he
  intro i hi hin
  apply hzero
  · intro hie
    have hle : i ≤ n := Nat.le_of_lt hin
    have hni : n - i < n := by omega
    have hshort : (σ ^ (n - i)) e = f := by
      calc
        (σ ^ (n - i)) e = (σ ^ (n - i)) ((σ ^ i) e) := by rw [hie]
        _ = (σ ^ ((n - i) + i)) e := by
          rw [pow_add, Equiv.Perm.mul_apply]
        _ = (σ ^ n) e := by rw [Nat.sub_add_cancel hle]
        _ = f := hpow
    exact (Nat.find_min hex (by simpa [n] using hni)) hshort
  · exact fun hif => (Nat.find_min hex (by simpa [n] using hin)) hif

/-! ## A cycle cannot use two corners of the same face at one vertex -/

variable {V : Type*} {G : SimpleGraph V}

/-- The endpoint of an outgoing dart survives deletion of its source. -/
def outDartTargetAway (c : V) (e : ↥(outDartsAt G c)) :
    PlaneTopology.Faces.FacialOccurrence.ComponentMap.Away V c :=
  ⟨e.1.snd, by
    intro hsnd
    exact e.1.fst_ne_snd (e.2.trans hsnd.symm)⟩

/-- At a fixed source, an undirected edge determines its outgoing dart. -/
theorem outDart_eq_of_edge_eq (c : V) (e f : ↥(outDartsAt G c))
    (h : e.1.edge = f.1.edge) : e = f := by
  apply Subtype.ext
  rcases (SimpleGraph.dart_edge_eq_iff e.1 f.1).mp h with hef | hef
  · exact hef
  · exfalso
    apply f.1.fst_ne_snd
    calc
      f.1.fst = c := f.2
      _ = e.1.fst := e.2.symm
      _ = f.1.symm.fst := congrArg (fun d : G.Dart ↦ d.fst) hef
      _ = f.1.snd := rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If the targets of two distinct outgoing darts are connected after their
common source is deleted, their joining path together with the two darts is a
cycle-space vector using exactly those two incident edges at the source. -/
theorem exists_cycleSpace_two_incident_of_reachable_away
    (c : V) (e f : ↥(outDartsAt G c)) (hef : e ≠ f)
    (hreach : (PlaneTopology.Faces.FacialOccurrence.ComponentMap.induceAway G c).Reachable
      (outDartTargetAway c e) (outDartTargetAway c f)) :
    ∃ z : EdgeSpace G, z ∈ G.CycleSpace ∧
      ∀ d : ↥(outDartsAt G c),
        z ⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ =
          if d = e ∨ d = f then 1 else 0 := by
  apply hreach.elim_path
  intro p
  let φ := SimpleGraph.Embedding.induce (G := G) {v : V | v ≠ c}
  let pG : G.Walk e.1.snd f.1.snd :=
    (p : (PlaneTopology.Faces.FacialOccurrence.ComponentMap.induceAway G c).Walk
      (outDartTargetAway c e) (outDartTargetAway c f)).map φ.toHom
  have hpG : pG.IsPath := by
    unfold pG
    exact SimpleGraph.Walk.map_isPath_of_injective
      (f := φ.toHom) φ.injective p.property
  have hcnot : c ∉ pG.support := by
    intro hc
    change c ∈ ((p :
      (PlaneTopology.Faces.FacialOccurrence.ComponentMap.induceAway G c).Walk
        (outDartTargetAway c e) (outDartTargetAway c f)).map φ.toHom).support at hc
    rw [SimpleGraph.Walk.support_map] at hc
    rcases List.mem_map.mp hc with ⟨y, _hy, hyc⟩
    change (y : V) = c at hyc
    exact y.property hyc
  have headj : G.Adj c e.1.snd := by
    exact (G.adj_congr_of_sym2 (by rw [e.2])).mp e.1.adj
  have hfadj : G.Adj f.1.snd c := by
    exact (G.adj_congr_of_sym2 (by rw [f.2])).mp f.1.adj.symm
  let tail : G.Walk e.1.snd c := pG.concat hfadj
  have htailPath : tail.IsPath := by
    unfold tail
    exact hpG.concat hcnot hfadj
  have heNotPath : e.1.edge ∉ pG.edges := by
    intro he
    apply hcnot
    have hs : e.1.fst ∈ pG.support :=
      pG.fst_mem_support_of_mem_edges he
    exact Eq.mp (congrArg (fun v : V ↦ v ∈ pG.support) e.2) hs
  have hefEdge : e.1.edge ≠ f.1.edge := by
    exact fun h ↦ hef (outDart_eq_of_edge_eq c e f h)
  have hfback : s(f.1.snd, c) = f.1.edge := by
    change s(f.1.snd, c) = s(f.1.fst, f.1.snd)
    rw [f.2]
    exact Sym2.eq_swap
  have hcedge : s(c, e.1.snd) = e.1.edge := by
    change s(c, e.1.snd) = s(e.1.fst, e.1.snd)
    rw [e.2]
  have heNotTail : e.1.edge ∉ tail.edges := by
    unfold tail
    rw [SimpleGraph.Walk.edges_concat]
    simp [heNotPath, hfback, hefEdge]
  let γ : G.Walk c c := SimpleGraph.Walk.cons headj tail
  have hγcycle : γ.IsCycle := by
    apply (SimpleGraph.Walk.cons_isCycle_iff tail headj).2
    refine ⟨htailPath, ?_⟩
    rw [hcedge]
    exact heNotTail
  let z : EdgeSpace G := SimpleGraph.Walk.edgeVector G γ
  refine ⟨z, SimpleGraph.Walk.edgeVector_mem_cycleSpace G hγcycle, ?_⟩
  intro d
  have hdNotPath : d.1.edge ∉ pG.edges := by
    intro hd
    apply hcnot
    have hs : d.1.fst ∈ pG.support :=
      pG.fst_mem_support_of_mem_edges hd
    exact Eq.mp (congrArg (fun v : V ↦ v ∈ pG.support) d.2) hs
  have hmemEdges : d.1.edge ∈ γ.edges ↔ d = e ∨ d = f := by
    unfold γ tail
    rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_concat]
    rw [List.concat_eq_append]
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    rw [hcedge, hfback]
    constructor
    · rintro (hde | hdpath | hdf)
      · exact Or.inl (outDart_eq_of_edge_eq c d e hde)
      · exact False.elim (hdNotPath hdpath)
      · exact Or.inr (outDart_eq_of_edge_eq c d f hdf)
    · intro h
      rcases h with hde | hdf
      · exact Or.inl (congrArg (fun q : ↥(outDartsAt G c) ↦ q.1.edge) hde)
      · exact Or.inr (Or.inr
          (congrArg (fun q : ↥(outDartsAt G c) ↦ q.1.edge) hdf))
  have hmem :
      (⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ : G.edgeFinset) ∈
          γ.edgeFinset ↔ d = e ∨ d = f := by
    rw [SimpleGraph.Walk.mem_edgeFinset]
    exact hmemEdges
  by_cases hdef : d = e ∨ d = f <;>
    simp [z, SimpleGraph.Walk.edgeVector, SimpleGraph.edgeIndicator, hmem, hdef]

/-- Algebraic Jordan separation at one vertex.  A cycle-space vector whose
only nonzero incident coordinates at `c` are two distinct darts cannot have
those two darts on the same face of a connected faithful plane map. -/
theorem not_sameFace_of_cycleSpace_two_incident
    (M : ConnectedPlaneMap G) (c : V)
    (e f : ↥(outDartsAt G c)) (hef : e ≠ f)
    (z : EdgeSpace G) (hzcycle : z ∈ G.CycleSpace)
    (hincident : ∀ d : ↥(outDartsAt G c),
      z ⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ =
        if d = e ∨ d = f then 1 else 0) :
    ¬M.rawRotation.SameFace e.1 f.1 := by
  intro hface
  have hzrange : z ∈ LinearMap.range (faceBoundary M.rawRotation) := by
    rw [range_faceBoundary_eq_cycleSpace M]
    exact hzcycle
  rcases hzrange with ⟨a, ha⟩
  let σc : Equiv.Perm ↥(outDartsAt G c) :=
    sigmaOutDartEquiv M.rawRotation c
  let A : ↥(outDartsAt G c) → ZMod 2 :=
    fun d ↦ a (faceIndex M.rawRotation d.1)
  let Z : ↥(outDartsAt G c) → ZMod 2 :=
    fun d ↦ z ⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩
  have hderiv : ∀ d, Z d = A d + A (σc d) := by
    intro d
    calc
      Z d = faceBoundary M.rawRotation a
          ⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ := by
        exact congrFun ha
          ⟨d.1.edge, G.mem_edgeFinset.mpr d.1.edge_mem⟩ |>.symm
      _ = a (faceIndex M.rawRotation d.1) +
          a (faceIndex M.rawRotation d.1.symm) :=
        faceBoundary_eq_dart_sum M.rawRotation a d.1
      _ = a (faceIndex M.rawRotation d.1) +
          a (faceIndex M.rawRotation (M.rawRotation.σ d.1)) := by
        rw [faceIndex_sigma_eq_symm]
      _ = A d + A (σc d) := by
        rfl
  have hcycle : σc.SameCycle e f := by
    let σc' : Equiv.Perm ↥(outDartsAt G c) :=
      M.rawRotation.σ.subtypePerm
        (fun _ ↦ (M.rotation.vertexCyclic c).apply_mem_iff)
    have hσσ : σc = σc' := by
      apply Equiv.ext
      intro d
      apply Subtype.ext
      rfl
    rw [hσσ]
    exact (M.rotation.vertexCyclic c).subtypePerm.2
      (Set.mem_univ e) (Set.mem_univ f)
  have hfirst : Z e = 1 := by
    unfold Z
    rw [hincident]
    simp
  have hzero : ∀ d, d ≠ e → d ≠ f → Z d = 0 := by
    intro d hde hdf
    unfold Z
    rw [hincident]
    simp [hde, hdf]
  have hne : A e ≠ A f :=
    coeff_ne_of_two_toggles_on_cycle σc A Z hderiv hef hcycle hfirst hzero
  apply hne
  exact congrArg a ((faceIndex_eq_iff_sameFace M.rawRotation e.1 f.1).mpr hface)

/-- **FACIAL-OCCURRENCE separation (L9b).**  In a supplied connected faithful
plane map, distinct occurrences of a vertex on one face land in distinct
components after that vertex is deleted.  This is the complete second half of
the algebraic separation route begun in `PlaneTopology.Faces.FaceBoundaryAlgebra`. -/
theorem componentAfterDelete_injective_of_connectedPlaneMap
    (M : ConnectedPlaneMap G) (base : G.Dart) (c : V) :
    Function.Injective
      (PlaneTopology.Faces.FacialOccurrence.ComponentMap.componentAfterDelete
        (K := G) (r := M.rawRotation) (base := base) (c := c)) := by
  intro q r hcomponent
  by_contra hqr
  have hdart : q.1.1 ≠ r.1.1 := by
    intro h
    apply hqr
    apply Subtype.ext
    apply Subtype.ext
    exact h
  let e : ↥(outDartsAt G c) := ⟨q.1.1, q.2⟩
  let f : ↥(outDartsAt G c) := ⟨r.1.1, r.2⟩
  have hef : e ≠ f := by
    intro h
    apply hdart
    exact congrArg (fun z : ↥(outDartsAt G c) ↦ z.1) h
  have hsameFace : M.rawRotation.SameFace e.1 f.1 := by
    exact M.rawRotation.sameFace_equivalence.trans
      (M.rawRotation.sameFace_equivalence.symm q.1.2) r.1.2
  have heTarget : outDartTargetAway c e =
      PlaneTopology.Faces.FacialOccurrence.ComponentMap.occurrenceTargetAway q := by
    apply Subtype.ext
    rfl
  have hfTarget : outDartTargetAway c f =
      PlaneTopology.Faces.FacialOccurrence.ComponentMap.occurrenceTargetAway r := by
    apply Subtype.ext
    rfl
  have hreach :
      (PlaneTopology.Faces.FacialOccurrence.ComponentMap.induceAway G c).Reachable
        (outDartTargetAway c e) (outDartTargetAway c f) := by
    rw [heTarget, hfTarget]
    exact SimpleGraph.ConnectedComponent.exact hcomponent
  obtain ⟨z, hzcycle, hincident⟩ :=
    exists_cycleSpace_two_incident_of_reachable_away c e f hef hreach
  exact (not_sameFace_of_cycleSpace_two_incident
    M c e f hef z hzcycle hincident) hsameFace

/-! ## Cyclic faces are automatic in the two-connected case -/

/-- In a connected faithful sphere map of a two-connected graph, the two
orientations of an edge cannot belong to the same face.  Otherwise every
linear combination of face boundaries would vanish on that edge, whereas
two-connectivity puts the edge on a graph cycle. -/
theorem dart_not_sameFace_symm_of_isKConnected_two
    (M : ConnectedPlaneMap G) (htwo : G.IsKConnected 2) (e : G.Dart) :
    ¬M.rawRotation.SameFace e e.symm := by
  intro hsame
  letI : Nontrivial V := htwo.two_nontrivial
  have hvertex : G.IsVertexConnected 2 := htwo.isVertexConnected G
  have hdeleted : (G.deleteEdges {e.edge}).Connected :=
    hvertex.deleteEdges_singleton_connected e.edge
  have hreach : (G \ SimpleGraph.fromEdgeSet {e.edge}).Reachable e.fst e.snd := by
    change (G.deleteEdges {e.edge}).Reachable e.fst e.snd
    exact hdeleted.preconnected e.fst e.snd
  obtain ⟨v, p, hpcycle, hedge⟩ :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := G) (v := e.fst) (w := e.snd)).mp ⟨e.adj, hreach⟩
  let z : EdgeSpace G := SimpleGraph.Walk.edgeVector G p
  have hzcycle : z ∈ G.CycleSpace :=
    SimpleGraph.Walk.edgeVector_mem_cycleSpace G hpcycle
  have hzrange : z ∈ LinearMap.range (faceBoundary M.rawRotation) := by
    rw [range_faceBoundary_eq_cycleSpace M]
    exact hzcycle
  rcases hzrange with ⟨a, ha⟩
  let ee : G.edgeFinset :=
    ⟨e.edge, G.mem_edgeFinset.mpr e.edge_mem⟩
  have hzone : z ee = 1 := by
    have hedge' : e.edge ∈ p.edges := by
      simpa only [SimpleGraph.Dart.edge] using hedge
    simp [z, SimpleGraph.Walk.edgeVector, SimpleGraph.edgeIndicator, ee,
      SimpleGraph.Walk.mem_edgeFinset, hedge']
  have hfaces : faceIndex M.rawRotation e =
      faceIndex M.rawRotation e.symm :=
    (faceIndex_eq_iff_sameFace M.rawRotation e e.symm).mpr hsame
  have hzzero : z ee = 0 := by
    calc
      z ee = faceBoundary M.rawRotation a ee := by
        exact congrFun ha ee |>.symm
      _ = a (faceIndex M.rawRotation e) +
          a (faceIndex M.rawRotation e.symm) :=
        faceBoundary_eq_dart_sum M.rawRotation a e
      _ = 0 := by rw [hfaces]; exact ZModModule.add_self _
  rw [hzone] at hzzero
  exact one_ne_zero hzzero

/-- Consequently a facial boundary walk in the two-connected faithful sphere
map never repeats an undirected edge: its dart orbit is duplicate-free, and
the only other way two darts can have the same edge is by reversal. -/
theorem faceBoundaryWalk_isTrail_of_isKConnected_two
    (M : ConnectedPlaneMap G) (htwo : G.IsKConnected 2) (d : G.Dart) :
    (M.rawRotation.faceBoundaryWalk d).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  unfold SimpleGraph.Walk.edges
  rw [M.rawRotation.faceBoundaryWalk_darts]
  apply List.Nodup.map_on
  · intro e he f hf hedge
    rcases (SimpleGraph.dart_edge_eq_iff e f).mp hedge with hef | hef
    · exact hef
    · exfalso
      have heface : M.rawRotation.SameFace d e := by
        exact (Equiv.Perm.mem_toList_iff.mp he).1
      have hfface : M.rawRotation.SameFace d f := by
        exact (Equiv.Perm.mem_toList_iff.mp hf).1
      have hefface : M.rawRotation.SameFace e f :=
        M.rawRotation.sameFace_equivalence.trans
          (M.rawRotation.sameFace_equivalence.symm heface) hfface
      rw [hef] at hefface
      exact (dart_not_sameFace_symm_of_isKConnected_two M htwo f)
        (M.rawRotation.sameFace_equivalence.symm hefface)
  · exact Equiv.Perm.nodup_toList M.rawRotation.facePerm d

/-- **Diestel Proposition 4.2.5 in the faithful-map interface.**  Every face
of a two-connected faithful sphere map contains a cycle no longer than its
facial degree.  In particular, `HasCyclicFaces` need not be supplied as a
separate topological assumption once the faithful plane map is available. -/
theorem hasCyclicFaces_of_connectedPlaneMap_of_isKConnected_two
    (M : ConnectedPlaneMap G) (htwo : G.IsKConnected 2) :
    M.rawRotation.HasCyclicFaces := by
  intro d _hd
  let w := M.rawRotation.faceBoundaryWalk d
  have htrail : w.IsTrail := by
    exact faceBoundaryWalk_isTrail_of_isKConnected_two M htwo d
  have hne : w ≠ .nil := by
    intro hnil
    have hzero : w.length = 0 := by rw [hnil]; rfl
    have hlength : w.length = M.rawRotation.faceDegree d := by
      exact M.rawRotation.faceBoundaryWalk_length d
    have hpos := M.rawRotation.faceDegree_pos d
    omega
  have hcycle : w.cycleBypass.IsCycle :=
    SimpleGraph.Walk.IsTrail.isCycle_cycleBypass hne htrail
  refine ⟨d.fst, w.cycleBypass, hcycle, ?_⟩
  calc
    w.cycleBypass.length ≤ w.length := by
      cases hw : w with
      | nil => exact False.elim (hne hw)
      | cons h p =>
          simp only [SimpleGraph.Walk.cycleBypass,
            SimpleGraph.Walk.length_cons]
          exact Nat.succ_le_succ (SimpleGraph.Walk.length_bypass_le p)
    _ = M.rawRotation.faceDegree d :=
      M.rawRotation.faceBoundaryWalk_length d

/-- A connected faithful sphere map of a graph containing a cycle has at
least two face orbits. -/
theorem two_le_card_faceIndex_of_not_isAcyclic
    (M : ConnectedPlaneMap G) (hna : ¬G.IsAcyclic) :
    2 ≤ Fintype.card (FaceIndex M.rawRotation) := by
  have hcomponent : Fintype.card G.ConnectedComponent = 1 :=
    SimpleGraph.connected_card_connectedComponent M.connected
  have hcomponentSetLike :
      @Fintype.card G.ConnectedComponent SetLike.instFintype = 1 := by
    calc
      @Fintype.card G.ConnectedComponent SetLike.instFintype =
          @Fintype.card G.ConnectedComponent
            (SimpleGraph.instFintypeConnectedComponent G) :=
        @Fintype.card_congr G.ConnectedComponent G.ConnectedComponent
          SetLike.instFintype (SimpleGraph.instFintypeConnectedComponent G)
          (Equiv.refl G.ConnectedComponent)
      _ = 1 := hcomponent
  have hnotTreeCard :
      G.edgeFinset.card + 1 ≠ Fintype.card V := by
    intro hcard
    apply hna
    rw [SimpleGraph.isAcyclic_iff_edgeFinset_card_add_card_connectedComponent]
    calc
      G.edgeFinset.card +
          @Fintype.card G.ConnectedComponent SetLike.instFintype =
          G.edgeFinset.card + 1 := by rw [hcomponentSetLike]
      _ = Fintype.card V := hcard
  have hlower : Fintype.card V ≤ G.edgeFinset.card + 1 :=
    SimpleGraph.connected_card_le_edgeFinset M.connected
  have hfaces := M.euler
  change 2 ≤ Fintype.card (FaceIndex M.rotation.toRotationSystem)
  rw [card_faceIndex_eq_numFaces]
  omega

/-- The unit face chain supported on one actual face orbit. -/
def faceUnit (r : G.RotationSystem) (F : FaceIndex r) : FaceChain r :=
  fun H ↦ if H = F then 1 else 0

/-- In a non-acyclic faithful sphere map, the boundary of every individual
face is nonzero.  The kernel consists only of constant chains, while there
are at least two faces. -/
theorem faceBoundary_faceUnit_ne_zero
    (M : ConnectedPlaneMap G) (hna : ¬G.IsAcyclic)
    (F : FaceIndex M.rawRotation) :
    faceBoundary M.rawRotation (faceUnit M.rawRotation F) ≠ 0 := by
  intro hzero
  have hker : faceUnit M.rawRotation F ∈
      LinearMap.ker (faceBoundary M.rawRotation) := by
    rw [LinearMap.mem_ker]
    exact hzero
  have hcard : 1 < Fintype.card (FaceIndex M.rawRotation) :=
    two_le_card_faceIndex_of_not_isAcyclic M hna
  obtain ⟨H, hHF⟩ := Fintype.exists_ne_of_one_lt_card hcard F
  have heq := eq_on_faces_of_mem_ker M.toConnectedCellularMap hker F H
  simp only [faceUnit, if_neg hHF] at heq
  exact one_ne_zero heq

/-- The finite support of the boundary of one face. -/
noncomputable def faceBoundarySupport
    (M : ConnectedPlaneMap G) (F : FaceIndex M.rawRotation) :
    Finset G.edgeFinset :=
  Finset.univ.filter (fun e ↦
    faceBoundary M.rawRotation (faceUnit M.rawRotation F) e ≠ 0)

private theorem zmod_two_eq_zero_or_one (a : ZMod 2) :
    a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The support indicator recovers exactly the boundary vector of one face. -/
theorem edgeIndicator_faceBoundarySupport
    (M : ConnectedPlaneMap G) (F : FaceIndex M.rawRotation) :
    G.edgeIndicator (faceBoundarySupport M F) =
      faceBoundary M.rawRotation (faceUnit M.rawRotation F) := by
  funext e
  rw [SimpleGraph.edgeIndicator]
  by_cases hm : e ∈ faceBoundarySupport M F
  · rw [if_pos hm]
    have hne :
        faceBoundary M.rawRotation (faceUnit M.rawRotation F) e ≠ 0 :=
      (Finset.mem_filter.mp hm).2
    obtain he | he := zmod_two_eq_zero_or_one
      (faceBoundary M.rawRotation (faceUnit M.rawRotation F) e)
    · exact (hne he).elim
    · exact he.symm
  · rw [if_neg hm]
    by_contra hne
    apply hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ e, fun hzero ↦ hne hzero.symm⟩

/-- In a non-acyclic faithful sphere map, every individual face has a
nonempty mod-two boundary support. -/
theorem faceBoundarySupport_nonempty
    (M : ConnectedPlaneMap G) (hna : ¬G.IsAcyclic)
    (F : FaceIndex M.rawRotation) :
    (faceBoundarySupport M F).Nonempty := by
  by_contra hempty
  have hsupport : faceBoundarySupport M F = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  apply faceBoundary_faceUnit_ne_zero M hna F
  rw [← edgeIndicator_faceBoundarySupport M F, hsupport]
  rfl

/-- A support edge has at least one oriented side in the selected face. -/
theorem faceBoundarySupport_side
    (M : ConnectedPlaneMap G) (F : FaceIndex M.rawRotation)
    {e : G.edgeFinset} (he : e ∈ faceBoundarySupport M F) :
    faceIndex M.rawRotation (dartOfEdge e) = F ∨
      faceIndex M.rawRotation (dartOfEdge e).symm = F := by
  have hne :
      faceBoundary M.rawRotation (faceUnit M.rawRotation F) e ≠ 0 :=
    (Finset.mem_filter.mp he).2
  rw [faceBoundary_apply] at hne
  by_contra hnone
  rw [not_or] at hnone
  rcases hnone with ⟨hleft, hright⟩
  simp only [faceUnit, if_neg hleft, if_neg hright, add_zero] at hne
  exact hne rfl

/-- The distinct graph edges encountered by the dart orbit of one face. -/
noncomputable def faceEdgeFinset
    (r : G.RotationSystem) (d : G.Dart) : Finset G.edgeFinset :=
  (r.faceDarts d).toFinset.image
    (fun q ↦ ⟨q.edge, G.mem_edgeFinset.mpr q.edge_mem⟩)

/-- Every support edge of the face indexed by `d` is encountered by the
concrete face-dart orbit based at `d`. -/
theorem faceBoundarySupport_subset_faceEdgeFinset
    (M : ConnectedPlaneMap G) (d : G.Dart) :
    faceBoundarySupport M (faceIndex M.rawRotation d) ⊆
      faceEdgeFinset M.rawRotation d := by
  intro e he
  rcases faceBoundarySupport_side M (faceIndex M.rawRotation d) he with
    hside | hside
  · apply Finset.mem_image.mpr
    refine ⟨dartOfEdge e, ?_, ?_⟩
    · rw [List.mem_toFinset]
      unfold RotationSystem.faceDarts
      rw [Equiv.Perm.mem_toList_iff]
      exact ⟨(faceIndex_eq_iff_sameFace M.rawRotation d (dartOfEdge e)).mp
          hside.symm,
        Equiv.Perm.mem_support.mpr
          (M.rawRotation.facePerm_ne_self d)⟩
    · apply Subtype.ext
      exact dartOfEdge_edge e
  · apply Finset.mem_image.mpr
    refine ⟨(dartOfEdge e).symm, ?_, ?_⟩
    · rw [List.mem_toFinset]
      unfold RotationSystem.faceDarts
      rw [Equiv.Perm.mem_toList_iff]
      exact ⟨(faceIndex_eq_iff_sameFace M.rawRotation d (dartOfEdge e).symm).mp
          hside.symm,
        Equiv.Perm.mem_support.mpr
          (M.rawRotation.facePerm_ne_self d)⟩
    · apply Subtype.ext
      exact (SimpleGraph.Dart.edge_symm (dartOfEdge e)).trans
        (dartOfEdge_edge e)

/-- The number of distinct graph edges on a face is at most the length of its
dart orbit, i.e. at most its face degree. -/
theorem card_faceEdgeFinset_le_faceDegree
    (r : G.RotationSystem) (d : G.Dart) :
    (faceEdgeFinset r d).card ≤ r.faceDegree d := by
  calc
    (faceEdgeFinset r d).card ≤ (r.faceDarts d).toFinset.card := by
      exact Finset.card_image_le
    _ ≤ (r.faceDarts d).length := List.toFinset_card_le _
    _ = r.faceDegree d := by
      rw [← r.faceBoundaryWalk_length d, ← Walk.length_darts,
        r.faceBoundaryWalk_darts]

/-- Therefore the mod-two boundary support of the face indexed by `d` has at
most the degree of that face. -/
theorem card_faceBoundarySupport_le_faceDegree
    (M : ConnectedPlaneMap G) (d : G.Dart) :
    (faceBoundarySupport M (faceIndex M.rawRotation d)).card ≤
      M.rawRotation.faceDegree d :=
  (Finset.card_le_card
    (faceBoundarySupport_subset_faceEdgeFinset M d)).trans
      (card_faceEdgeFinset_le_faceDegree M.rawRotation d)

/-- A trail uses each edge once, so its edge-finset cardinality is its walk
length.  The analogous helper in `CycleSpaceInduced` is private. -/
theorem card_edgeFinset_eq_length_of_isTrail
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    p.edgeFinset.card = p.length := by
  rw [← p.length_edges, ← List.toFinset_card_of_nodup hp.edges_nodup]
  apply Finset.card_bij
      (fun e (_ : e ∈ p.edgeFinset) ↦ (e.1 : Sym2 V))
  · intro e he
    simpa using (Walk.mem_edgeFinset (G := G) p e).mp he
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro e he
    have he' : e ∈ p.edges := by simpa using he
    have heG : e ∈ G.edgeSet := Walk.edges_subset_edgeSet p he'
    refine ⟨⟨e, G.mem_edgeFinset.mpr heG⟩, ?_, rfl⟩
    exact (Walk.mem_edgeFinset (G := G) p _).mpr he'

/-- Every face of a non-acyclic faithful sphere map contains some graph cycle
whose length is bounded by that face's degree. -/
theorem exists_cycle_le_faceDegree_of_not_isAcyclic
    (M : ConnectedPlaneMap G) (hna : ¬G.IsAcyclic) (d : G.Dart) :
    ∃ (v : V) (c : G.Walk v v),
      c.IsCycle ∧ c.length ≤ M.rawRotation.faceDegree d := by
  let F := faceBoundarySupport M (faceIndex M.rawRotation d)
  have hmem : G.edgeIndicator F ∈ G.CycleSpace := by
    rw [show G.edgeIndicator F =
        faceBoundary M.rawRotation
          (faceUnit M.rawRotation (faceIndex M.rawRotation d)) by
      simpa [F] using
        edgeIndicator_faceBoundarySupport M
          (faceIndex M.rawRotation d)]
    exact faceBoundary_mem_cycleSpace M.rawRotation
      (faceUnit M.rawRotation (faceIndex M.rawRotation d))
  rcases
      (G.edgeIndicator_mem_cycleSpace_iff_hasEdgeDisjointCycleDecomposition F).mp
        hmem with
    ⟨n, v, p, hcycle, hdisjoint, hunion⟩
  have hn : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    subst n
    have hFempty : F = ∅ := by
      simpa using hunion.symm
    exact (faceBoundarySupport_nonempty M hna
      (faceIndex M.rawRotation d)).ne_empty (by simpa [F] using hFempty)
  let i : Fin n := ⟨0, hn⟩
  refine ⟨v i, p i, hcycle i, ?_⟩
  rw [← card_edgeFinset_eq_length_of_isTrail (p i) (hcycle i).isTrail]
  apply (Finset.card_le_card ?_).trans
    (card_faceBoundarySupport_le_faceDegree M d)
  intro e he
  change e ∈ F
  rw [← hunion]
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩

/-- Non-acyclicity is enough to derive the legacy cyclic-face condition from
a supplied faithful connected sphere map; no separate facial-cycle field is
needed. -/
theorem hasCyclicFaces_of_connectedPlaneMap_of_not_isAcyclic
    (M : ConnectedPlaneMap G) (hna : ¬G.IsAcyclic) :
    M.rawRotation.HasCyclicFaces := by
  intro d _hd
  exact exists_cycle_le_faceDegree_of_not_isAcyclic M hna d

#print axioms coeff_ne_of_first_toggle
#print axioms coeff_ne_of_two_toggles_on_cycle
#print axioms exists_cycleSpace_two_incident_of_reachable_away
#print axioms not_sameFace_of_cycleSpace_two_incident
#print axioms componentAfterDelete_injective_of_connectedPlaneMap
#print axioms dart_not_sameFace_symm_of_isKConnected_two
#print axioms faceBoundaryWalk_isTrail_of_isKConnected_two
#print axioms hasCyclicFaces_of_connectedPlaneMap_of_isKConnected_two
#print axioms two_le_card_faceIndex_of_not_isAcyclic
#print axioms faceBoundary_faceUnit_ne_zero
#print axioms edgeIndicator_faceBoundarySupport
#print axioms faceBoundarySupport_nonempty
#print axioms faceBoundarySupport_side
#print axioms faceBoundarySupport_subset_faceEdgeFinset
#print axioms card_faceBoundarySupport_le_faceDegree
#print axioms card_edgeFinset_eq_length_of_isTrail
#print axioms exists_cycle_le_faceDegree_of_not_isAcyclic
#print axioms hasCyclicFaces_of_connectedPlaneMap_of_not_isAcyclic

end PlaneTopology.Faces.FacialSeparation

/-! ## Compatibility: alternate facial-occurrence API

Both API developments are retained with distinct declaration names.
-/

/-!
# Algebraic separation of facial occurrences

This file closes the faithful-plane-map part of the `FACIAL-OCCURRENCE`
bridge.  Its first lemma is deliberately independent of graphs: on one
finite cyclic orbit, an `F₂` potential whose discrete derivative is supported
at two distinct points takes different values at those two points.
-/

namespace PlaneTopology.Faces.FacialSeparation

open SimpleGraph
open PlaneTopology.Faces.FacialOccurrence
open PlaneTopology.Faces.FacialOccurrence.FaceBoundary
open PlaneTopology.Faces.FacialOccurrence.ComponentMap

theorem dart_eq_of_edge_eq_of_fst_eq
    {V : Type*} {G : SimpleGraph V} {d e : G.Dart}
    (hfst : d.fst = e.fst) (hedge : d.edge = e.edge) :
    d = e := by
  rcases (SimpleGraph.dart_edge_eq_iff d e).mp hedge with h | h
  · exact h
  · exfalso
    apply e.fst_ne_snd
    exact hfst.symm.trans (congrArg (fun x : G.Dart => x.fst) h)

theorem value_ne_of_two_toggles
    {α : Type*} [Finite α] [DecidableEq α]
    (σ : Equiv.Perm α) {d e : α}
    (hcycle : σ.SameCycle d e) (hne : d ≠ e)
    (b : α → ZMod 2)
    (hd : b d + b (σ d) = 1)
    (hz : ∀ k : ℕ, (σ ^ k) d ≠ d → (σ ^ k) d ≠ e →
      b ((σ ^ k) d) + b (σ ((σ ^ k) d)) = 0) :
    b d ≠ b e := by
  let n : ℕ := Nat.find hcycle.exists_nat_pow_eq
  have hn : (σ ^ n) d = e := Nat.find_spec hcycle.exists_nat_pow_eq
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos h
    apply hne
    simpa [hnzero] using hn
  have hbeforeE : ∀ k < n, (σ ^ k) d ≠ e := by
    intro k hk hke
    exact Nat.find_min hcycle.exists_nat_pow_eq hk hke
  have hbeforeD : ∀ k, 0 < k → k < n → (σ ^ k) d ≠ d := by
    intro k hk hkn hkd
    have hsub_lt : n - k < n := Nat.sub_lt hnpos hk
    have hk_le : k ≤ n := hkn.le
    have hhit : (σ ^ (n - k)) d = e := by
      calc
        (σ ^ (n - k)) d = (σ ^ (n - k)) ((σ ^ k) d) := by rw [hkd]
        _ = ((σ ^ (n - k)) * (σ ^ k)) d := by rfl
        _ = (σ ^ ((n - k) + k)) d := by rw [pow_add]
        _ = (σ ^ n) d := by rw [Nat.sub_add_cancel hk_le]
        _ = e := hn
    exact Nat.find_min hcycle.exists_nat_pow_eq hsub_lt hhit
  have hconstant : ∀ k, 1 ≤ k → k ≤ n → b ((σ ^ k) d) = b (σ d) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    intro hjn
    induction j with
    | zero => simp
    | succ j ih =>
        have hj1_pos : 0 < 1 + j := by omega
        have hj1_lt : 1 + j < n := by omega
        have hnotD : (σ ^ (1 + j)) d ≠ d := hbeforeD _ hj1_pos hj1_lt
        have hnotE : (σ ^ (1 + j)) d ≠ e := hbeforeE _ hj1_lt
        have hzero := hz (1 + j) hnotD hnotE
        have hstep : b (σ ((σ ^ (1 + j)) d)) = b ((σ ^ (1 + j)) d) := by
          symm
          simpa only [ZModModule.neg_eq_self] using eq_neg_of_add_eq_zero_left hzero
        have hpow :
            (σ ^ (1 + Nat.succ j)) d = σ ((σ ^ (1 + j)) d) := by
          simp only [Nat.succ_eq_add_one]
          rw [show 1 + (j + 1) = (1 + j) + 1 by omega, pow_succ']
          rfl
        calc
          b ((σ ^ (1 + Nat.succ j)) d) = b (σ ((σ ^ (1 + j)) d)) :=
            congrArg b hpow
          _ = b ((σ ^ (1 + j)) d) := hstep
          _ = b (σ d) := ih (by omega) (by omega)
  have hend : b e = b (σ d) := by
    rw [← hn]
    exact hconstant n (Nat.succ_le_iff.mpr hnpos) le_rfl
  intro hde
  have heq : b d = b (σ d) := hde.trans hend
  rw [heq] at hd
  have hzeroOne : (0 : ZMod 2) = 1 := by
    simpa only [ZModModule.add_self] using hd
  exact zero_ne_one hzeroOne

/-! ## A cycle forced by two occurrences in one deleted component -/

theorem exists_cycle_of_componentAfterDelete_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : G.RotationSystem} {base : G.Dart} {c : V}
    (q q' : FacialOccurrence r base c) (hne : q ≠ q')
    (hcomp : componentAfterDelete q = componentAfterDelete q') :
    ∃ C : G.Walk c c, C.IsCycle ∧
      ∀ f : G.Dart, f.fst = c →
        (f.edge ∈ C.edges ↔ f = q.1.1 ∨ f = q'.1.1) := by
  classical
  have hdart_ne : q.1.1 ≠ q'.1.1 := by
    intro h
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  change
    (induceAway G c).connectedComponentMk (occurrenceTargetAway q) =
      (induceAway G c).connectedComponentMk (occurrenceTargetAway q') at hcomp
  have hreach : (induceAway G c).Reachable
      (occurrenceTargetAway q) (occurrenceTargetAway q') :=
    SimpleGraph.ConnectedComponent.exact hcomp
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  let ι : induceAway G c ↪g G :=
    SimpleGraph.Embedding.induce (G := G) {v : V | v ≠ c}
  let pG : G.Walk q.1.1.snd q'.1.1.snd := p.map ι.toHom
  have hpG : pG.IsPath := by
    exact p.map_isPath_of_injective ι.injective hp
  have hpG_support :
      pG.support = p.support.map (fun x : Away V c => (x : V)) := by
    change (p.map ι.toHom).support = _
    rw [Walk.support_map]
    rfl
  have hcnot : c ∉ pG.support := by
    intro hc
    rw [hpG_support, List.mem_map] at hc
    rcases hc with ⟨x, _hx, hxc⟩
    exact x.property hxc
  let tail : G.Walk q.1.1.snd q.1.1.fst :=
    (pG.concat q'.1.1.symm.adj).copy rfl (q'.2.trans q.2.symm)
  have htail : tail.IsPath := by
    have hend_not : q'.1.1.fst ∉ pG.support := by
      intro hmem
      apply hcnot
      exact (congrArg (fun x => x ∈ pG.support) q'.2).mp hmem
    have := hpG.concat hend_not q'.1.1.symm.adj
    simpa only [tail, Walk.isPath_copy] using this
  have hedge_ne : q.1.1.edge ≠ q'.1.1.edge := by
    intro hedge
    exact hdart_ne (dart_eq_of_edge_eq_of_fst_eq
      (q.2.trans q'.2.symm) hedge)
  have hedge_not_pG : q.1.1.edge ∉ pG.edges := by
    intro hedge
    apply hcnot
    exact (congrArg (fun x => x ∈ pG.support) q.2).mp
      (pG.fst_mem_support_of_mem_edges hedge)
  have hedge_not_tail : q.1.1.edge ∉ tail.edges := by
    simp only [tail, Walk.edges_copy, Walk.edges_concat]
    rw [List.concat_eq_append]
    change q.1.1.edge ∉ pG.edges ++ [q'.1.1.symm.edge]
    rw [List.mem_append, List.mem_singleton, q'.1.1.edge_symm, not_or]
    exact ⟨hedge_not_pG, hedge_ne⟩
  let C0 : G.Walk q.1.1.fst q.1.1.fst :=
    Walk.cons q.1.1.adj tail
  have hC0 : C0.IsCycle := by
    apply (Walk.cons_isCycle_iff tail q.1.1.adj).mpr
    exact ⟨htail, hedge_not_tail⟩
  let C : G.Walk c c := C0.copy q.2 q.2
  have hC : C.IsCycle := by
    simpa only [C, Walk.isCycle_copy] using hC0
  refine ⟨C, hC, ?_⟩
  intro f hf
  have hf_not_pG : f.edge ∉ pG.edges := by
    intro hedge
    apply hcnot
    exact (congrArg (fun x => x ∈ pG.support) hf).mp
      (pG.fst_mem_support_of_mem_edges hedge)
  have hfd : f.edge = q.1.1.edge ↔ f = q.1.1 := by
    constructor
    · exact dart_eq_of_edge_eq_of_fst_eq (hf.trans q.2.symm)
    · exact fun h => congrArg SimpleGraph.Dart.edge h
  have hfe : f.edge = q'.1.1.edge ↔ f = q'.1.1 := by
    constructor
    · exact dart_eq_of_edge_eq_of_fst_eq (hf.trans q'.2.symm)
    · exact fun h => congrArg SimpleGraph.Dart.edge h
  have hCedges : C.edges = q.1.1.edge :: (pG.edges ++ [q'.1.1.edge]) := by
    have hdedge : s(q.1.1.fst, q.1.1.snd) = q.1.1.edge := rfl
    have heedge : s(q'.1.1.snd, q'.1.1.fst) = q'.1.1.edge :=
      q'.1.1.edge_symm
    simp [C, C0, tail, List.concat_eq_append, hdedge, heedge]
  rw [hCedges]
  simp only [List.mem_cons, List.mem_append]
  rw [hfd, hfe]
  simp [hf_not_pG]

/-! ## Facial occurrences separate in a faithful plane map -/

open PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open PlaneTopology.Faces.FaceBoundaryAlgebra

/-- Distinct occurrences of one vertex on one face of a connected plane map
land in distinct connected components after deleting that vertex.  The proof
is algebraic: a path in a purported common component closes to a cycle whose
face-boundary potential toggles at exactly the two occurrences.  Equal face
indices at those occurrences contradict the parity of that vertex-rotation
cycle. -/
theorem componentAfterDelete_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : ConnectedPlaneMap G) (base : G.Dart) (c : V) :
    Function.Injective
      (componentAfterDelete
        (K := G) (r := M.rawRotation) (base := base) (c := c)) := by
  classical
  intro q q' hcomp
  by_contra hne
  have hdart_ne : q.1.1 ≠ q'.1.1 := by
    intro h
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  obtain ⟨C, hC, hinc⟩ :=
    exists_cycle_of_componentAfterDelete_eq q q' hne hcomp
  have hcycleVector : Walk.edgeVector G C ∈ G.CycleSpace :=
    Walk.edgeVector_mem_cycleSpace (G := G) hC
  rw [← range_faceBoundary_eq_cycleSpace M] at hcycleVector
  rcases hcycleVector with ⟨a, ha⟩
  let potential : G.Dart → ZMod 2 :=
    fun d => a (faceIndex M.rawRotation d)
  let dq : G.edgeFinset :=
    ⟨q.1.1.edge, G.mem_edgeFinset.mpr q.1.1.edge_mem⟩
  have hd_mem_edges : q.1.1.edge ∈ C.edges :=
    (hinc q.1.1 q.2).mpr (Or.inl rfl)
  have hd_mem_finset : dq ∈ Walk.edgeFinset G C :=
    (Walk.mem_edgeFinset (G := G) C dq).mpr hd_mem_edges
  have hd_coordinate : Walk.edgeVector G C dq = 1 := by
    simp [Walk.edgeVector, SimpleGraph.edgeIndicator, hd_mem_finset]
  have hd_sum :
      a (faceIndex M.rawRotation q.1.1) +
          a (faceIndex M.rawRotation q.1.1.symm) = 1 := by
    calc
      _ = faceBoundary M.rawRotation a dq :=
        (faceBoundary_eq_dart_sum M.rawRotation a q.1.1).symm
      _ = Walk.edgeVector G C dq := by rw [ha]
      _ = 1 := hd_coordinate
  have hd_toggle :
      potential q.1.1 + potential (M.rawRotation.σ q.1.1) = 1 := by
    unfold potential
    rw [faceIndex_sigma_eq_symm]
    exact hd_sum
  have hsource_pow : ∀ k : ℕ,
      ((M.rawRotation.σ ^ k) q.1.1).fst = c := by
    intro k
    induction k with
    | zero => simpa using q.2
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (M.rawRotation.σ_source _).trans ih
  have hzero : ∀ k : ℕ,
      (M.rawRotation.σ ^ k) q.1.1 ≠ q.1.1 →
      (M.rawRotation.σ ^ k) q.1.1 ≠ q'.1.1 →
      potential ((M.rawRotation.σ ^ k) q.1.1) +
          potential (M.rawRotation.σ ((M.rawRotation.σ ^ k) q.1.1)) = 0 := by
    intro k hnotq hnotq'
    let x : G.Dart := (M.rawRotation.σ ^ k) q.1.1
    have hxsource : x.fst = c := hsource_pow k
    let ex : G.edgeFinset :=
      ⟨x.edge, G.mem_edgeFinset.mpr x.edge_mem⟩
    have hx_not_edges : x.edge ∉ C.edges := by
      intro hx
      rcases (hinc x hxsource).mp hx with hxq | hxq'
      · exact hnotq hxq
      · exact hnotq' hxq'
    have hx_not_finset : ex ∉ Walk.edgeFinset G C := by
      intro hx
      exact hx_not_edges ((Walk.mem_edgeFinset (G := G) C ex).mp hx)
    have hx_coordinate : Walk.edgeVector G C ex = 0 := by
      simp [Walk.edgeVector, SimpleGraph.edgeIndicator, hx_not_finset]
    have hx_sum :
        a (faceIndex M.rawRotation x) +
            a (faceIndex M.rawRotation x.symm) = 0 := by
      calc
        _ = faceBoundary M.rawRotation a ex :=
          (faceBoundary_eq_dart_sum M.rawRotation a x).symm
        _ = Walk.edgeVector G C ex := by rw [ha]
        _ = 0 := hx_coordinate
    change potential x + potential (M.rawRotation.σ x) = 0
    unfold potential
    rw [faceIndex_sigma_eq_symm]
    exact hx_sum
  have hvertexCycle :
      M.rawRotation.σ.SameCycle q.1.1 q'.1.1 :=
    M.vertexDarts_sameCycle (q.2.trans q'.2.symm)
  have hsameFace : M.rawRotation.SameFace q.1.1 q'.1.1 :=
    M.rawRotation.sameFace_equivalence.trans
      (M.rawRotation.sameFace_equivalence.symm q.1.2) q'.1.2
  have hpotential_eq : potential q.1.1 = potential q'.1.1 := by
    unfold potential
    exact congrArg a
      ((faceIndex_eq_iff_sameFace M.rawRotation q.1.1 q'.1.1).mpr hsameFace)
  exact (value_ne_of_two_toggles M.rawRotation.σ hvertexCycle hdart_ne
    potential hd_toggle hzero) hpotential_eq

/-- Cardinal form of `FACIAL-OCCURRENCE` for a supplied faithful connected
plane map. -/
theorem card_facialOccurrence_le_components_of_planeMap
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : ConnectedPlaneMap G) (base : G.Dart) (c : V) :
    Nat.card (FacialOccurrence M.rawRotation base c) ≤
      Nat.card (induceAway G c).ConnectedComponent :=
  card_facialOccurrence_le_components
    (componentAfterDelete_injective M base c)

/-! ## Feeding facial separation into LOCAL-OCC -/

open PlaneTopology.Faces.FourContactLocalOccurrence

/-- Stable decidability for the induced graph used as the deletion map's
vertex type. -/
noncomputable instance induceAwayDecidableAdj
    {V : Type*} (G : SimpleGraph V) (d : V) :
    DecidableRel (induceAway G d).Adj :=
  Classical.decRel _

/-- For a faithful connected plane map of `G-d`, the component-injection
input of LOCAL-OCC is automatic.  The only remaining geometric input at this
layer is planarity of the concrete port graph. -/
theorem localOccurrenceAt_of_planeMap_facialFourPorts
    {V X P : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V)
    [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P]
    (M : ConnectedPlaneMap (induceAway G d))
    (base : (induceAway G d).Dart)
    (S : PlaneTopology.Faces.FacialOccurrence.FacialPorts.FacialFourPortSystem
      G d M.rawRotation base X P)
    (hplanar : S.incidence.portGraph.IsPlanar) :
    3 * Fintype.card X ≤
      PlaneTopology.Faces.FourContactLedger.GraphLedger.neighborComponentSum G d := by
  exact PlaneTopology.Faces.FacialOccurrence.FacialPorts.localOccurrenceAt_of_facialFourPorts
    G d M.rawRotation base S hplanar
      (fun c hadj => componentAfterDelete_injective M base
        (PlaneTopology.Faces.FacialOccurrence.IteratedDeletion.awayVertex
          d c hadj.ne.symm))

/-- Owner-wise geometric data after eliminating the redundant manual
component embeddings.  The port type and the plane map of `G-d` may depend on
the owner. -/
structure OwnerFacialFourCertificate
    {V X : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (marked : Finset X) (ownerMap : X → V) (d : V) where
  Port : Type
  [portFintype : Fintype Port]
  [portDecidableEq : DecidableEq Port]
  planeMap : ConnectedPlaneMap (induceAway G d)
  base : (induceAway G d).Dart
  system : PlaneTopology.Faces.FacialOccurrence.FacialPorts.FacialFourPortSystem
    G d planeMap.rawRotation base
      (PlaneTopology.Faces.FourContactLocalOccurrence.OwnerFiber marked ownerMap d) Port
  portGraph_planar : system.incidence.portGraph.IsPlanar

namespace OwnerFacialFourCertificate

variable {V X : Type*} [Fintype V] [DecidableEq V] [DecidableEq X]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (marked : Finset X) (ownerMap : X → V)

/-- The faithful facial certificates give the graph-valued LOCAL-OCC
predicate without any separately supplied port/component injection. -/
theorem localOccurrenceFour_of_facialCertificates
    (cert : ∀ d, OwnerFacialFourCertificate G marked ownerMap d) :
    PlaneTopology.Faces.FourContactLedger.GraphLedger.LocalOccurrenceFour G
      (fun d => PlaneTopology.Faces.FourContactLedger.OwnerPartition.markedFiberCount
        marked ownerMap d) := by
  intro d
  let C := cert d
  letI : Fintype C.Port := C.portFintype
  letI : DecidableEq C.Port := C.portDecidableEq
  have h := localOccurrenceAt_of_planeMap_facialFourPorts
    G d C.planeMap C.base C.system C.portGraph_planar
  simpa [PlaneTopology.Faces.FourContactLocalOccurrence.OwnerFiber,
    PlaneTopology.Faces.FourContactLedger.OwnerPartition.markedFiberCount] using h

/-- End-to-end planar two-connected four-contact bound from faithful facial
port certificates.  SPLIT-DEFICIT and facial occurrence separation are both
proved internally. -/
theorem planar_twoConnected_markedSet_bound_of_facialCertificates
    (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V)
    (htwo : G.IsKConnected 2)
    (cert : ∀ d, OwnerFacialFourCertificate G marked ownerMap d) :
    marked.card ≤ 2 * Fintype.card V - 4 := by
  exact PlaneTopology.Faces.FourContactLedger.GraphLedger.planar_twoConnected_markedSet_bound
    G marked ownerMap hG hcard htwo
      (localOccurrenceFour_of_facialCertificates G marked ownerMap cert)

end OwnerFacialFourCertificate

#print axioms componentAfterDelete_injective
#print axioms card_facialOccurrence_le_components_of_planeMap
#print axioms localOccurrenceAt_of_planeMap_facialFourPorts
#print axioms OwnerFacialFourCertificate.localOccurrenceFour_of_facialCertificates
#print axioms OwnerFacialFourCertificate.planar_twoConnected_markedSet_bound_of_facialCertificates

end PlaneTopology.Faces.FacialSeparation
