import GraphTheory.Plane.PlaneFanArcRetention

/-!
# Two actual noncrossing apex fans in one old face

A first fan retains an attachment-free old boundary gap. One common face
contains the first apex and every vertex of that closed gap; the second fan
is then inserted into this actual face, including the edge between the apices.
-/

namespace PlaneTopology.PlaneTwoFans

open SimpleGraph Equiv Equiv.Perm PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlanePermutationSurgery PlaneTopology.PlaneLeafInsertion PlaneTopology.PlaneChordFaces
open PlaneTopology.PlaneFanInsertion PlaneTopology.PlaneFanArcRetention

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Leaf insertion leaves each old facial step unchanged unless that step
enters the attachment vertex. -/
theorem leafRotation_facePerm_old (r : G.RotationSystem) (v : V)
    (d : G.Dart) (hd : d.fst = v) (x : G.Dart) (hx : x.snd ≠ v) :
    (leafRotation G v r d hd).facePerm (leafDart G v (Sum.inl x)) =
      leafDart G v (Sum.inl (r.facePerm x)) := by
  have hxd : r.facePerm x ≠ d := by
    intro h
    apply hx
    rw [← r.facePerm_source x, h, hd]
  change (leafRotation G v r d hd).facePerm (leafDartEquiv G v (Sum.inl x)) = _
  rw [leafRotation_facePerm, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change leafDart G v (leafFacePerm G r d (Sum.inl x)) = _
  change r.σ x.symm ≠ d at hxd
  simp [leafFacePerm, mul_apply, Equiv.swap_apply_def, hxd]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Literal old facial iterates remain unchanged along an arc avoiding the
leaf attachment internally. -/
theorem leafRotation_facePerm_pow_old (r : G.RotationSystem) (v : V)
    (d : G.Dart) (hd : d.fst = v) (x : G.Dart) (n : ℕ)
    (havoid : ∀ i < n, ((r.facePerm ^ i) x).snd ≠ v) :
    ((leafRotation G v r d hd).facePerm ^ n) (leafDart G v (Sum.inl x)) =
      leafDart G v (Sum.inl ((r.facePerm ^ n) x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply, ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))]
    simpa only [pow_succ', mul_apply] using
      leafRotation_facePerm_old G r v d hd ((r.facePerm ^ n) x)
        (havoid n (Nat.lt_succ_self n))

/-- Construct the first actual apex fan with one common face containing the
apex and an entire protected old arc, including both endpoint vertices. -/
theorem exists_apexPlaneMap_commonFace_arc (M : ConnectedPlaneMap G) (X : Finset V)
    (v : V) (hv : v ∈ X) (d : G.Dart) (hd : d.fst = v)
    (hX : ∀ x ∈ X, ∃ e : G.Dart, e.fst = x ∧ M.rawRotation.SameFace d e)
    (n : ℕ) (havoid : ∀ i < n, ((M.rawRotation.facePerm ^ i) d).snd ∉ X) :
    ∃ N : ConnectedPlaneMap (apexGraph G X),
      ∃ a : (apexGraph G X).Dart, a.fst = none ∧
        ∀ i ≤ n, ∃ b t : (apexGraph G X).Dart,
          b.fst = some ((M.rawRotation.facePerm ^ i) d).fst ∧
          t.fst = some ((M.rawRotation.facePerm ^ i) d).snd ∧
          N.rawRotation.SameFace a b ∧ N.rawRotation.SameFace a t := by
  classical
  let L := leafPlaneMapAt G v M d hd
  let T := X.image some
  have hco (x : Option V) (hx : x ∈ T) : CoFacial (leafGraph G v) L.rawRotation none x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he, hface⟩ := hX y hy
    refine ⟨leafDart G v (Sum.inr true), leafDart G v (Sum.inl e), rfl,
      congrArg some he, ?_⟩
    exact leafRotation_sameFace_leaf G v M.rawRotation d hd e hface
  let c := leafDart G v (Sum.inr true)
  let x := leafDart G v (Sum.inl d)
  have hcx : L.rawRotation.SameFace c x :=
    leafRotation_sameFace_leaf G v M.rawRotation d hd d (SameCycle.refl _ _)
  have hpow (i : ℕ) (hi : i ≤ n) :
      (L.rawRotation.facePerm ^ i) x = leafDart G v (Sum.inl ((M.rawRotation.facePerm ^ i) d)) := by
    exact leafRotation_facePerm_pow_old G M.rawRotation v d hd d i
      (fun j hj h => havoid j (Nat.lt_of_lt_of_le hj hi) (h ▸ hv))
  have hguard (i : ℕ) (hi : i < n) :
      ((L.rawRotation.facePerm ^ i) x).snd ≠ none ∧
        ((L.rawRotation.facePerm ^ i) x).snd ∉ T := by
    rw [hpow i (Nat.le_of_lt hi)]
    exact ⟨by simp [leafDart], by simpa [leafDart, T] using havoid i hi⟩
  let N₀ := retainedFanPlaneMap (leafGraph G v) L none T hco
  obtain ⟨a, ha, harc⟩ := retainedFanPlaneMap_commonFace_arc
    (leafGraph G v) L none T hco c x rfl hcx n hguard
  have hgraph : fanGraph (leafGraph G v) none T = apexGraph G X :=
    fan_leafGraph_eq_apexGraph G X v hv
  refine ⟨castPlaneMap hgraph N₀, castDart hgraph a, ?_, ?_⟩
  · exact (congrArg Prod.fst (castDart_toProd hgraph a)).trans ha
  · intro i hi
    obtain ⟨b, t, hb, ht, hab, hat⟩ := harc i hi
    refine ⟨castDart hgraph b, castDart hgraph t, ?_, ?_,
      castPlaneMap_sameFace hgraph N₀ a b hab, castPlaneMap_sameFace hgraph N₀ a t hat⟩
    · rw [hpow i hi] at hb
      exact (congrArg Prod.fst (castDart_toProd hgraph b)).trans hb
    · rw [hpow i hi] at ht
      exact (congrArg Prod.fst (castDart_toProd hgraph t)).trans ht

/-- Exact graph with two fresh adjacent apices: the first has old neighbors
`X`, and the second has old neighbors `Y`, with no other added edge. -/
def twoFanGraph (X Y : Finset V) : SimpleGraph (Option (Option V)) :=
  apexGraph (apexGraph G X) (insert none (Y.image some))

instance twoFanGraphDecidableRel (X Y : Finset V) :
    DecidableRel (twoFanGraph G X Y).Adj := by
  unfold twoFanGraph
  infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- No old edge is changed by the two-fan construction. -/
theorem twoFanGraph_old_adj (X Y : Finset V) (v w : V) :
    (twoFanGraph G X Y).Adj (some (some v)) (some (some w)) ↔ G.Adj v w := Iff.rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- The first apex has exactly the requested old neighbors. -/
theorem twoFanGraph_first_adj (X Y : Finset V) (v : V) :
    (twoFanGraph G X Y).Adj (some none) (some (some v)) ↔ v ∈ X := Iff.rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- The second apex has exactly the requested old neighbors. -/
theorem twoFanGraph_second_adj (X Y : Finset V) (v : V) :
    (twoFanGraph G X Y).Adj none (some (some v)) ↔ v ∈ Y := by
  simp [twoFanGraph, apexGraph]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The two fresh apices are genuinely adjacent in the output graph. -/
theorem twoFanGraph_apices_adj (X Y : Finset V) :
    (twoFanGraph G X Y).Adj none (some none) := by
  simp [twoFanGraph, apexGraph]

/-- **Actual two-fan construction.** All second-apex attachment vertices
lie on one closed first-fan-free old arc. The inter-apex edge is included
in the output graph, not introduced as a later assumption. -/
theorem exists_twoFanPlaneMap (M : ConnectedPlaneMap G) (X Y : Finset V)
    (v : V) (hv : v ∈ X) (d : G.Dart) (hd : d.fst = v)
    (hX : ∀ x ∈ X, ∃ e : G.Dart, e.fst = x ∧ M.rawRotation.SameFace d e)
    (n : ℕ) (havoid : ∀ i < n, ((M.rawRotation.facePerm ^ i) d).snd ∉ X)
    (hY : ∀ y ∈ Y, ∃ i ≤ n,
      y = ((M.rawRotation.facePerm ^ i) d).fst ∨
        y = ((M.rawRotation.facePerm ^ i) d).snd) :
    Nonempty (ConnectedPlaneMap (twoFanGraph G X Y)) := by
  classical
  obtain ⟨N, a, ha, harc⟩ := exists_apexPlaneMap_commonFace_arc G M X v hv d hd hX n havoid
  let T := insert none (Y.image some)
  have hT (z : Option V) (hz : z ∈ T) :
      ∃ e : (apexGraph G X).Dart, e.fst = z ∧ N.rawRotation.SameFace a e := by
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact ⟨a, ha, SameCycle.refl _ _⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i, hi, hiy⟩ := hY y hy
      obtain ⟨b, t, hb, ht, hab, hat⟩ := harc i hi
      rcases hiy with hiy | hiy
      · exact ⟨b, hb.trans (congrArg some hiy.symm), hab⟩
      · exact ⟨t, ht.trans (congrArg some hiy.symm), hat⟩
  exact exists_apexPlaneMap (apexGraph G X) N T none (Finset.mem_insert_self _ _) a ha hT

/-- A chosen real sphere map of the exact adjacent-two-apex graph. -/
noncomputable def twoFanPlaneMap (M : ConnectedPlaneMap G) (X Y : Finset V)
    (v : V) (hv : v ∈ X) (d : G.Dart) (hd : d.fst = v)
    (hX : ∀ x ∈ X, ∃ e : G.Dart, e.fst = x ∧ M.rawRotation.SameFace d e)
    (n : ℕ) (havoid : ∀ i < n, ((M.rawRotation.facePerm ^ i) d).snd ∉ X)
    (hY : ∀ y ∈ Y, ∃ i ≤ n,
      y = ((M.rawRotation.facePerm ^ i) d).fst ∨
        y = ((M.rawRotation.facePerm ^ i) d).snd) :
    ConnectedPlaneMap (twoFanGraph G X Y) :=
  (exists_twoFanPlaneMap G M X Y v hv d hd hX n havoid hY).some

#print axioms exists_apexPlaneMap_commonFace_arc
#print axioms twoFanPlaneMap

end PlaneTopology.PlaneTwoFans
