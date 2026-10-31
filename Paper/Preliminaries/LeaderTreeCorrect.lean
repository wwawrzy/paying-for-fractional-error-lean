import Paper.Preliminaries.LeaderTree

/-! A derived specification of the actual composed program. The fields
below are proved from its execution, not supplied as a construction oracle. -/
namespace Paper.LeaderTreeCorrect
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Spec (G : SimpleGraph V) (A : V → Bool) (D : ℕ) (root : V)
    (out : V → ParentElection.Node V D) : Prop where
  active : ∀ v, (out v).active = A v
  root_parent : (out root).parent = none
  root_rank : (out root).rank.val = 0
  inactive : ∀ v, A v = false → (out v).parent = none
  rank_bound : ∀ v, A v = true → (out v).rank.val ≤ D
  parent_edge : ∀ v u, (out v).parent = some u → G.Adj v u
  parent_active : ∀ v u, (out v).parent = some u → A v = true ∧ A u = true
  parent_rank : ∀ v u, (out v).parent = some u → (out u).rank.val < (out v).rank.val
  parent_exists : ∀ v, A v = true → v ≠ root → ∃ u, (out v).parent = some u

theorem Spec.acyclic {G : SimpleGraph V} {A : V → Bool} {D : ℕ} {root : V}
    {out : V → ParentElection.Node V D} (h : Spec G A D root out) :
    (ParentForest.graph (fun v => (out v).parent) (fun v => (out v).rank.val) h.parent_rank).IsAcyclic :=
  ParentForest.isAcyclic _ _ _

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : V → Bool)

theorem correct {b : ℕ} (C : BitCode V b) (D : ℕ) (root : V)
    (har : A root = true) (hmin : ∀ v, A v = true → root ≤ v)
    (hdiam : ∀ v, A v = true → ∃ p : G.Walk v root,
      p.length ≤ D ∧ ∀ z ∈ p.support, A z = true) :
    Spec G A D root ((LeaderTree.program C D).run G A) := by
  rw [LeaderTree.run_eq G A C D root har hmin hdiam]
  let B : V → Bool := fun v => A v && decide (v = root)
  have hbr : B root = true := LeaderTree.source_root A root har
  have hb : ∀ u, B u = true → u = root := fun _ h => LeaderTree.source_unique A root h
  refine ⟨fun v => (DistanceTree.metadata G D A B v).1,
    DistanceTree.root_parent G D A B root har hbr, ?_,
    fun _ h => DistanceTree.inactive G D A B h,
    fun _ h => DistanceTree.rank_bound G D A B root hbr hdiam h,
    fun _ _ h => (DistanceTree.parent_mem G D A B h).2.1,
    fun _ _ h => ⟨(DistanceTree.parent_mem G D A B h).1,
      DistanceTree.parent_active G D A B root hbr hdiam h⟩,
    fun _ _ h => (DistanceTree.parent_mem G D A B h).2.2,
    fun _ h hv => DistanceTree.exists_parent G D A B root hbr hb hdiam h hv⟩
  rw [(DistanceTree.metadata G D A B root).2]
  exact MaskedDistance.source_zero G D A B D har hbr
end Paper.LeaderTreeCorrect
