import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepairUnion

/-! Exact local replay of the entire repair union event. The graph and global
coins below occur only in the correctness proof. Runtime uses the received
finite records, one shared local seed list, and the actual repair observer. -/
namespace Paper.GeneralCoveringOwnerRepairUnionNative
open BroadcastModel SevenFoundation NeighborBalls
open GeneralCoveringOwnerFramePartition GeneralCoveringOwnerRepairUnion
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C targets : V → Finset V) (D R : Finset V) (L Δ r k t b n : ℕ)
variable (hr : GeneralCoveringOwnerFramePartition.radius k n ≤ r)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u)
variable (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D))
variable (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v)
variable (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets

local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q
noncomputable local instance publicAdj : DecidableRel (SimpleGraph.Adj J) := fun _ _ => Classical.propDecidable _

def source {ids : ℕ} (I : BitCode V ids) (v : V) :=
  (GeneralCoveringOwnerRootFrames.program I L Δ r).runEncoded G input v

def observed {ids : ℕ} (I : BitCode V ids) (v : V) :=
  (GeneralCoveringOwnerRepairObserver.core I).runEncoded G
    (GeneralCoveringOwnerRepairFrames.environments G L Δ r input I) v

theorem window_true {ids : ℕ} (I : BitCode V ids) (v : V) :
    ∀ a ∈ window (source G L Δ r input I v), a.2.val.toFinset = SimpleGraph.neighborFinset J a.1 := by
  intro a ha
  exact RootFrameUnion.records_true (GeneralCoveringOwnerRoleFrames.received G I L Δ r input v)
    (fun w => SimpleGraph.neighborFinset J w)
    (GeneralCoveringOwnerRoleFrames.frame_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets I v) a ha

theorem window_keys {ids : ℕ} (I : BitCode V ids) (v : V) :
    TaggedDictionary.keys (window (source G L Δ r input I v)) =
      (TaggedDictionary.keys (source G L Δ r input I v).roots.val).biUnion
        (fun u => ball (fun w => SimpleGraph.neighborFinset J w) u r) :=
  RootFrameUnion.keys_records _ _
    (GeneralCoveringOwnerRoleFrames.frame_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets I v)

theorem window_low {ids : ℕ} (I : BitCode V ids) (v : V) :
    TaggedDictionary.keys (window (source G L Δ r input I v)) ⊆ U := by
  rw [window_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets I v]
  intro w hw
  obtain ⟨u, hu, hw⟩ := Finset.mem_biUnion.mp hw
  have hroot := GeneralCoveringOwnerRoleFrames.roots_low G C targets D R L Δ r
    hinc hlocal input hD hR hC hTargets I v hu
  exact GeneralCoveringOwnerRoleFrames.ball_low G C targets D R L Δ
    hinc hlocal input hD hR hC hTargets u hroot r hw

include hr in
theorem window_cover {ids : ℕ} (I : BitCode V ids) (v u : V)
    (hu : u ∈ (observed G L Δ r input I v).roots) :
    ball (fun w => SimpleGraph.neighborFinset J w) u (ActiveFiniteBitPartition.program I Δ k t b n).rounds ⊆
      TaggedDictionary.keys (window (source G L Δ r input I v)) := by
  have hroot := GeneralCoveringOwnerRepairFrames.roots_subset G C targets D R L Δ r
    hinc hlocal input hD hR hC hTargets I v hu
  exact RootFrameUnion.subball_coverage _ _
    (GeneralCoveringOwnerRoleFrames.frame_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets I v)
    0 _ (by rw [ActiveFiniteBitPartition.rounds]; simpa only [Nat.zero_add] using hr) u u hroot (self_mem _ u 0)

include hr in
theorem boundary_base {ids : ℕ} (I : BitCode V ids) (v u : V)
    (hu : u ∈ (observed G L Δ r input I v).roots) (β : V → Bits Δ k b n) :
    boundary I Δ k t b n (window (source G L Δ r input I v))
      (LocalSeedRecords.base (addresses (window (source G L Δ r input I v)))
        (fun i => β ((addresses (window (source G L Δ r input I v))).get i))) u =
      ((ActiveFiniteBitPartition.program I Δ k t b n).runEncoded J
        (fun w => (decide (w ∈ U), β w)) u).2 := by
  let xs := window (source G L Δ r input I v)
  let l := addresses xs
  let σ := fun w => (decide (w ∈ U), β w)
  have hs : seeds Δ k b n (LocalSeedRecords.base l (fun i => β (l.get i))) =
      LocalSeedRecords.base l (fun i => σ (l.get i)) := by
    unfold seeds LocalSeedRecords.base
    rw [List.map_ofFn]
    congr 1
    funext i
    have hi : l.get i ∈ TaggedDictionary.keys xs := (Finset.mem_sort (· ≤ ·)).mp (l.get_mem i)
    have hl := window_low G C targets D R L Δ r hinc hlocal input hD hR hC hTargets I v hi
    exact Prod.ext rfl (Prod.ext (decide_eq_true hl).symm rfl)
  have hc := window_cover G C targets D R L Δ r k t b n hr hinc hlocal input hD hR hC hTargets I v u hu
  have hl : ball (fun w => SimpleGraph.neighborFinset J w) u (ActiveFiniteBitPartition.program I Δ k t b n).rounds ⊆
      l.toFinset := by simpa only [l, xs, addresses, Finset.sort_toFinset] using hc
  change (FrameInterpreter.evaluate (ActiveFiniteBitPartition.program I Δ k t b n) xs _ _ u).2 = _
  rw [hs]
  exact congrArg Prod.snd ((LocalSeedRecords.evaluate_base J (ActiveFiniteBitPartition.program I Δ k t b n)
    xs l σ (true, zeroBits Δ k b n) u
    (window_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets I v) hc hl).trans
      (congrFun (Program.runEncoded_eq_run J (ActiveFiniteBitPartition.program I Δ k t b n) σ) u).symm)

include hr in
theorem event_base {ids : ℕ} (I : BitCode V ids) (v : V) (β : V → Bits Δ k b n) :
    event I k t b n (source G L Δ r input I v) (observed G L Δ r input I v)
      (LocalSeedRecords.base (addresses (window (source G L Δ r input I v)))
        (fun i => β ((addresses (window (source G L Δ r input I v))).get i))) =
      if GeneralCoveringOwnerRepairObserver.evaluate (observed G L Δ r input I v).fixed
          (observed G L Δ r input I v).roots (fun u =>
            ((ActiveFiniteBitPartition.program I Δ k t b n).runEncoded J
              (fun w => (decide (w ∈ U), β w)) u).2) then 1 else 0 := by
  unfold event
  apply congrArg (fun flag : Bool => if flag then (1 : ℕ) else 0)
  apply Bool.eq_iff_iff.mpr
  simp only [GeneralCoveringOwnerRepairObserver.evaluate_iff]
  apply or_congr Iff.rfl
  apply exists_congr
  intro u
  apply and_congr_right
  intro hu
  rw [boundary_base G C targets D R L Δ r k t b n hr hinc hlocal input hD hR hC hTargets I v u hu β]

include hr in
theorem event_selected {ids : ℕ} (I : BitCode V ids) (v : V) (β : V → Bits Δ k b n) :
    event I k t b n (source G L Δ r input I v) (observed G L Δ r input I v)
      (LocalSeedRecords.base (addresses (window (source G L Δ r input I v)))
        (fun i => β ((addresses (window (source G L Δ r input I v))).get i))) =
      if ((GeneralCoveringOwnerRepair.core I).runEncoded G (fun u =>
        let E := GeneralCoveringOwnerRepairFrames.environments G L Δ r input I u
        ⟨E, E.high || (E.low && ((ActiveFiniteBitPartition.program I Δ k t b n).runEncoded J
          (fun w => (decide (w ∈ U), β w)) u).2)⟩) v).selected then 1 else 0 := by
  rw [event_base G C targets D R L Δ r k t b n hr hinc hlocal input hD hR hC hTargets I v β]
  rw [GeneralCoveringOwnerRepairObserver.core_selected]
  rfl

include hr in
/-- A literal local finite count divided by its public padded denominator
is the exact mean of the accepted physical repair core, with actual Env
and actual partition boundary outputs for every global coin assignment. -/
theorem selected_mean {ids : ℕ} (I : BitCode V ids) (v : V) :
    (count I k t b n (source G L Δ r input I v) (observed G L Δ r input I v) : ℝ) /
        denominator L Δ k b n r =
      (∑ β : V → Bits Δ k b n,
        ((if ((GeneralCoveringOwnerRepair.core I).runEncoded G (fun u =>
          let E := GeneralCoveringOwnerRepairFrames.environments G L Δ r input I u
          ⟨E, E.high || (E.low && ((ActiveFiniteBitPartition.program I Δ k t b n).runEncoded J
            (fun w => (decide (w ∈ U), β w)) u).2)⟩) v).selected then 1 else 0 : ℕ) : ℝ)) /
          Fintype.card (V → Bits Δ k b n) := by
  rw [GeneralCoveringOwnerRepairUnion.mean]
  congr 1
  apply Finset.sum_congr rfl
  intro β _
  exact congrArg Nat.cast
    (event_selected G C targets D R L Δ r k t b n hr hinc hlocal input hD hR hC hTargets I v β)

end Paper.GeneralCoveringOwnerRepairUnionNative

#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.window_true
#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.window_keys
#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.window_low
#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.window_cover
#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.boundary_base
#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.event_base
#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.event_selected
#print axioms Paper.GeneralCoveringOwnerRepairUnionNative.selected_mean
