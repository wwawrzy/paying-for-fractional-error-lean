import Paper.Solver.LocalSearch.GeneralCoveringOwnerRootFrames
import Paper.Preliminaries.RootFrameUnion
import Paper.Partitions.Local.NeighborBallGraph
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps

/-! Local role anchors and canonical frames from one actual-C RootFrames
execution. Generic RootFrameUnion is used only for finite record operations;
all root, owner and public-graph semantics come from the actual Option owners.
Partitions and connected task parts occur only in the analysis. -/
namespace Paper.GeneralCoveringOwnerRoleFrames
open BroadcastModel SevenFoundation NeighborBalls GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

/-- The legacy alias used by the structural union API is just bounded records. -/
theorem frame_type_compat (Δ r : ℕ) :
    GeneralCoveringOwnerRootFrames.Frame V Δ r = OwnerFramePayload.Frame V Δ r := rfl

def packets {L Δ r : ℕ} (z : GeneralCoveringOwnerRootFrames.Output V L Δ r) :
    List (V × OwnerFramePayload.Frame V Δ r) := z.roots.val

structure Output (V : Type) (L Δ r : ℕ) where
  anchors : Finset V
  frames : List (V × List (TopologyGather.Record V Δ))
  source : GeneralCoveringOwnerRootFrames.Output V L Δ r

def finish {L Δ r : ℕ} (k s : ℕ) (z : GeneralCoveringOwnerRootFrames.Output V L Δ r) : Output V L Δ r :=
  let xs := packets z
  let A := RootFrameUnion.anchors k xs
  ⟨A, A.sort.map (fun a => (a, RootFrameUnion.canonical s a xs)), z⟩

/-- One received producer, followed by local computation and no broadcast. -/
def program {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (Output V L Δ r) :=
  .seq (GeneralCoveringOwnerRootFrames.program ids L Δ r) (.local fun _ _ z => finish k s z)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem post_run {In X Y : Type} (P : Program V In X) (f : X → Y) (input : V → In) :
    (Program.seq P (Program.local fun _ _ z => f z)).runEncoded G input =
      fun v => f (P.runEncoded G input v) := rfl

theorem run_program {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ r k s).runEncoded G input = fun v =>
      finish k s ((GeneralCoveringOwnerRootFrames.program ids L Δ r).runEncoded G input v) :=
  post_run G _ _ input

def received {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) (input : V → GeneralCoveringOwners.Input V) (v : V) :=
  packets ((GeneralCoveringOwnerRootFrames.program ids L Δ r).runEncoded G input v)

def canonical {b : ℕ} (ids : BitCode V b) (L Δ r s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V) :=
  RootFrameUnion.canonical s a (received G ids L Δ r input v)

theorem env_retained {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).source.env =
      GeneralCoveringOwnerSimulation.learned G ids L Δ input v := by
  rw [run_program]
  exact GeneralCoveringOwnerRootFrames.env_retained G ids L Δ r input v

theorem private_input_retained {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).source.env.metadata.owned.input = input v := by
  rw [env_retained]
  exact GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v

theorem source_retained {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).source =
      (GeneralCoveringOwnerRootFrames.program ids L Δ r).runEncoded G input v := by
  rw [run_program] <;> rfl

theorem anchors_run {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).anchors =
      RootFrameUnion.anchors k (received G ids L Δ r input v) := by
  rw [run_program] <;> rfl

theorem frame_dictionary_keys {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    TaggedDictionary.keys ((program ids L Δ r k s).runEncoded G input v).frames =
      ((program ids L Δ r k s).runEncoded G input v).anchors := by
  rw [run_program]
  simp [finish, TaggedDictionary.keys, List.map_map, Function.comp_def]

theorem frame_dictionary_consistent {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    TaggedDictionary.Consistent (canonical G ids L Δ r s input v)
      ((program ids L Δ r k s).runEncoded G input v).frames := by
  intro p hp
  rw [run_program] at hp
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem frame_lookup {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors) :
    TaggedDictionary.lookup ((program ids L Δ r k s).runEncoded G input v).frames a =
      some (canonical G ids L Δ r s input v a) := by
  apply TaggedDictionary.lookup_correct _ _ (frame_dictionary_consistent G ids L Δ r k s input v)
  rw [frame_dictionary_keys]
  exact ha

theorem frame_dictionary_length {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).frames.length =
      ((program ids L Δ r k s).runEncoded G input v).anchors.card := by
  rw [run_program]
  simp only [finish, List.length_map, Finset.length_sort]

theorem empty_roots {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V)
    (hr : TaggedDictionary.keys (received G ids L Δ r input v) = ∅) :
    ((program ids L Δ r k s).runEncoded G input v).anchors = ∅ ∧
      ((program ids L Δ r k s).runEncoded G input v).frames = [] := by
  have ha : RootFrameUnion.anchors k (received G ids L Δ r input v) = ∅ := by
    simp only [RootFrameUnion.anchors, hr, Finset.biUnion_empty]
  rw [run_program]
  change RootFrameUnion.anchors k (received G ids L Δ r input v) = ∅ ∧
    (RootFrameUnion.anchors k (received G ids L Δ r input v)).sort.map
      (fun a => (a, canonical G ids L Δ r s input v a)) = []
  rw [ha]
  simp only [Finset.sort_empty, List.map_nil, and_self]

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Connected owner-part walks are mapped to the actual public embedding. -/
theorem part_ball (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (i j : Low D Q) (hi : i ∈ I) (hj : j ∈ I) :
    j.val.val ∈ ball (fun w => (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).neighborFinset w) i.val.val k := by
  let f : ((graph G C D R L Q).induce (I : Set (Low D Q))) →g
      GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q := {
    toFun := fun x => x.val.val.val
    map_rel' := by
      intro x y hxy
      exact (PublicEmbedding.adj_iff (graph G C D R L Q)
        (GeneralCoveringOwnerVirtualPrepare.embedding D Q) _ _).mpr ⟨x.val, y.val, hxy, rfl, rfl⟩ }
  obtain ⟨p, hp⟩ := (hI (⟨i, hi⟩ : ↥(I : Set (Low D Q))) ⟨j, hj⟩).exists_isPath
  have hlen : p.length < I.card := by
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hp.length_lt
  apply NeighborBallGraph.walk_mem _ (p.map f) k
  rw [SimpleGraph.Walk.length_map]
  omega

def partIds (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) : Finset V :=
  I.image (fun i => i.val.val)

theorem partIds_nonempty (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) (hi : I.Nonempty) :
    (partIds D Q I).Nonempty := by
  obtain ⟨i, hi⟩ := hi
  exact ⟨i.val.val, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

theorem part_nonempty (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected) : I.Nonempty := by
  obtain ⟨i⟩ := hI.nonempty
  exact ⟨i.val, i.property⟩

/-- A participant touches a genuine owner of I, by star or gated support. -/
theorem touches (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (v : V) (hv : v ∈ vertices G C D R L Q I) :
    ∃ i ∈ I, i.val.val ∈ GeneralCoveringOwnerRouteLabels.labels G C D R L v := by
  rcases Finset.mem_union.mp hv with hs | hc
  · obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hs
    exact ⟨i, hi, GeneralCoveringOwnerRouteLabels.owner_label G C D R L (Finset.mem_filter.mp hv).2⟩
  · obtain ⟨i, hi, hl⟩ := (Finset.mem_filter.mp hc).2
    exact ⟨i, hi, GeneralCoveringOwnerRouteLabels.lightSupport_subset G C D R L v hl⟩

section Correct
variable (C targets : V → Finset V) (D R : Finset V) (L Δ r k s : ℕ)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q

theorem root_keys {b : ℕ} (ids : BitCode V b) (v : V) :
    TaggedDictionary.keys (received G ids L Δ r input v) =
      GeneralCoveringOwnerRouteLabels.labels G C D R L v ∩ U :=
  GeneralCoveringOwnerRootFrames.keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v

theorem frame_keys {b : ℕ} (ids : BitCode V b) (v : V) :
    ∀ p ∈ received G ids L Δ r input v, TaggedDictionary.keys p.2.val =
      ball (fun w => SimpleGraph.neighborFinset J w) p.1 r := by
  intro p hp
  have he := GeneralCoveringOwnerRootFrames.consistent G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v p hp
  rw [he]
  exact GeneralCoveringOwnerRootFrames.frame_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids p.1

theorem frame_true {b : ℕ} (ids : BitCode V b) (v : V) :
    ∀ p ∈ received G ids L Δ r input v, ∀ a ∈ p.2.val,
      a.2.val.toFinset = SimpleGraph.neighborFinset J a.1 := by
  intro p hp a ha
  have he := GeneralCoveringOwnerRootFrames.consistent G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v p hp
  rw [he] at ha
  have ht := GeneralCoveringOwnerRootFrames.frame_record_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids p.1 a ha
  exact (congrArg List.toFinset ht).trans (Finset.sort_toFinset _ _)

theorem anchors_eq {b : ℕ} (ids : BitCode V b) (hk : k ≤ r) (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).anchors =
      (GeneralCoveringOwnerRouteLabels.labels G C D R L v ∩ U).biUnion
        (fun u => ball (fun w => SimpleGraph.neighborFinset J w) u k) := by
  rw [anchors_run, RootFrameUnion.anchors_eq _ _
    (frame_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v)
    (frame_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v) k hk,
    root_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]

omit hinc hlocal hD hR hC hTargets in
theorem root_count {b : ℕ} (ids : BitCode V b) (v : V) :
    (TaggedDictionary.keys (received G ids L Δ r input v)).card ≤ max 1 L := by
  have hkeys : (TaggedDictionary.keys (received G ids L Δ r input v)).card ≤
      (received G ids L Δ r input v).length := by
    simpa only [TaggedDictionary.keys, List.length_map] using
      List.toFinset_card_le ((received G ids L Δ r input v).map Prod.fst)
  exact hkeys.trans (GeneralCoveringOwnerRootFrames.root_capacity G ids L Δ r input v)

theorem anchors_card {b : ℕ} (ids : BitCode V b) (hk : k ≤ r) (v : V) :
    (((program ids L Δ r k s).runEncoded G input v).anchors).card ≤ max 1 L * (Δ + 1) ^ k := by
  rw [anchors_run, RootFrameUnion.anchors_eq _ _
    (frame_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v)
    (frame_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v) k hk]
  calc
    _ ≤ ∑ u ∈ TaggedDictionary.keys (received G ids L Δ r input v),
        (ball (fun w => SimpleGraph.neighborFinset J w) u k).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ TaggedDictionary.keys (received G ids L Δ r input v), (Δ + 1) ^ k :=
      Finset.sum_le_sum (fun u _ => NeighborBallGraph.graph_card_bound J Δ
        (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) u k)
    _ = (TaggedDictionary.keys (received G ids L Δ r input v)).card * (Δ + 1) ^ k := by
      simp only [Finset.sum_const_nat]
    _ ≤ _ := Nat.mul_le_mul_right _ (root_count G L Δ r input ids v)

theorem roots_low {b : ℕ} (ids : BitCode V b) (v : V) :
    TaggedDictionary.keys (received G ids L Δ r input v) ⊆ U := by
  rw [root_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]
  exact Finset.inter_subset_right

theorem ball_low (u : V) (hu : u ∈ U) (t : ℕ) :
    ball (fun w => SimpleGraph.neighborFinset J w) u t ⊆ U := by
  induction t generalizing u with
  | zero => simpa only [ball, Finset.singleton_subset_iff] using hu
  | succ t ih =>
    intro a ha
    rcases (mem_succ _ u a t).mp ha with he | ⟨w, hw, ha⟩
    · exact he ▸ hu
    · obtain ⟨i, j, _, _, hj⟩ :=
        (PublicEmbedding.adj_iff (graph G C D R L Q) (GeneralCoveringOwnerVirtualPrepare.embedding D Q) u w).mp
          ((SimpleGraph.mem_neighborFinset J u w).mp hw)
      have hwU : w ∈ U := (GeneralCoveringOwnerVirtualPrepare.mem_image D Q w).mpr ⟨j.val, hj, j.property⟩
      exact ih w hwU ha

theorem anchors_low {b : ℕ} (ids : BitCode V b) (hk : k ≤ r) (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).anchors ⊆ U := by
  rw [anchors_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hk v]
  intro a ha
  obtain ⟨u, hu, ha⟩ := Finset.mem_biUnion.mp ha
  exact ball_low G C targets D R L Δ hinc hlocal input hD hR hC hTargets u (Finset.mem_inter.mp hu).2 k ha

theorem task_ids {b : ℕ} (ids : BitCode V b) (hk : k ≤ r)
    (I : Finset (Low D Q)) (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (hsize : I.card ≤ k) (v : V) (hv : v ∈ vertices G C D R L Q I) :
    partIds D Q I ⊆ ((program ids L Δ r k s).runEncoded G input v).anchors := by
  obtain ⟨j, hj, hjlabel⟩ := touches G C D R L Q I v hv
  rw [anchors_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hk v]
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_biUnion.mpr ⟨j.val.val, Finset.mem_inter.mpr ⟨hjlabel,
    (GeneralCoveringOwnerVirtualPrepare.mem_image D Q j.val.val).mpr ⟨j.val, rfl, j.property⟩⟩,
    part_ball G C D R L Q I hI k hsize j i hj hi⟩

theorem task_minimum {b : ℕ} (ids : BitCode V b) (hk : k ≤ r)
    (I : Finset (Low D Q)) (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (hsize : I.card ≤ k) (v : V) (hv : v ∈ vertices G C D R L Q I) :
    (partIds D Q I).min' (partIds_nonempty D Q I (part_nonempty G C D R L Q I hI)) ∈
      ((program ids L Δ r k s).runEncoded G input v).anchors :=
  task_ids G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hk I hI hsize v hv
    (Finset.min'_mem _ _)

theorem canonical_eq {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v a : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors) :
    canonical G ids L Δ r s input v a =
      (ball (fun w => SimpleGraph.neighborFinset J w) a s).sort.map (TopologyGather.localData J Δ) := by
  rw [anchors_run] at ha
  exact RootFrameUnion.canonical_eq _ _
    (frame_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v)
    (frame_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v) k s hks a ha

theorem canonical_common {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v w a : V)
    (hv : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors)
    (hw : a ∈ ((program ids L Δ r k s).runEncoded G input w).anchors) :
    canonical G ids L Δ r s input v a = canonical G ids L Δ r s input w a := by
  rw [canonical_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a hv,
    canonical_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks w a hw]

theorem canonical_keys {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v a : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors) :
    TaggedDictionary.keys (canonical G ids L Δ r s input v a) =
      ball (fun w => SimpleGraph.neighborFinset J w) a s := by
  rw [canonical_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a ha]
  simp [TaggedDictionary.keys, List.map_map, Function.comp_def, TopologyGather.localData]

theorem canonical_true {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v a : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors) :
    ∀ p ∈ canonical G ids L Δ r s input v a,
      p.2.val = (SimpleGraph.neighborFinset J p.1).sort (· ≤ ·) := by
  rw [canonical_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a ha]
  intro p hp
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
  exact TopologyGather.true_neighbors J Δ (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) u

theorem canonical_length {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v a : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors) :
    (canonical G ids L Δ r s input v a).length ≤ (Δ + 1) ^ s := by
  rw [canonical_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a ha,
    List.length_map, Finset.length_sort]
  exact NeighborBallGraph.graph_card_bound J Δ (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a s

theorem canonical_neighbors {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v a u : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors)
    (hu : u ∈ ball (fun w => SimpleGraph.neighborFinset J w) a s) :
    FrameInterpreter.neighbors (canonical G ids L Δ r s input v a) u = SimpleGraph.neighborFinset J u := by
  apply FrameInterpreter.neighbors_correct _ _ ?_ u
  · rw [canonical_keys G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a ha]
    exact hu
  · intro p hp
    have ht := canonical_true G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a ha p hp
    exact (congrArg List.toFinset ht).trans (Finset.sort_toFinset _ _)

theorem canonical_ball {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v a : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors) (t : ℕ) (ht : t ≤ s) :
    ball (FrameInterpreter.neighbors (canonical G ids L Δ r s input v a)) a t =
      ball (fun w => SimpleGraph.neighborFinset J w) a t := by
  apply (FiniteBallAgreement.balls_eq _ _ a t _).symm
  intro u hu
  exact (canonical_neighbors G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a u ha
    (monotone _ a ht hu)).symm

theorem lookup_true_frame {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r) (v a : V)
    (ha : a ∈ ((program ids L Δ r k s).runEncoded G input v).anchors) :
    TaggedDictionary.lookup ((program ids L Δ r k s).runEncoded G input v).frames a =
      some ((ball (fun w => SimpleGraph.neighborFinset J w) a s).sort.map (TopologyGather.localData J Δ)) := by
  rw [frame_lookup G ids L Δ r k s input v a ha,
    canonical_eq G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a ha]

theorem task_common {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r)
    (I : Finset (Low D Q)) (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (hsize : I.card ≤ k) (v w a : V) (hv : v ∈ vertices G C D R L Q I)
    (hw : w ∈ vertices G C D R L Q I) (ha : a ∈ partIds D Q I) :
    canonical G ids L Δ r s input v a = canonical G ids L Δ r s input w a :=
  canonical_common G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v w a
    (task_ids G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids (by omega) I hI hsize v hv ha)
    (task_ids G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids (by omega) I hI hsize w hw ha)

theorem task_frame_lookup {b : ℕ} (ids : BitCode V b) (hks : k + s ≤ r)
    (I : Finset (Low D Q)) (hI : ((graph G C D R L Q).induce (I : Set (Low D Q))).Connected)
    (hsize : I.card ≤ k) (v a : V) (hv : v ∈ vertices G C D R L Q I) (ha : a ∈ partIds D Q I) :
    TaggedDictionary.lookup ((program ids L Δ r k s).runEncoded G input v).frames a =
      some ((ball (fun w => SimpleGraph.neighborFinset J w) a s).sort.map (TopologyGather.localData J Δ)) :=
  lookup_true_frame G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids hks v a
    (task_ids G C targets D R L Δ r k s hinc hlocal input hD hR hC hTargets ids (by omega) I hI hsize v hv ha)

theorem none_nongated {b : ℕ} (ids : BitCode V b) (v : V)
    (hg : ¬ (v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L))
    (ho : GeneralCoveringOwners.owner C D R v = none) :
    ((program ids L Δ r k s).runEncoded G input v).anchors = ∅ ∧
      ((program ids L Δ r k s).runEncoded G input v).frames = [] :=
  empty_roots G ids L Δ r k s input v
    (GeneralCoveringOwnerRootFrames.none_nongated G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v hg ho)

theorem empty_low {b : ℕ} (ids : BitCode V b) [IsEmpty (Low D Q)] (v : V) :
    ((program ids L Δ r k s).runEncoded G input v).anchors = ∅ ∧
      ((program ids L Δ r k s).runEncoded G input v).frames = [] := by
  exact empty_roots G ids L Δ r k s input v
    (GeneralCoveringOwnerRootFrames.empty_low G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v)
end Correct

theorem empty_physical [IsEmpty V] {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ r k s).runEncoded G input = fun v => isEmptyElim v := by
  funext v
  exact isEmptyElim v

theorem rounds {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ) :
    (program ids L Δ r k s).rounds = 12 + 4 * r := by
  simp only [program, Program.rounds, GeneralCoveringOwnerRootFrames.rounds, Nat.add_zero]

theorem maxBits_eq {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ) :
    (program ids L Δ r k s).maxBits = (GeneralCoveringOwnerRootFrames.program ids L Δ r).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]

theorem maxBits {b : ℕ} (ids : BitCode V b) (L Δ r k s : ℕ) :
    (program ids L Δ r k s).maxBits ≤ max
      ((L + Δ + 3) * (b + (Δ + 1) ^ (r + 1) * (b + 1) + 2))
      (b + GeneralCoveringOwnerRootFrames.capacity Δ r * (b + Δ * (b + 1) + 1) + 1) := by
  rw [maxBits_eq]
  exact GeneralCoveringOwnerRootFrames.maxBits ids L Δ r

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (L Δ r k s n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program ids L Δ r k s).maxBits ≤ max
      ((L + Δ + 3) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2))
      (c + GeneralCoveringOwnerRootFrames.capacity Δ r * (c + Δ * (c + 1) + 1) + 1) * Nat.clog 2 (n + 2) := by
  rw [maxBits_eq]
  exact GeneralCoveringOwnerRootFrames.logarithmic_bits ids L Δ r n c hids

theorem logarithmic_public_card {b : ℕ} (ids : BitCode V b) (L Δ r k s c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids L Δ r k s).maxBits ≤ max
      ((L + Δ + 3) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2))
      (c + GeneralCoveringOwnerRootFrames.capacity Δ r * (c + Δ * (c + 1) + 1) + 1) * Nat.clog 2 (Fintype.card V + 2) :=
  logarithmic_bits ids L Δ r k s (Fintype.card V) c hids

end Paper.GeneralCoveringOwnerRoleFrames

#print axioms Paper.GeneralCoveringOwnerRoleFrames.frame_type_compat
#print axioms Paper.GeneralCoveringOwnerRoleFrames.run_program
#print axioms Paper.GeneralCoveringOwnerRoleFrames.env_retained
#print axioms Paper.GeneralCoveringOwnerRoleFrames.private_input_retained
#print axioms Paper.GeneralCoveringOwnerRoleFrames.source_retained
#print axioms Paper.GeneralCoveringOwnerRoleFrames.anchors_run
#print axioms Paper.GeneralCoveringOwnerRoleFrames.frame_dictionary_keys
#print axioms Paper.GeneralCoveringOwnerRoleFrames.frame_dictionary_consistent
#print axioms Paper.GeneralCoveringOwnerRoleFrames.frame_lookup
#print axioms Paper.GeneralCoveringOwnerRoleFrames.frame_dictionary_length
#print axioms Paper.GeneralCoveringOwnerRoleFrames.empty_roots
#print axioms Paper.GeneralCoveringOwnerRoleFrames.part_ball
#print axioms Paper.GeneralCoveringOwnerRoleFrames.partIds_nonempty
#print axioms Paper.GeneralCoveringOwnerRoleFrames.part_nonempty
#print axioms Paper.GeneralCoveringOwnerRoleFrames.touches
#print axioms Paper.GeneralCoveringOwnerRoleFrames.root_keys
#print axioms Paper.GeneralCoveringOwnerRoleFrames.frame_keys
#print axioms Paper.GeneralCoveringOwnerRoleFrames.frame_true
#print axioms Paper.GeneralCoveringOwnerRoleFrames.anchors_eq
#print axioms Paper.GeneralCoveringOwnerRoleFrames.root_count
#print axioms Paper.GeneralCoveringOwnerRoleFrames.anchors_card
#print axioms Paper.GeneralCoveringOwnerRoleFrames.roots_low
#print axioms Paper.GeneralCoveringOwnerRoleFrames.ball_low
#print axioms Paper.GeneralCoveringOwnerRoleFrames.anchors_low
#print axioms Paper.GeneralCoveringOwnerRoleFrames.task_ids
#print axioms Paper.GeneralCoveringOwnerRoleFrames.task_minimum
#print axioms Paper.GeneralCoveringOwnerRoleFrames.canonical_eq
#print axioms Paper.GeneralCoveringOwnerRoleFrames.canonical_common
#print axioms Paper.GeneralCoveringOwnerRoleFrames.canonical_keys
#print axioms Paper.GeneralCoveringOwnerRoleFrames.canonical_true
#print axioms Paper.GeneralCoveringOwnerRoleFrames.canonical_length
#print axioms Paper.GeneralCoveringOwnerRoleFrames.canonical_neighbors
#print axioms Paper.GeneralCoveringOwnerRoleFrames.canonical_ball
#print axioms Paper.GeneralCoveringOwnerRoleFrames.lookup_true_frame
#print axioms Paper.GeneralCoveringOwnerRoleFrames.task_common
#print axioms Paper.GeneralCoveringOwnerRoleFrames.task_frame_lookup
#print axioms Paper.GeneralCoveringOwnerRoleFrames.none_nongated
#print axioms Paper.GeneralCoveringOwnerRoleFrames.empty_low
#print axioms Paper.GeneralCoveringOwnerRoleFrames.empty_physical
#print axioms Paper.GeneralCoveringOwnerRoleFrames.rounds
#print axioms Paper.GeneralCoveringOwnerRoleFrames.maxBits_eq
#print axioms Paper.GeneralCoveringOwnerRoleFrames.maxBits
#print axioms Paper.GeneralCoveringOwnerRoleFrames.logarithmic_bits
#print axioms Paper.GeneralCoveringOwnerRoleFrames.logarithmic_public_card
