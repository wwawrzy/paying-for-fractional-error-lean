import Paper.Solver.LocalSearch.GeneralCoveringOwnerTopologyGather
import Paper.Solver.LocalSearch.GeneralCoveringOwnerRouteLabels

/-! Canonical bounded frames from one actual low-owner topology gather,
followed by two physical broadcasts. Optional owners read their own root;
only light admissible vertices keep the closed physical support union.
No total-owner fallback or physical dependency-ball enumeration is used. -/
namespace Paper.GeneralCoveringOwnerRootFrames
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V A : Type} [LinearOrder V]

def capacity (Δ r : ℕ) : ℕ := (Δ + 1) ^ r
abbrev Frame (V : Type) (Δ r : ℕ) :=
  {xs : List (TopologyGather.Record V Δ) // xs.length ≤ capacity Δ r}

def frameCode {b : ℕ} (ids : BitCode V b) (Δ r : ℕ) :
    BitCode (Frame V Δ r) (capacity Δ r * (b + Δ * (b + 1) + 1)) :=
  ListPacket.bounded (TopologyGather.code ids Δ) (capacity Δ r)

def packet (Δ r : ℕ) (xs : List (TopologyGather.Record V Δ)) : Frame V Δ r :=
  TaggedDictionary.bounded (capacity Δ r) xs

/-- This CORE takes already computed metadata; it does not rerun its producer. -/
def deliver {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L : ℕ) :
    Program V (GeneralCoveringOwnerPayloadRoute.Input V A)
      {xs : List (V × A) // xs.length ≤ max 1 L} :=
  .seq (.local fun _ _ s => (s, s))
    (.seq (ProgramMemory.carry (GeneralCoveringOwnerPayloadRoute.readProgram P))
      (.seq (.local fun _ _ s => (s.1.toList, (s.1, s.2)))
        (.seq (ProgramMemory.carry (TaggedGather.program ids P 1))
          (.local fun _ _ s => TaggedDictionary.bounded (max 1 L)
            (if GeneralCoveringOwnerPayloadRoute.gate s.2.2 then s.1 else s.2.1.toList)))))

def routeInput {Δ r : ℕ} (s : Frame V Δ r × GeneralCoveringOwnerVirtualPrepare.Env V) :
    GeneralCoveringOwnerPayloadRoute.Input V (Frame V Δ r) :=
  ⟨s.2.metadata, s.2.low, s.1⟩

structure Output (V : Type) (L Δ r : ℕ) where
  roots : {xs : List (V × Frame V Δ r) // xs.length ≤ max 1 L}
  ownFrame : Frame V Δ r
  env : GeneralCoveringOwnerVirtualPrepare.Env V

def core {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) :
    Program V (Frame V Δ r × GeneralCoveringOwnerVirtualPrepare.Env V) (Output V L Δ r) :=
  .seq (.local fun _ _ s => (routeInput s, s))
    (.seq (ProgramMemory.carry (deliver ids (frameCode ids Δ r) L))
      (.local fun _ _ s => ⟨s.1, s.2.1, s.2.2⟩))

/-- All parameters and packet codes are public before the physical graph. -/
def program {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (Output V L Δ r) :=
  .seq (GeneralCoveringOwnerTopologyGather.program ids L Δ r)
    (.seq (.local fun _ _ s => (packet Δ r s.1, s.2)) (core ids L Δ r))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def raw {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (s : V → GeneralCoveringOwnerPayloadRoute.Input V A) (v : V) : List (V × A) :=
  if GeneralCoveringOwnerPayloadRoute.gate (s v) then
    GeneralCoveringOwnerPayloadRoute.candidate G ids P s v
  else (GeneralCoveringOwnerPayloadRoute.first G P s v).toList

theorem deliver_run {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L : ℕ)
    (s : V → GeneralCoveringOwnerPayloadRoute.Input V A) :
    (deliver ids P L).run G s = fun v => TaggedDictionary.bounded (max 1 L) (raw G ids P s v) := by
  change (Program.seq _ (Program.seq (ProgramMemory.carry (TaggedGather.program ids P 1)) _)).run G
    ((ProgramMemory.carry (GeneralCoveringOwnerPayloadRoute.readProgram P)).run G (fun v => (s v, s v))) = _
  rw [ProgramMemory.run G (GeneralCoveringOwnerPayloadRoute.readProgram P)]
  change (Program.local _).run G ((ProgramMemory.carry (TaggedGather.program ids P 1)).run G
    (fun v => ((GeneralCoveringOwnerPayloadRoute.first G P s v).toList,
      (GeneralCoveringOwnerPayloadRoute.first G P s v, s v)))) = _
  rw [ProgramMemory.run G (TaggedGather.program ids P 1)]
  funext v
  by_cases hg : GeneralCoveringOwnerPayloadRoute.gate (s v) = true <;>
    simp only [Program.run, raw, GeneralCoveringOwnerPayloadRoute.candidate, hg, Bool.false_eq_true, ↓reduceIte]

theorem core_run {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ)
    (s : V → Frame V Δ r × GeneralCoveringOwnerVirtualPrepare.Env V) :
    (core ids L Δ r).run G s = fun v =>
      ⟨(deliver ids (frameCode ids Δ r) L).run G (fun u => routeInput (s u)) v, (s v).1, (s v).2⟩ := by
  change (Program.local _).run G ((ProgramMemory.carry (deliver ids (frameCode ids Δ r) L)).run G
    (fun v => (routeInput (s v), s v))) = _
  rw [ProgramMemory.run G (deliver ids (frameCode ids Δ r) L)] <;> rfl

def gathered {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) (input : V → GeneralCoveringOwners.Input V) :=
  (GeneralCoveringOwnerTopologyGather.program ids L Δ r).runEncoded G input

def frame {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) (input : V → GeneralCoveringOwners.Input V) (v : V) : Frame V Δ r :=
  packet Δ r (gathered G ids L Δ r input v).1

/-- Keep the large producer opaque while exposing only its local projections. -/
private theorem compose_run {In Out X : Type} {Δ r : ℕ} (P : Program V In (List (TopologyGather.Record V Δ) × X))
    (Q : Program V (Frame V Δ r × X) Out) (input : V → In) :
    (Program.seq P (Program.seq (Program.local fun _ _ s => (packet Δ r s.1, s.2)) Q)).runEncoded G input =
      Q.run G (fun v => (packet Δ r (P.runEncoded G input v).1, (P.runEncoded G input v).2)) := by
  simp only [Program.runEncoded_eq_run] <;> rfl

theorem run_program {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ r).runEncoded G input = fun v =>
      ⟨(deliver ids (frameCode ids Δ r) L).run G
        (fun u => routeInput (frame G ids L Δ r input u, (gathered G ids L Δ r input u).2)) v,
        frame G ids L Δ r input v, (gathered G ids L Δ r input v).2⟩ := by
  delta program
  rw [compose_run G, core_run] <;> rfl

theorem env_retained {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r).runEncoded G input v).env = GeneralCoveringOwnerSimulation.learned G ids L Δ input v := by
  rw [run_program]
  exact GeneralCoveringOwnerTopologyGather.env_retained G ids L Δ r input v

theorem private_input_retained {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r).runEncoded G input v).env.metadata.owned.input = input v := by
  rw [env_retained]
  exact GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v

theorem own_frame_retained {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r).runEncoded G input v).ownFrame = frame G ids L Δ r input v := by
  rw [run_program]

theorem raw_keys {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → GeneralCoveringOwnerPayloadRoute.PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (v : V) :
    TaggedDictionary.keys (raw G ids P (GeneralCoveringOwnerPayloadRoute.expected G C D R L s) v) =
      GeneralCoveringOwnerRouteLabels.labels G C D R L v ∩ GeneralCoveringOwnerPayloadRoute.activeSet s := by
  by_cases hg : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · have he : raw G ids P (GeneralCoveringOwnerPayloadRoute.expected G C D R L s) v =
        GeneralCoveringOwnerPayloadRoute.candidate G ids P (GeneralCoveringOwnerPayloadRoute.expected G C D R L s) v := by
      rw [raw, GeneralCoveringOwnerPayloadRoute.gate_expected, if_pos (decide_eq_true hg)]
    rw [he, GeneralCoveringOwnerPayloadRoute.candidate_keys G ids P C D R L hlocal s hD v,
      GeneralCoveringOwnerRouteLabels.labels_eq_light G C D R L hg]
  · rw [raw, GeneralCoveringOwnerPayloadRoute.gate_expected]
    simp only [decide_eq_false hg, Bool.false_eq_true, ↓reduceIte]
    rw [GeneralCoveringOwnerRouteLabels.labels_eq_own G C D R L hg]
    ext k
    rw [GeneralCoveringOwnerPayloadRoute.first_keys_iff G P C D R L hlocal s hD v k, Finset.mem_inter]
    cases ho : GeneralCoveringOwners.owner C D R v <;> simp [ho, eq_comm]

theorem raw_consistent {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → GeneralCoveringOwnerPayloadRoute.PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (v : V) :
    TaggedDictionary.Consistent (fun u => (s u).payload)
      (raw G ids P (GeneralCoveringOwnerPayloadRoute.expected G C D R L s) v) := by
  unfold raw
  split
  · exact GeneralCoveringOwnerPayloadRoute.candidate_consistent G ids P C D R L hlocal s hD v
  · exact GeneralCoveringOwnerPayloadRoute.first_consistent G P C D R L hlocal s hD v

theorem raw_bound {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → GeneralCoveringOwnerPayloadRoute.PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (v : V) :
    (TaggedDictionary.keys (raw G ids P (GeneralCoveringOwnerPayloadRoute.expected G C D R L s) v)).card ≤ max 1 L := by
  rw [raw_keys G ids P C D R L hlocal s hD v]
  apply (Finset.card_le_card Finset.inter_subset_left).trans
  by_cases hg : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · rw [GeneralCoveringOwnerRouteLabels.labels_eq_light G C D R L hg]
    exact (lightSupport_bound G C D R L v).trans (le_max_right _ _)
  · rw [GeneralCoveringOwnerRouteLabels.labels_eq_own G C D R L hg]
    cases GeneralCoveringOwners.owner C D R v <;> simp <;> omega

section Correct
variable (C targets : V → Finset V) (D R : Finset V) (L Δ r : ℕ)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q

noncomputable local instance publicAdj : DecidableRel (SimpleGraph.Adj J) := fun _ _ => Classical.propDecidable _

theorem packet_eq {b : ℕ} (ids : BitCode V b) (v : V) :
    (frame G ids L Δ r input v).val =
      TaggedDictionary.normalize (GeneralCoveringOwnerTopologyGather.received G ids L Δ r input v) :=
  TaggedDictionary.bounded_eq _ _
    (GeneralCoveringOwnerTopologyGather.key_count G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v)

theorem frame_keys {b : ℕ} (ids : BitCode V b) (v : V) :
    TaggedDictionary.keys (frame G ids L Δ r input v).val =
      NeighborBalls.ball (fun u => SimpleGraph.neighborFinset J u) v r := by
  rw [packet_eq G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v, TaggedDictionary.keys_normalize]
  exact GeneralCoveringOwnerTopologyGather.keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v

theorem frame_record_true {b : ℕ} (ids : BitCode V b) (v : V) (a : TopologyGather.Record V Δ)
    (ha : a ∈ (frame G ids L Δ r input v).val) :
    a.2.val = (SimpleGraph.neighborFinset J a.1).sort (· ≤ ·) := by
  have hm := TaggedDictionary.bounded_mem (capacity Δ r) (gathered G ids L Δ r input v).1 a ha
  obtain ⟨u, _, _, hk, hn⟩ := GeneralCoveringOwnerTopologyGather.record_true G C targets D R L Δ r
    hinc hlocal input hD hR hC hTargets ids v a hm
  rw [hk]
  exact hn

noncomputable def privatePayload {b : ℕ} (ids : BitCode V b) (v : V) :
    GeneralCoveringOwnerPayloadRoute.PrivateInput V (Frame V Δ r) :=
  ⟨input v, decide (v ∈ U), frame G ids L Δ r input v⟩

theorem route_input_eq {b : ℕ} (ids : BitCode V b) :
    (fun v => routeInput (frame G ids L Δ r input v, (gathered G ids L Δ r input v).2)) =
      GeneralCoveringOwnerPayloadRoute.expected G C D R L (privatePayload G C D R L Δ r input ids) := by
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets
  funext v
  change GeneralCoveringOwnerPayloadRoute.Input.mk (gathered G ids L Δ r input v).2.metadata
    (gathered G ids L Δ r input v).2.low (frame G ids L Δ r input v) =
    ⟨GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input v, decide (v ∈ U), frame G ids L Δ r input v⟩
  rw [show (gathered G ids L Δ r input v).2 = GeneralCoveringOwnerSimulation.learned G ids L Δ input v from
    GeneralCoveringOwnerTopologyGather.env_retained G ids L Δ r input v, hs.1 v, hs.2.2.1 v]

omit hinc hlocal hD hR hC hTargets in
theorem active_eq {b : ℕ} (ids : BitCode V b) :
    GeneralCoveringOwnerPayloadRoute.activeSet (privatePayload G C D R L Δ r input ids) = U := by
  ext v
  rw [GeneralCoveringOwnerPayloadRoute.mem_activeSet]
  exact decide_eq_true_iff

theorem keys {b : ℕ} (ids : BitCode V b) (v : V) :
    TaggedDictionary.keys ((program ids L Δ r).runEncoded G input v).roots.val =
      GeneralCoveringOwnerRouteLabels.labels G C D R L v ∩ U := by
  rw [run_program, route_input_eq G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids, deliver_run]
  rw [TaggedDictionary.keys_bounded_eq _ _
    (raw_bound G ids (frameCode ids Δ r) C D R L hlocal (privatePayload G C D R L Δ r input ids) hD v)]
  rw [raw_keys G ids (frameCode ids Δ r) C D R L hlocal (privatePayload G C D R L Δ r input ids) hD v,
    active_eq G C D R L Δ r input ids]

theorem consistent {b : ℕ} (ids : BitCode V b) (v : V) :
    TaggedDictionary.Consistent (frame G ids L Δ r input)
      ((program ids L Δ r).runEncoded G input v).roots.val := by
  rw [run_program, route_input_eq G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids, deliver_run]
  exact TaggedDictionary.bounded_consistent _ _ _
    (raw_consistent G ids (frameCode ids Δ r) C D R L hlocal (privatePayload G C D R L Δ r input ids) hD v)

theorem lookup {b : ℕ} (ids : BitCode V b) (v u : V)
    (hu : u ∈ GeneralCoveringOwnerRouteLabels.labels G C D R L v ∩ U) :
    TaggedDictionary.lookup ((program ids L Δ r).runEncoded G input v).roots.val u =
      some (frame G ids L Δ r input u) := by
  apply TaggedDictionary.lookup_correct _ _
    (consistent G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v)
  rw [keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]
  exact hu

/-- Original owner-star vertices retain the low root even when not admissible. -/
theorem owner_lookup {b : ℕ} (ids : BitCode V b) (v u : V)
    (ho : GeneralCoveringOwners.owner C D R v = some u) (hu : u ∈ U) :
    TaggedDictionary.lookup ((program ids L Δ r).runEncoded G input v).roots.val u =
      some (frame G ids L Δ r input u) :=
  lookup G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v u
    (Finset.mem_inter.mpr ⟨GeneralCoveringOwnerRouteLabels.owner_label G C D R L ho, hu⟩)

theorem support_lookup {b : ℕ} (ids : BitCode V b) (v u : V)
    (ha : v ∈ CoveringSupport.admissible C R) (hn : v ∉ GeneralCoveringOwnerSupport.heavy G C D R L)
    (hs : u ∈ GeneralCoveringOwnerSupport.support G C D R v) (hu : u ∈ U) :
    TaggedDictionary.lookup ((program ids L Δ r).runEncoded G input v).roots.val u =
      some (frame G ids L Δ r input u) :=
  lookup G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v u
    (Finset.mem_inter.mpr ⟨GeneralCoveringOwnerRouteLabels.light_label G C D R L ha hn hs, hu⟩)

theorem nonadmissible_keys {b : ℕ} (ids : BitCode V b) (v : V)
    (ha : v ∉ CoveringSupport.admissible C R) :
    TaggedDictionary.keys ((program ids L Δ r).runEncoded G input v).roots.val =
      (GeneralCoveringOwners.owner C D R v).toFinset ∩ U := by
  rw [keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v,
    GeneralCoveringOwnerRouteLabels.nonadmissible_labels G C D R L ha]

theorem delivered_frame {b : ℕ} (ids : BitCode V b) (v u : V) (f : Frame V Δ r)
    (hf : TaggedDictionary.lookup ((program ids L Δ r).runEncoded G input v).roots.val u = some f) :
    TaggedDictionary.keys f.val = NeighborBalls.ball (fun w => SimpleGraph.neighborFinset J w) u r ∧
      ∀ a ∈ f.val, a.2.val = (SimpleGraph.neighborFinset J a.1).sort (· ≤ ·) := by
  cases hfind : (((program ids L Δ r).runEncoded G input v).roots.val.find? (fun p => decide (p.1 = u))) with
  | none => simp [TaggedDictionary.lookup, hfind] at hf
  | some p =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred : (fun t : V × Frame V Δ r => decide (t.1 = u)) p = true :=
      List.find?_some (p := fun t : V × Frame V Δ r => decide (t.1 = u)) (a := p) hfind
    have hkey : p.1 = u := of_decide_eq_true hpred
    have hval := consistent G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v p hmem
    have hpf : p.2 = f := by simpa only [TaggedDictionary.lookup, hfind, Option.map_some, Option.some.injEq] using hf
    have hfu : f = frame G ids L Δ r input u := by
      calc
        f = p.2 := hpf.symm
        _ = frame G ids L Δ r input p.1 := hval
        _ = frame G ids L Δ r input u := congrArg (frame G ids L Δ r input) hkey
    rw [hfu]
    exact ⟨frame_keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids u,
      frame_record_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids u⟩

theorem none_nongated {b : ℕ} (ids : BitCode V b) (v : V)
    (hg : ¬ (v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L))
    (ho : GeneralCoveringOwners.owner C D R v = none) :
    TaggedDictionary.keys ((program ids L Δ r).runEncoded G input v).roots.val = ∅ := by
  rw [keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v,
    GeneralCoveringOwnerRouteLabels.nongated_none G C D R L hg ho, Finset.empty_inter]

theorem high_absent {b : ℕ} (ids : BitCode V b) (v : V) (i : D) (hi : i ∈ Q) :
    i.val ∉ TaggedDictionary.keys ((program ids L Δ r).runEncoded G input v).roots.val := by
  rw [keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]
  intro hm
  exact ((GeneralCoveringOwnerVirtualPrepare.low_image D Q i.val i.property).mp (Finset.mem_inter.mp hm).2) hi

theorem empty_low {b : ℕ} (ids : BitCode V b) [IsEmpty (Low D Q)] (v : V) :
    TaggedDictionary.keys ((program ids L Δ r).runEncoded G input v).roots.val = ∅ := by
  rw [keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨i, _, hi⟩ := (GeneralCoveringOwnerVirtualPrepare.mem_image D Q u).mp (Finset.mem_inter.mp hu).2
  exact isEmptyElim (⟨i, hi⟩ : Low D Q)
end Correct

theorem root_capacity {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r).runEncoded G input v).roots.val.length ≤ max 1 L :=
  ((program ids L Δ r).runEncoded G input v).roots.property

theorem empty_physical [IsEmpty V] {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ r).runEncoded G input = fun v => isEmptyElim v := by
  funext v
  exact isEmptyElim v

theorem deliver_rounds {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L : ℕ) :
    (deliver ids P L).rounds = 2 := rfl

theorem deliver_maxBits {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L : ℕ) :
    (deliver ids P L).maxBits ≤ b + w + 1 := by
  simp only [deliver, Program.maxBits, ProgramMemory.maxBits,
    GeneralCoveringOwnerPayloadRoute.readProgram, TaggedGather.maxBits, Nat.one_mul,
    Nat.zero_max, Nat.max_zero]
  exact max_le (by omega) (le_refl _)

theorem rounds {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) :
    (program ids L Δ r).rounds = 12 + 4 * r := by
  simp only [program, core, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringOwnerTopologyGather.rounds, deliver_rounds]
  omega

theorem maxBits {b : ℕ} (ids : BitCode V b) (L Δ r : ℕ) :
    (program ids L Δ r).maxBits ≤ max
      ((L + Δ + 3) * (b + (Δ + 1) ^ (r + 1) * (b + 1) + 2))
      (b + capacity Δ r * (b + Δ * (b + 1) + 1) + 1) := by
  simp only [program, core, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact max_le_max (GeneralCoveringOwnerTopologyGather.maxBits ids L Δ r)
    (deliver_maxBits ids (frameCode ids Δ r) L)

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (L Δ r n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program ids L Δ r).maxBits ≤ max
      ((L + Δ + 3) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2))
      (c + capacity Δ r * (c + Δ * (c + 1) + 1) + 1) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb1 := (BroadcastModel.logarithmic_message_budget n b c hids).1
  have hr : b + Δ * (b + 1) ≤ (c + Δ * (c + 1)) * Nat.clog 2 (n + 2) := by
    simpa only [Nat.add_mul, Nat.mul_assoc] using Nat.add_le_add hids (Nat.mul_le_mul_left Δ hb1)
  have hf := ListPacket.logarithmic_width (capacity Δ r) _ _ n hr
  have hd : b + capacity Δ r * (b + Δ * (b + 1) + 1) + 1 ≤
      (c + capacity Δ r * (c + Δ * (c + 1) + 1) + 1) * Nat.clog 2 (n + 2) := by
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.add_le_add (Nat.add_le_add hids hf) hl
  simp only [program, core, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  apply max_le
  · exact (GeneralCoveringOwnerTopologyGather.logarithmic_bits ids L Δ r n c hids).trans
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · exact (deliver_maxBits ids (frameCode ids Δ r) L).trans
      (hd.trans (Nat.mul_le_mul_right _ (le_max_right _ _)))

theorem logarithmic_public_card {b : ℕ} (ids : BitCode V b) (L Δ r c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids L Δ r).maxBits ≤ max
      ((L + Δ + 3) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2))
      (c + capacity Δ r * (c + Δ * (c + 1) + 1) + 1) * Nat.clog 2 (Fintype.card V + 2) :=
  logarithmic_bits ids L Δ r (Fintype.card V) c hids

end Paper.GeneralCoveringOwnerRootFrames

#print axioms Paper.GeneralCoveringOwnerRootFrames.deliver_run
#print axioms Paper.GeneralCoveringOwnerRootFrames.core_run
#print axioms Paper.GeneralCoveringOwnerRootFrames.run_program
#print axioms Paper.GeneralCoveringOwnerRootFrames.env_retained
#print axioms Paper.GeneralCoveringOwnerRootFrames.private_input_retained
#print axioms Paper.GeneralCoveringOwnerRootFrames.own_frame_retained
#print axioms Paper.GeneralCoveringOwnerRootFrames.raw_keys
#print axioms Paper.GeneralCoveringOwnerRootFrames.raw_consistent
#print axioms Paper.GeneralCoveringOwnerRootFrames.raw_bound
#print axioms Paper.GeneralCoveringOwnerRootFrames.packet_eq
#print axioms Paper.GeneralCoveringOwnerRootFrames.frame_keys
#print axioms Paper.GeneralCoveringOwnerRootFrames.frame_record_true
#print axioms Paper.GeneralCoveringOwnerRootFrames.route_input_eq
#print axioms Paper.GeneralCoveringOwnerRootFrames.active_eq
#print axioms Paper.GeneralCoveringOwnerRootFrames.keys
#print axioms Paper.GeneralCoveringOwnerRootFrames.consistent
#print axioms Paper.GeneralCoveringOwnerRootFrames.lookup
#print axioms Paper.GeneralCoveringOwnerRootFrames.owner_lookup
#print axioms Paper.GeneralCoveringOwnerRootFrames.support_lookup
#print axioms Paper.GeneralCoveringOwnerRootFrames.nonadmissible_keys
#print axioms Paper.GeneralCoveringOwnerRootFrames.delivered_frame
#print axioms Paper.GeneralCoveringOwnerRootFrames.none_nongated
#print axioms Paper.GeneralCoveringOwnerRootFrames.high_absent
#print axioms Paper.GeneralCoveringOwnerRootFrames.empty_low
#print axioms Paper.GeneralCoveringOwnerRootFrames.root_capacity
#print axioms Paper.GeneralCoveringOwnerRootFrames.empty_physical
#print axioms Paper.GeneralCoveringOwnerRootFrames.deliver_rounds
#print axioms Paper.GeneralCoveringOwnerRootFrames.deliver_maxBits
#print axioms Paper.GeneralCoveringOwnerRootFrames.rounds
#print axioms Paper.GeneralCoveringOwnerRootFrames.maxBits
#print axioms Paper.GeneralCoveringOwnerRootFrames.logarithmic_bits
#print axioms Paper.GeneralCoveringOwnerRootFrames.logarithmic_public_card
