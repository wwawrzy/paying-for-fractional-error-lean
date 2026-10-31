import Paper.Solver.LocalSearch.GeneralCoveringOwnerRoleFrames
import Paper.Partitions.Local.ActiveFiniteBitPartition
import Paper.Preliminaries.LocalSeedRecords

/-! Exact local execution of the accepted active priority partition, including
its boundary round, from an actual canonical owner frame. A query takes a
fixed finite array of coin tables. Global coins occur only in the analysis
of restriction/extension; neither graphs nor global assignments enter runtime.
Part-event counting and physical fractional-output averaging are later gates. -/
namespace Paper.GeneralCoveringOwnerFramePartition
open BroadcastModel SevenFoundation NeighborBalls GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

def radius (k n : ℕ) : ℕ := n * (3 * k + 1) + 1
def outerRadius (k n : ℕ) : ℕ := k + radius k n
def slots (Δ k n : ℕ) : ℕ := (Δ + 1) ^ radius k n
abbrev Bits := ActiveFiniteBitPartition.Bits
abbrev Coins (Δ k b n : ℕ) := Fin (slots Δ k n) → Bits Δ k b n
def zeroBits (Δ k b n : ℕ) : Bits Δ k b n := fun _ _ => false

def addresses {Δ : ℕ} (xs : List (TopologyGather.Record V Δ)) : List V :=
  (TaggedDictionary.keys xs).sort (· ≤ ·)

/-- Padded arrays are indexed by finite sorted frame addresses only. -/
def coinRecords {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ)) (ω : Coins Δ k b n) :
    List (V × Bits Δ k b n) :=
  if h : (addresses xs).length ≤ slots Δ k n then LocalSeedRecords.records (addresses xs) h ω else []

def seedRecords {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ)) (ω : Coins Δ k b n) :
    List (V × ActiveFiniteBitPartition.Input Δ k b n) :=
  if h : (addresses xs).length ≤ slots Δ k n then
    LocalSeedRecords.records (addresses xs) h (fun j => (true, ω j)) else []

/-- Total outside the frame, with explicit zero padding and no default vertex. -/
def extend {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ)) (ω : Coins Δ k b n) : V → Bits Δ k b n :=
  FrameInterpreter.inputs (coinRecords k b n xs ω) (zeroBits Δ k b n)

/-- Analysis restriction: a public global assignment is read only at frame IDs. -/
def restrict {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (β : V → Bits Δ k b n) : Coins Δ k b n := fun j =>
  if h : j.val < (addresses xs).length then β ((addresses xs).get ⟨j.val, h⟩) else zeroBits Δ k b n

def evaluate {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (ω : Coins Δ k b n) : Finset V × Bool :=
  FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs (seedRecords k b n xs ω)
    (true, zeroBits Δ k b n) a

def query {idBits L : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (z : GeneralCoveringOwnerRoleFrames.Output V L Δ (outerRadius k n)) (a : V) (ω : Coins Δ k b n) :
    Option (Finset V × Bool) :=
  (TaggedDictionary.lookup z.frames a).map (fun xs => evaluate ids Δ k t b n xs a ω)

private theorem query_lookup {idBits L : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (z : GeneralCoveringOwnerRoleFrames.Output V L Δ (outerRadius k n)) (a : V) (ω : Coins Δ k b n)
    (xs : List (TopologyGather.Record V Δ)) (h : TaggedDictionary.lookup z.frames a = some xs) :
    query ids Δ k t b n z a ω = some (evaluate ids Δ k t b n xs a ω) := by
  exact congrArg (fun value : Option (List (TopologyGather.Record V Δ)) =>
    value.map (fun ys => evaluate ids Δ k t b n ys a ω)) h

def occurs (value : Option (Finset V × Bool)) (T : Finset V) : Bool :=
  match value with
  | none => false
  | some z => decide (z.1 = T)

structure Output (V : Type) (L Δ k b n : ℕ) where
  source : GeneralCoveringOwnerRoleFrames.Output V L Δ (outerRadius k n)
  answer : V → Coins Δ k b n → Option (Finset V × Bool)

def finish {idBits L : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (z : GeneralCoveringOwnerRoleFrames.Output V L Δ (outerRadius k n)) : Output V L Δ k b n :=
  ⟨z, query ids Δ k t b n z⟩

/-- One real frame producer and a local callable finite-coin evaluator.
No coin enumeration or additional broadcast is performed here. -/
def program {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (Output V L Δ k b n) :=
  .seq (GeneralCoveringOwnerRoleFrames.program ids L Δ (outerRadius k n) k (radius k n))
    (.local fun _ _ z => finish ids Δ k t b n z)

theorem slots_pos (Δ k n : ℕ) : 0 < slots Δ k n := by unfold slots; positivity

theorem bit_positions (Δ k b n : ℕ) :
    Fintype.card (Fin (slots Δ k n) × (CurrentFiniteBitPartition.Index Δ k n × Fin b)) =
      slots Δ k n * (n * 2 ^ ((Δ + 1) ^ k) * b) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    congrArg (fun m => slots Δ k n * m) (CurrentFiniteBitPartition.bits_per_vertex Δ k b n)

theorem restrict_slot {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (β : V → Bits Δ k b n) (h : (addresses xs).length ≤ slots Δ k n) (i : Fin (addresses xs).length) :
    restrict k b n xs β (LocalSeedRecords.slot (addresses xs) h i) = β ((addresses xs).get i) := by
  simp only [restrict, LocalSeedRecords.slot, dif_pos i.isLt]

private theorem base_lookup {A : Type} (l : List V) (hl : l.Nodup) (τ : Fin l.length → A) (i : Fin l.length) :
    TaggedDictionary.lookup (LocalSeedRecords.base l τ) (l.get i) = some (τ i) := by
  have hk : l.get i ∈ TaggedDictionary.keys (LocalSeedRecords.base l τ) := by
    rw [LocalSeedRecords.keys_base]
    exact List.mem_toFinset.mpr (l.get_mem i)
  have hm := TaggedDictionary.entry_mem (LocalSeedRecords.base l τ) (l.get i) hk
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
  have he := TaggedDictionary.entry_key (LocalSeedRecords.base l τ) (l.get i) hk
  rw [← hj] at he
  have hji : j = i := hl.injective_get he
  rw [TaggedDictionary.lookup, TaggedDictionary.find_entry (LocalSeedRecords.base l τ) (l.get i) hk]
  simp only [Option.map_some]
  rw [← hj, hji]

private theorem lookup_none {A : Type} (xs : List (V × A)) (a : V) (ha : a ∉ TaggedDictionary.keys xs) :
    TaggedDictionary.lookup xs a = none := by
  have hf : xs.find? (fun p : V × A => decide (p.1 = a)) = none := List.find?_eq_none.mpr (by
    intro p hp hcond
    have he : p.1 = a := of_decide_eq_true hcond
    exact ha ((TaggedDictionary.mem_keys xs a).mpr ⟨p, hp, he⟩))
  rw [TaggedDictionary.lookup, hf, Option.map_none]

theorem extend_slot {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (ω : Coins Δ k b n) (h : (addresses xs).length ≤ slots Δ k n) (i : Fin (addresses xs).length) :
    extend k b n xs ω ((addresses xs).get i) = ω (LocalSeedRecords.slot (addresses xs) h i) := by
  unfold extend coinRecords
  rw [dif_pos h]
  change (TaggedDictionary.lookup (LocalSeedRecords.base (addresses xs)
    (fun j => ω (LocalSeedRecords.slot (addresses xs) h j))) ((addresses xs).get i)).getD _ = _
  have hnodup : (addresses xs).Nodup := Finset.sort_nodup _ _
  rw [base_lookup (addresses xs) hnodup _ i, Option.getD_some]

theorem extend_restrict {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (β : V → Bits Δ k b n) (h : (addresses xs).length ≤ slots Δ k n) (u : V)
    (hu : u ∈ TaggedDictionary.keys xs) : extend k b n xs (restrict k b n xs β) u = β u := by
  have hul : u ∈ addresses xs := (Finset.mem_sort (· ≤ ·)).mpr hu
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hul
  rw [← hi, extend_slot k b n xs _ h i, restrict_slot k b n xs β h i]

private theorem seed_input {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (ω : Coins Δ k b n) (h : (addresses xs).length ≤ slots Δ k n) (S : Finset V)
    (hS : TaggedDictionary.keys xs ⊆ S) :
    seedRecords k b n xs ω = LocalSeedRecords.base (addresses xs)
      (fun i => (decide ((addresses xs).get i ∈ S), extend k b n xs ω ((addresses xs).get i))) := by
  rw [seedRecords, dif_pos h]
  apply congrArg (LocalSeedRecords.base (addresses xs))
  funext i
  have hiS := hS ((Finset.mem_sort (· ≤ ·)).mp ((addresses xs).get_mem i))
  rw [decide_eq_true hiS, extend_slot k b n xs ω h i]

private theorem seed_input_restrict {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (β : V → Bits Δ k b n) (h : (addresses xs).length ≤ slots Δ k n) (S : Finset V)
    (hS : TaggedDictionary.keys xs ⊆ S) :
    seedRecords k b n xs (restrict k b n xs β) = LocalSeedRecords.base (addresses xs)
      (fun i => (decide ((addresses xs).get i ∈ S), β ((addresses xs).get i))) := by
  rw [seed_input k b n xs _ h S hS]
  apply congrArg (LocalSeedRecords.base (addresses xs))
  funext i
  rw [extend_restrict k b n xs β h _ ((Finset.mem_sort (· ≤ ·)).mp ((addresses xs).get_mem i))]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem post_run {In X Y : Type} (P : Program V In X) (f : X → Y) (input : V → In) :
    (Program.seq P (Program.local fun _ _ z => f z)).runEncoded G input = fun v => f (P.runEncoded G input v) := rfl

def snapshot {idBits : ℕ} (ids : BitCode V idBits) (L Δ k n : ℕ) (input : V → GeneralCoveringOwners.Input V) :=
  (GeneralCoveringOwnerRoleFrames.program ids L Δ (outerRadius k n) k (radius k n)).runEncoded G input

def frame {idBits : ℕ} (ids : BitCode V idBits) (L Δ k n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V) :=
  GeneralCoveringOwnerRoleFrames.canonical G ids L Δ (outerRadius k n) (radius k n) input v a

theorem run_program {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ k t b n).runEncoded G input = fun v => finish ids Δ k t b n (snapshot G ids L Δ k n input v) :=
  post_run G _ _ input

theorem source_retained {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ k t b n).runEncoded G input v).source = snapshot G ids L Δ k n input v := by
  rw [run_program] <;> rfl

theorem native_query {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V) (ω : Coins Δ k b n) :
    ((program ids L Δ k t b n).runEncoded G input v).answer a ω =
      query ids Δ k t b n (snapshot G ids L Δ k n input v) a ω := by
  rw [run_program] <;> rfl

theorem no_anchor {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V) (ω : Coins Δ k b n)
    (ha : a ∉ (snapshot G ids L Δ k n input v).anchors) :
    ((program ids L Δ k t b n).runEncoded G input v).answer a ω = none := by
  have he : TaggedDictionary.keys (snapshot G ids L Δ k n input v).frames =
      (snapshot G ids L Δ k n input v).anchors :=
    GeneralCoveringOwnerRoleFrames.frame_dictionary_keys G ids L Δ (outerRadius k n) k (radius k n) input v
  have hn : a ∉ TaggedDictionary.keys (snapshot G ids L Δ k n input v).frames := by rwa [he]
  rw [native_query, query, lookup_none _ a hn, Option.map_none]

theorem env_retained {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ k t b n).runEncoded G input v).source.source.env =
      GeneralCoveringOwnerSimulation.learned G ids L Δ input v := by
  rw [source_retained]
  exact GeneralCoveringOwnerRoleFrames.env_retained G ids L Δ (outerRadius k n) k (radius k n) input v

theorem private_input_retained {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ k t b n).runEncoded G input v).source.source.env.metadata.owned.input = input v := by
  rw [env_retained]
  exact GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).Adj := fun _ _ => Classical.propDecidable _

section Correct
variable (C targets : V → Finset V) (D R : Finset V) (L Δ k t b n : ℕ)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q

theorem frame_keys {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) :
    TaggedDictionary.keys (frame G ids L Δ k n input v a) =
      ball (fun w => SimpleGraph.neighborFinset J w) a (radius k n) :=
  GeneralCoveringOwnerRoleFrames.canonical_keys G C targets D R L Δ (outerRadius k n) k (radius k n)
    hinc hlocal input hD hR hC hTargets ids (Nat.le_refl _) v a ha

theorem frame_true {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) :
    ∀ p ∈ frame G ids L Δ k n input v a, p.2.val.toFinset = SimpleGraph.neighborFinset J p.1 := by
  intro p hp
  have ht := GeneralCoveringOwnerRoleFrames.canonical_true G C targets D R L Δ (outerRadius k n) k (radius k n)
    hinc hlocal input hD hR hC hTargets ids (Nat.le_refl _) v a ha p hp
  exact (congrArg List.toFinset ht).trans (Finset.sort_toFinset _ _)

theorem frame_capacity {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) :
    (addresses (frame G ids L Δ k n input v a)).length ≤ slots Δ k n := by
  rw [addresses, Finset.length_sort, frame_keys G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha]
  exact NeighborBallGraph.graph_card_bound J Δ (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a (radius k n)

theorem anchor_low {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) : a ∈ U :=
  GeneralCoveringOwnerRoleFrames.anchors_low G C targets D R L Δ (outerRadius k n) k (radius k n)
    hinc hlocal input hD hR hC hTargets ids (Nat.le_add_right k (radius k n)) v ha

theorem frame_low {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) :
    TaggedDictionary.keys (frame G ids L Δ k n input v a) ⊆ U := by
  rw [frame_keys G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha]
  exact GeneralCoveringOwnerRoleFrames.ball_low G C targets D R L Δ hinc hlocal input hD hR hC hTargets a
    (anchor_low G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) (radius k n)

theorem frame_cover {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) :
    ball (fun w => SimpleGraph.neighborFinset J w) a (ActiveFiniteBitPartition.program ids Δ k t b n).rounds ⊆
      TaggedDictionary.keys (frame G ids L Δ k n input v a) := by
  rw [ActiveFiniteBitPartition.rounds,
    frame_keys G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha] <;>
    exact Finset.Subset.refl _

theorem evaluate_extended {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (ω : Coins Δ k b n) :
    evaluate ids Δ k t b n (frame G ids L Δ k n input v a) a ω =
      (ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J
        (fun u => (decide (u ∈ U), extend k b n (frame G ids L Δ k n input v a) ω u)) a := by
  let xs := frame G ids L Δ k n input v a
  let σ := fun u => (decide (u ∈ U), extend k b n xs ω u)
  have hc := frame_cover G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha
  have hl : ball (fun w => SimpleGraph.neighborFinset J w) a (ActiveFiniteBitPartition.program ids Δ k t b n).rounds ⊆
      (addresses xs).toFinset := by simpa only [addresses, Finset.sort_toFinset] using hc
  change FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs
    (seedRecords k b n xs ω) (true, zeroBits Δ k b n) a =
    (ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J σ a
  have hseed := seed_input k b n xs ω
    (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) U
    (frame_low G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha)
  have htransport : FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs
      (seedRecords k b n xs ω) (true, zeroBits Δ k b n) a =
      FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs
        (LocalSeedRecords.base (addresses xs) (fun i => σ ((addresses xs).get i))) (true, zeroBits Δ k b n) a :=
    congrArg (fun ys => FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs ys
      (true, zeroBits Δ k b n) a) hseed
  exact htransport.trans ((LocalSeedRecords.evaluate_base J (ActiveFiniteBitPartition.program ids Δ k t b n) xs (addresses xs) σ
    (true, zeroBits Δ k b n) a (frame_true G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) hc hl).trans
      (congrFun (Program.runEncoded_eq_run J (ActiveFiniteBitPartition.program ids Δ k t b n) σ) a).symm)

/-- The exact SAME public coin assignment is restricted to the bounded frame. -/
theorem evaluate_restricted {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (β : V → Bits Δ k b n) :
    evaluate ids Δ k t b n (frame G ids L Δ k n input v a) a (restrict k b n (frame G ids L Δ k n input v a) β) =
      (ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J (fun u => (decide (u ∈ U), β u)) a := by
  let xs := frame G ids L Δ k n input v a
  let σ := fun u => (decide (u ∈ U), β u)
  have hc := frame_cover G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha
  have hl : ball (fun w => SimpleGraph.neighborFinset J w) a (ActiveFiniteBitPartition.program ids Δ k t b n).rounds ⊆
      (addresses xs).toFinset := by simpa only [addresses, Finset.sort_toFinset] using hc
  change FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs
    (seedRecords k b n xs (restrict k b n xs β)) (true, zeroBits Δ k b n) a =
    (ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J σ a
  have hseed := seed_input_restrict k b n xs β
    (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) U
    (frame_low G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha)
  have htransport : FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs
      (seedRecords k b n xs (restrict k b n xs β)) (true, zeroBits Δ k b n) a =
      FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs
        (LocalSeedRecords.base (addresses xs) (fun i => σ ((addresses xs).get i))) (true, zeroBits Δ k b n) a :=
    congrArg (fun ys => FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n) xs ys
      (true, zeroBits Δ k b n) a) hseed
  exact htransport.trans ((LocalSeedRecords.evaluate_base J (ActiveFiniteBitPartition.program ids Δ k t b n) xs (addresses xs) σ
    (true, zeroBits Δ k b n) a (frame_true G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) hc hl).trans
      (congrFun (Program.runEncoded_eq_run J (ActiveFiniteBitPartition.program ids Δ k t b n) σ) a).symm)

theorem native_restricted {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (β : V → Bits Δ k b n) :
    ((program ids L Δ k t b n).runEncoded G input v).answer a (restrict k b n (frame G ids L Δ k n input v a) β) =
      some ((ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J (fun u => (decide (u ∈ U), β u)) a) := by
  have hlookup : TaggedDictionary.lookup (snapshot G ids L Δ k n input v).frames a =
      some (frame G ids L Δ k n input v a) :=
    GeneralCoveringOwnerRoleFrames.frame_lookup G ids L Δ (outerRadius k n) k (radius k n) input v a ha
  calc
    _ = query ids Δ k t b n (snapshot G ids L Δ k n input v) a
        (restrict k b n (frame G ids L Δ k n input v a) β) := native_query G ids L Δ k t b n input v a _
    _ = some (evaluate ids Δ k t b n (frame G ids L Δ k n input v a) a
        (restrict k b n (frame G ids L Δ k n input v a) β)) := query_lookup ids Δ k t b n _ a _ _ hlookup
    _ = _ := congrArg some (evaluate_restricted G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha β)

theorem native_common {idBits : ℕ} (ids : BitCode V idBits) (v w a : V)
    (hv : a ∈ (snapshot G ids L Δ k n input v).anchors)
    (hw : a ∈ (snapshot G ids L Δ k n input w).anchors) (β : V → Bits Δ k b n) :
    ((program ids L Δ k t b n).runEncoded G input v).answer a (restrict k b n (frame G ids L Δ k n input v a) β) =
      ((program ids L Δ k t b n).runEncoded G input w).answer a (restrict k b n (frame G ids L Δ k n input w a) β) := by
  exact (native_restricted G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a hv β).trans
    (native_restricted G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids w a hw β).symm

/-- Full label and boundary refer to ONE actual accepted active partition. -/
theorem native_correct {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (β : V → Bits Δ k b n) :
    let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
    ((program ids L Δ k t b n).runEncoded G input v).answer a (restrict k b n (frame G ids L Δ k n input v a) β) =
      some (DisjointPartLabels.label P.parts a, decide (a ∈ BoundaryOwners.vertices J U P.parts)) := by
  dsimp only
  calc
    _ = some ((ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J (fun u => (decide (u ∈ U), β u)) a) :=
      native_restricted G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha β
    _ = _ := congrArg some (ActiveFiniteBitPartition.correct J ids Δ k hk t ht b n U β
      (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a)

theorem part_event {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (β : V → Bits Δ k b n) (T : Finset V) :
    occurs (((program ids L Δ k t b n).runEncoded G input v).answer a
      (restrict k b n (frame G ids L Δ k n input v a) β)) T =
      decide (DisjointPartLabels.label (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts a = T) := by
  rw [native_correct G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v a ha β] <;> rfl

theorem same_boundary {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (β : V → Bits Δ k b n) :
    ((((program ids L Δ k t b n).runEncoded G input v).answer a
      (restrict k b n (frame G ids L Δ k n input v a) β)).map Prod.snd) =
      some (decide (a ∈ BoundaryOwners.vertices J U (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts)) := by
  rw [native_correct G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v a ha β] <;> rfl

theorem output_part {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (β : V → Bits Δ k b n) :
    let T := ((ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J (fun u => (decide (u ∈ U), β u)) a).1
    T ∈ (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts ∧ a ∈ T ∧ T.card ≤ k ∧
      ((J).induce (T : Set V)).Connected :=
  ActiveFiniteBitPartition.output_part J ids Δ k hk t ht b n U β
    (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a
    (anchor_low G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha)

theorem empty_low {idBits : ℕ} (ids : BitCode V idBits) [IsEmpty (Low D Q)] (v a : V) (ω : Coins Δ k b n) :
    ((program ids L Δ k t b n).runEncoded G input v).answer a ω = none := by
  rw [native_query, query]
  have he : (snapshot G ids L Δ k n input v).frames = [] :=
    (GeneralCoveringOwnerRoleFrames.empty_low G C targets D R L Δ (outerRadius k n) k (radius k n)
      hinc hlocal input hD hR hC hTargets ids v).2
  rw [he] <;> rfl
end Correct

theorem empty_physical [IsEmpty V] {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ k t b n).runEncoded G input = fun v => isEmptyElim v := by
  funext v
  exact isEmptyElim v

theorem rounds {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) :
    (program ids L Δ k t b n).rounds = 12 + 4 * outerRadius k n := by
  simp only [program, Program.rounds, GeneralCoveringOwnerRoleFrames.rounds, Nat.add_zero]

theorem maxBits_eq {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) :
    (program ids L Δ k t b n).maxBits =
      (GeneralCoveringOwnerRoleFrames.program ids L Δ (outerRadius k n) k (radius k n)).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]

theorem maxBits {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) :
    (program ids L Δ k t b n).maxBits ≤ max
      ((L + Δ + 3) * (idBits + (Δ + 1) ^ (outerRadius k n + 1) * (idBits + 1) + 2))
      (idBits + GeneralCoveringOwnerRootFrames.capacity Δ (outerRadius k n) * (idBits + Δ * (idBits + 1) + 1) + 1) := by
  rw [maxBits_eq]
  exact GeneralCoveringOwnerRoleFrames.maxBits ids L Δ (outerRadius k n) k (radius k n)

theorem logarithmic_public_card {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n c : ℕ)
    (hids : idBits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids L Δ k t b n).maxBits ≤ max
      ((L + Δ + 3) * (c + (Δ + 1) ^ (outerRadius k n + 1) * (c + 1) + 2))
      (c + GeneralCoveringOwnerRootFrames.capacity Δ (outerRadius k n) * (c + Δ * (c + 1) + 1) + 1) *
        Nat.clog 2 (Fintype.card V + 2) := by
  rw [maxBits_eq]
  exact GeneralCoveringOwnerRoleFrames.logarithmic_public_card ids L Δ (outerRadius k n) k (radius k n) c hids

end Paper.GeneralCoveringOwnerFramePartition

#print axioms Paper.GeneralCoveringOwnerFramePartition.slots_pos
#print axioms Paper.GeneralCoveringOwnerFramePartition.bit_positions
#print axioms Paper.GeneralCoveringOwnerFramePartition.restrict_slot
#print axioms Paper.GeneralCoveringOwnerFramePartition.extend_slot
#print axioms Paper.GeneralCoveringOwnerFramePartition.extend_restrict
#print axioms Paper.GeneralCoveringOwnerFramePartition.run_program
#print axioms Paper.GeneralCoveringOwnerFramePartition.source_retained
#print axioms Paper.GeneralCoveringOwnerFramePartition.native_query
#print axioms Paper.GeneralCoveringOwnerFramePartition.no_anchor
#print axioms Paper.GeneralCoveringOwnerFramePartition.env_retained
#print axioms Paper.GeneralCoveringOwnerFramePartition.private_input_retained
#print axioms Paper.GeneralCoveringOwnerFramePartition.frame_keys
#print axioms Paper.GeneralCoveringOwnerFramePartition.frame_true
#print axioms Paper.GeneralCoveringOwnerFramePartition.frame_capacity
#print axioms Paper.GeneralCoveringOwnerFramePartition.anchor_low
#print axioms Paper.GeneralCoveringOwnerFramePartition.frame_low
#print axioms Paper.GeneralCoveringOwnerFramePartition.frame_cover
#print axioms Paper.GeneralCoveringOwnerFramePartition.evaluate_extended
#print axioms Paper.GeneralCoveringOwnerFramePartition.evaluate_restricted
#print axioms Paper.GeneralCoveringOwnerFramePartition.native_restricted
#print axioms Paper.GeneralCoveringOwnerFramePartition.native_common
#print axioms Paper.GeneralCoveringOwnerFramePartition.native_correct
#print axioms Paper.GeneralCoveringOwnerFramePartition.part_event
#print axioms Paper.GeneralCoveringOwnerFramePartition.same_boundary
#print axioms Paper.GeneralCoveringOwnerFramePartition.output_part
#print axioms Paper.GeneralCoveringOwnerFramePartition.empty_low
#print axioms Paper.GeneralCoveringOwnerFramePartition.empty_physical
#print axioms Paper.GeneralCoveringOwnerFramePartition.rounds
#print axioms Paper.GeneralCoveringOwnerFramePartition.maxBits_eq
#print axioms Paper.GeneralCoveringOwnerFramePartition.maxBits
#print axioms Paper.GeneralCoveringOwnerFramePartition.logarithmic_public_card
