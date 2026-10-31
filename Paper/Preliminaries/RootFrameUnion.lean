import Paper.Owners.Construction.OwnerFramePayload
import Paper.Partitions.Local.FiniteBallAgreement

/-! Executable union of received bounded root frames. Balls and canonical
anchor frames are computed from finite records without a graph oracle. -/
namespace Paper.RootFrameUnion
open NeighborBalls
variable {V : Type} [LinearOrder V] {Δ r : ℕ}

def records (xs : List (V × OwnerFramePayload.Frame V Δ r)) : List (TopologyGather.Record V Δ) :=
  xs.flatMap (fun p => p.2.val)

def neighbors (xs : List (V × OwnerFramePayload.Frame V Δ r)) : V → Finset V :=
  FrameInterpreter.neighbors (records xs)

def anchors (k : ℕ) (xs : List (V × OwnerFramePayload.Frame V Δ r)) : Finset V :=
  (TaggedDictionary.keys xs).biUnion (fun u => ball (neighbors xs) u k)

def canonical (s : ℕ) (a : V) (xs : List (V × OwnerFramePayload.Frame V Δ r)) :
    List (TopologyGather.Record V Δ) :=
  (ball (neighbors xs) a s).sort.map
    (fun u => (u, ListPacket.truncate Δ ((neighbors xs u).sort (· ≤ ·))))

theorem keys_records (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (N : V → Finset V)
    (hkeys : ∀ p ∈ xs, TaggedDictionary.keys p.2.val = ball N p.1 r) :
    TaggedDictionary.keys (records xs) =
      (TaggedDictionary.keys xs).biUnion (fun u => ball N u r) := by
  ext w
  rw [records, TaggedDictionary.mem_keys_flatMap, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hw⟩
    exact ⟨p.1, (TaggedDictionary.mem_keys xs p.1).mpr ⟨p, hp, rfl⟩, hkeys p hp ▸ hw⟩
  · rintro ⟨u, hu, hw⟩
    obtain ⟨p, hp, he⟩ := (TaggedDictionary.mem_keys xs u).mp hu
    refine ⟨p, hp, ?_⟩
    rw [hkeys p hp, he]
    exact hw

theorem records_true (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (N : V → Finset V)
    (htrue : ∀ p ∈ xs, ∀ a ∈ p.2.val, a.2.val.toFinset = N a.1) :
    ∀ a ∈ records xs, a.2.val.toFinset = N a.1 := by
  intro a ha
  obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
  exact htrue p hp a ha

theorem neighbors_correct (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (N : V → Finset V)
    (htrue : ∀ p ∈ xs, ∀ a ∈ p.2.val, a.2.val.toFinset = N a.1)
    (u : V) (hu : u ∈ TaggedDictionary.keys (records xs)) : neighbors xs u = N u :=
  FrameInterpreter.neighbors_correct _ N (records_true xs N htrue) u hu

theorem subball_coverage (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (N : V → Finset V)
    (hkeys : ∀ p ∈ xs, TaggedDictionary.keys p.2.val = ball N p.1 r)
    (k s : ℕ) (hks : k + s ≤ r) (u a : V)
    (hu : u ∈ TaggedDictionary.keys xs) (ha : a ∈ ball N u k) :
    ball N a s ⊆ TaggedDictionary.keys (records xs) := by
  rw [keys_records xs N hkeys]
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨u, hu, monotone N u hks (subball N k s u a ha hw)⟩

theorem subball_eq (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (N : V → Finset V)
    (hkeys : ∀ p ∈ xs, TaggedDictionary.keys p.2.val = ball N p.1 r)
    (htrue : ∀ p ∈ xs, ∀ a ∈ p.2.val, a.2.val.toFinset = N a.1)
    (k s : ℕ) (hks : k + s ≤ r) (u a : V)
    (hu : u ∈ TaggedDictionary.keys xs) (ha : a ∈ ball N u k) :
    ball (neighbors xs) a s = ball N a s := by
  apply (FiniteBallAgreement.balls_eq N (neighbors xs) a s _).symm
  intro w hw
  exact (neighbors_correct xs N htrue w (subball_coverage xs N hkeys k s hks u a hu ha hw)).symm

theorem anchors_eq (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (N : V → Finset V)
    (hkeys : ∀ p ∈ xs, TaggedDictionary.keys p.2.val = ball N p.1 r)
    (htrue : ∀ p ∈ xs, ∀ a ∈ p.2.val, a.2.val.toFinset = N a.1)
    (k : ℕ) (hk : k ≤ r) :
    anchors k xs = (TaggedDictionary.keys xs).biUnion (fun u => ball N u k) := by
  apply Finset.biUnion_congr rfl
  intro u hu
  exact subball_eq xs N hkeys htrue 0 k (by omega) u u hu (self_mem N u 0)

theorem canonical_eq (xs : List (V × OwnerFramePayload.Frame V Δ r))
    (N : V → Finset V)
    (hkeys : ∀ p ∈ xs, TaggedDictionary.keys p.2.val = ball N p.1 r)
    (htrue : ∀ p ∈ xs, ∀ a ∈ p.2.val, a.2.val.toFinset = N a.1)
    (k s : ℕ) (hks : k + s ≤ r) (a : V) (ha : a ∈ anchors k xs) :
    canonical s a xs = (ball N a s).sort.map
      (fun u => (u, ListPacket.truncate Δ ((N u).sort (· ≤ ·)))) := by
  rw [anchors_eq xs N hkeys htrue k (by omega)] at ha
  obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
  unfold canonical
  rw [subball_eq xs N hkeys htrue k s hks u a hu hau]
  apply List.map_congr_left
  intro w hw
  have hw' : w ∈ ball N a s := (Finset.mem_sort (· ≤ ·)).mp hw
  rw [neighbors_correct xs N htrue w (subball_coverage xs N hkeys k s hks u a hu hau hw')]

end Paper.RootFrameUnion
