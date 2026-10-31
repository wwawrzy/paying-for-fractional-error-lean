import Paper.Solver.LocalSearch.GeneralCoveringOwnerSimulation
import Paper.Preliminaries.TopologyGather
import Paper.Preliminaries.FrameInterpreter

/-! Actual arbitrary-C optional-owner bounded-radius topology frames.
Native VirtualPrepare executes ONCE,then the generic topology client is
translated on its ACTUAL public embedded low graph. All frame IDs are public
physical IDs;the physical dependency ball is never enumerated. These frames
are prerequisites for later local coin enumeration/forwarding,not a claim
that a center frame determines the entire fractional mean. -/
namespace Paper.GeneralCoveringOwnerTopologyGather
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

/-- Graph-free public program;only original private owner inputs are given. -/
def program {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ) :
    Program V (GeneralCoveringOwners.Input V)
      (List (TopologyGather.Record V Δ) × GeneralCoveringOwnerVirtualPrepare.Env V) :=
  .seq (.local (fun _ _ s => (s, ())))
    (GeneralCoveringOwnerSimulation.execute ids L Δ (TopologyGather.program ids Δ r))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem packed_run {In Out : Type} (P : Program V (In × Unit) Out) (input : V → In) :
    (Program.seq (Program.local (fun _ _ s => (s, ()))) P).runEncoded G input =
      P.runEncoded G (fun v => (input v, ())) := rfl

theorem execute_eq {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ) (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ r).runEncoded G input =
      (GeneralCoveringOwnerSimulation.execute ids L Δ (TopologyGather.program ids Δ r)).runEncoded G
        (fun v => (input v, ())) := by
  delta program
  exact packed_run G _ input

def received {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ) (input : V → GeneralCoveringOwners.Input V) (v : V) :=
  ((program ids L Δ r).runEncoded G input v).1

theorem env_retained {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ) (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r).runEncoded G input v).2 = GeneralCoveringOwnerSimulation.learned G ids L Δ input v := by
  rw [execute_eq]
  exact GeneralCoveringOwnerSimulation.execute_env G ids L Δ (TopologyGather.program ids Δ r) input (fun _ => ()) v

theorem private_input_retained {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ r).runEncoded G input v).2.metadata.owned.input = input v := by
  rw [execute_eq]
  exact GeneralCoveringOwnerSimulation.execute_private_input_retained G ids L Δ
    (TopologyGather.program ids Δ r) input (fun _ => ()) v

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).Adj := fun _ _ => Classical.propDecidable _

/-- Actual low-owner degree threshold,derived from its computed high set. -/
theorem public_degree (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    ∀ v, (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).degree v ≤ Δ :=
  GeneralCoveringOwnerVirtualPrepare.public_degree_bound G C D R L Δ

section Correct
variable (C targets : V → Finset V) (D R : Finset V) (L Δ r : ℕ)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q

/-- Full encoded record-list equality and the real retained Env. -/
theorem run_program {bits : ℕ} (ids : BitCode V bits) :
    (program ids L Δ r).runEncoded G input = fun v =>
      ((TopologyGather.program ids Δ r).run J (fun _ => ()) v,
        GeneralCoveringOwnerSimulation.learned G ids L Δ input v) := by
  rw [execute_eq]
  exact GeneralCoveringOwnerSimulation.execute_correct G ids C targets D R L Δ hinc hlocal
    input hD hR hC hTargets (TopologyGather.program ids Δ r) (fun _ => ())

/-- The REAL prepared neighbor list is bounded,not a supplied capacity fact. -/
theorem learned_degree {bits : ℕ} (ids : BitCode V bits) (v : V) :
    ((program ids L Δ r).runEncoded G input v).2.neighbors.card ≤ Δ := by
  rw [env_retained, (GeneralCoveringOwnerSimulation.learned_spec G ids C targets D R L Δ
    hinc hlocal input hD hR hC hTargets).2.2.2 v]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using public_degree G C D R L Δ v

theorem records {bits : ℕ} (ids : BitCode V bits) (v : V) (a : TopologyGather.Record V Δ) :
    a ∈ received G ids L Δ r input v ↔
      ∃ u, ∃ p : SimpleGraph.Walk J v u, p.length ≤ r ∧ a = TopologyGather.localData J Δ u := by
  delta received
  rw [run_program G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids]
  exact TopologyGather.records J ids Δ r (public_degree G C D R L Δ) v a

theorem record_true {bits : ℕ} (ids : BitCode V bits) (v : V) (a : TopologyGather.Record V Δ)
    (ha : a ∈ received G ids L Δ r input v) :
    ∃ u, ∃ p : SimpleGraph.Walk J v u, p.length ≤ r ∧ a.1 = u ∧ a.2.val = (SimpleGraph.neighborFinset J u).sort (· ≤ ·) := by
  obtain ⟨u, p, hp, rfl⟩ := (records G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v a).mp ha
  exact ⟨u, p, hp, rfl, TopologyGather.true_neighbors J Δ (public_degree G C D R L Δ) u⟩

/-- Exactly the frame-consistency contract of the EXISTING interpreter. -/
theorem consistent {bits : ℕ} (ids : BitCode V bits) (v : V) :
    ∀ a ∈ received G ids L Δ r input v, a.2.val.toFinset = SimpleGraph.neighborFinset J a.1 := by
  intro a ha
  obtain ⟨u, _, _, hk, hn⟩ := record_true G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v a ha
  rw [hn, hk]
  exact Finset.sort_toFinset _ _

/-- Complete keys in the ACTUAL virtual graph,not a physical dependency ball. -/
theorem keys {bits : ℕ} (ids : BitCode V bits) (v : V) :
    TaggedDictionary.keys (received G ids L Δ r input v) = NeighborBalls.ball (fun u => SimpleGraph.neighborFinset J u) v r := by
  ext k
  rw [TaggedDictionary.mem_keys]
  constructor
  · rintro ⟨a, ha, hk⟩
    obtain ⟨u, p, hp, he⟩ := (records G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v a).mp ha
    have huk : u = k := by rw [he] at hk; exact hk
    exact huk ▸ NeighborBallGraph.walk_mem J p r hp
  · intro hk
    obtain ⟨p, hp⟩ := NeighborBallGraph.exists_walk J v k r hk
    exact ⟨TopologyGather.localData J Δ k,
      (records G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v _).mpr ⟨k, p, hp, rfl⟩, rfl⟩

theorem key_count {bits : ℕ} (ids : BitCode V bits) (v : V) :
    (TaggedDictionary.keys (received G ids L Δ r input v)).card ≤ (Δ + 1) ^ r := by
  rw [keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]
  exact NeighborBallGraph.graph_card_bound J Δ (public_degree G C D R L Δ) v r

theorem frame_neighbors {bits : ℕ} (ids : BitCode V bits) (v u : V)
    (hu : u ∈ TaggedDictionary.keys (received G ids L Δ r input v)) :
    FrameInterpreter.neighbors (received G ids L Δ r input v) u = SimpleGraph.neighborFinset J u :=
  FrameInterpreter.neighbors_correct _ (fun w => SimpleGraph.neighborFinset J w)
    (consistent G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v) u hu

/-- Outside the actual low image,retain the SELF key with no virtual edges. -/
theorem keys_outside {bits : ℕ} (ids : BitCode V bits) (v : V)
    (hv : v ∉ GeneralCoveringOwnerVirtualPrepare.image D Q) :
    TaggedDictionary.keys (received G ids L Δ r input v) = {v} := by
  rw [keys G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v]
  have hn : SimpleGraph.neighborFinset J v = ∅ := GeneralCoveringOwnerVirtualPrepare.neighbor_outside G C D R L Q v hv
  cases r <;> simp [NeighborBalls.ball, hn]

theorem keys_noncenter {bits : ℕ} (ids : BitCode V bits) (v : V) (hv : v ∉ D) :
    TaggedDictionary.keys (received G ids L Δ r input v) = {v} := by
  apply keys_outside G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v
  intro h
  obtain ⟨i, he, _⟩ := (GeneralCoveringOwnerVirtualPrepare.mem_image D Q v).mp h
  exact hv (he ▸ i.property)

theorem keys_high {bits : ℕ} (ids : BitCode V bits) (i : D) (hi : i ∈ Q) :
    TaggedDictionary.keys (received G ids L Δ r input i.val) = {i.val} := by
  apply keys_outside G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids i.val
  intro h
  exact ((GeneralCoveringOwnerVirtualPrepare.low_image D Q i.val i.property).mp h) hi

theorem keys_empty_low {bits : ℕ} (ids : BitCode V bits) [IsEmpty (Low D Q)] (v : V) :
    TaggedDictionary.keys (received G ids L Δ r input v) = {v} := by
  apply keys_outside G C targets D R L Δ r hinc hlocal input hD hR hC hTargets ids v
  intro h
  obtain ⟨j, _, hj⟩ := (GeneralCoveringOwnerVirtualPrepare.mem_image D Q v).mp h
  exact isEmptyElim (⟨j, hj⟩ : Low D Q)
end Correct

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ r).runEncoded G input = fun v => isEmptyElim v := by
  funext v
  exact isEmptyElim v

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ) :
    (program ids L Δ r).rounds = 10 + 4 * r := by
  simp only [program, Program.rounds, GeneralCoveringOwnerSimulation.execute_rounds, TopologyGather.rounds, Nat.zero_add]

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L Δ r : ℕ) :
    (program ids L Δ r).maxBits ≤ (L + Δ + 3) * (bits + (Δ + 1) ^ (r + 1) * (bits + 1) + 2) := by
  simp only [program, Program.maxBits, Nat.zero_max]
  apply (GeneralCoveringOwnerSimulation.execute_maxBits ids L Δ (TopologyGather.program ids Δ r)).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_left (TopologyGather.maxBits ids Δ r) bits) 2)

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (L Δ r n c : ℕ)
    (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program ids L Δ r).maxBits ≤
      ((L + Δ + 3) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2)) * Nat.clog 2 (n + 2) := by
  simp only [program, Program.maxBits, Nat.zero_max]
  exact GeneralCoveringOwnerSimulation.execute_logarithmic_bits ids L Δ (TopologyGather.program ids Δ r) n c
    ((Δ + 1) ^ (r + 1) * (c + 1)) hids (TopologyGather.logarithmic_bits ids Δ r c n hids)

theorem logarithmic_public_card {bits : ℕ} (ids : BitCode V bits) (L Δ r c : ℕ)
    (hids : bits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids L Δ r).maxBits ≤
      ((L + Δ + 3) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2)) * Nat.clog 2 (Fintype.card V + 2) :=
  logarithmic_bits ids L Δ r (Fintype.card V) c hids

end Paper.GeneralCoveringOwnerTopologyGather

#print axioms Paper.GeneralCoveringOwnerTopologyGather.execute_eq
#print axioms Paper.GeneralCoveringOwnerTopologyGather.env_retained
#print axioms Paper.GeneralCoveringOwnerTopologyGather.private_input_retained
#print axioms Paper.GeneralCoveringOwnerTopologyGather.public_degree
#print axioms Paper.GeneralCoveringOwnerTopologyGather.run_program
#print axioms Paper.GeneralCoveringOwnerTopologyGather.learned_degree
#print axioms Paper.GeneralCoveringOwnerTopologyGather.records
#print axioms Paper.GeneralCoveringOwnerTopologyGather.record_true
#print axioms Paper.GeneralCoveringOwnerTopologyGather.consistent
#print axioms Paper.GeneralCoveringOwnerTopologyGather.keys
#print axioms Paper.GeneralCoveringOwnerTopologyGather.key_count
#print axioms Paper.GeneralCoveringOwnerTopologyGather.frame_neighbors
#print axioms Paper.GeneralCoveringOwnerTopologyGather.keys_outside
#print axioms Paper.GeneralCoveringOwnerTopologyGather.keys_noncenter
#print axioms Paper.GeneralCoveringOwnerTopologyGather.keys_high
#print axioms Paper.GeneralCoveringOwnerTopologyGather.keys_empty_low
#print axioms Paper.GeneralCoveringOwnerTopologyGather.empty_physical
#print axioms Paper.GeneralCoveringOwnerTopologyGather.rounds
#print axioms Paper.GeneralCoveringOwnerTopologyGather.maxBits
#print axioms Paper.GeneralCoveringOwnerTopologyGather.logarithmic_bits
#print axioms Paper.GeneralCoveringOwnerTopologyGather.logarithmic_public_card
