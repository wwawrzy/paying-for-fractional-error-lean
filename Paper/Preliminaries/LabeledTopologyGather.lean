import Paper.Preliminaries.TopologyGather

/-! Actual bounded-degree BC gathering of true neighbor lists and private
local labels. The label alphabet and its code are fixed public constants. -/
namespace Paper.LabeledTopologyGather
open BroadcastModel
variable {V A : Type} [LinearOrder V] [DecidableEq A]

abbrev Record (V A : Type) (Δ : ℕ) := V × ({l : List V // l.length ≤ Δ} × A)

def code {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (Δ : ℕ) :
    BitCode (Record V A Δ) (b + (Δ * (b + 1) + w)) :=
  PacketCode.product C (PacketCode.product (ListPacket.bounded C Δ) P)

def program {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (Δ r : ℕ) :
    Program V A (List (Record V A Δ)) :=
  .seq (.local fun v N s => [(v, (ListPacket.truncate Δ (N.sort (· ≤ ·)), s))])
    (BoundedGossip.program (code C P Δ) Δ 1 r)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def localData (Δ : ℕ) (s : V → A) (v : V) : Record V A Δ :=
  (v, (ListPacket.truncate Δ ((G.neighborFinset v).sort (· ≤ ·)), s v))

theorem records {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (Δ r : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (s : V → A) (v : V) (a : Record V A Δ) :
    a ∈ (program C P Δ r).run G s v ↔
      ∃ u, ∃ p : G.Walk v u, p.length ≤ r ∧ a = localData G Δ s u := by
  have hc := (BoundedGossip.correct G (code C P Δ) Δ 1 r (fun u => [localData G Δ s u]) hdeg
    (fun _ => by simp) (fun _ => by simp)).1 v
  change a ∈ (BoundedGossip.program (code C P Δ) Δ 1 r).run G (fun u => [localData G Δ s u]) v ↔ _
  constructor
  · intro ha
    have hm : a ∈ GossipKnowledge.knowledge G (fun u => ([localData G Δ s u]).toFinset) r v := by
      rw [← hc]
      exact List.mem_toFinset.mpr ha
    obtain ⟨u, p, hp, ha⟩ := GossipKnowledge.exists_walk G _ r v hm
    exact ⟨u, p, hp, by simpa using ha⟩
  · rintro ⟨u, p, hp, rfl⟩
    apply List.mem_toFinset.mp
    rw [hc]
    exact GossipKnowledge.of_walk G (fun u => ([localData G Δ s u]).toFinset) p r hp (by simp)

theorem true_neighbors (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (s : V → A) (v : V) :
    (localData G Δ s v).2.1.val = (G.neighborFinset v).sort (· ≤ ·) :=
  ListPacket.truncate_eq Δ _ (by simpa only [Finset.length_sort, SimpleGraph.card_neighborFinset_eq_degree] using hdeg v)

theorem rounds {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (Δ r : ℕ) :
    (program C P Δ r).rounds = r := by
  simp only [program, Program.rounds, BoundedGossip.program, Program.iterate_rounds,
    BoundedGossipRound.program, Nat.mul_one, Nat.zero_add]

theorem maxBits {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (Δ r : ℕ) :
    (program C P Δ r).maxBits ≤ (Δ + 1) ^ r * (b + (Δ * (b + 1) + w) + 1) := by
  simp only [program, Program.maxBits, Nat.zero_max, BoundedGossip.program]
  simpa only [Nat.one_mul] using Program.iterate_maxBits
    (BoundedGossipRound.program (V := V) (code C P Δ) (1 * (Δ + 1) ^ r)) r
end Paper.LabeledTopologyGather
