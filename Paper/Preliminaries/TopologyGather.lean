import Paper.Communication.BoundedGossip

/-! A concrete constant-round CONGEST_BC program gathers the complete
radius-R records in a bounded-degree graph. Every record contains an ID
and its true sorted neighbor list. The program has no graph argument. -/
namespace Paper.TopologyGather
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev Record (V : Type) (Δ : ℕ) := V × {l : List V // l.length ≤ Δ}

def code {b : ℕ} (C : BitCode V b) (Δ : ℕ) : BitCode (Record V Δ) (b + Δ * (b + 1)) :=
  PacketCode.product C (ListPacket.bounded C Δ)

def start (Δ : ℕ) : Program V Unit (List (Record V Δ)) :=
  .local (fun v N _ => [(v, ListPacket.truncate Δ (N.sort (· ≤ ·)))])

def program {b : ℕ} (C : BitCode V b) (Δ R : ℕ) : Program V Unit (List (Record V Δ)) :=
  .seq (start Δ) (BoundedGossip.program (code C Δ) Δ 1 R)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def localData (Δ : ℕ) (v : V) : Record V Δ :=
  (v, ListPacket.truncate Δ ((G.neighborFinset v).sort (· ≤ ·)))

theorem true_neighbors (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (localData G Δ v).2.val = (G.neighborFinset v).sort (· ≤ ·) := by
  apply ListPacket.truncate_eq
  simpa only [Finset.length_sort, SimpleGraph.card_neighborFinset_eq_degree] using hdeg v

theorem localData_injective (Δ : ℕ) : Function.Injective (localData G Δ) := by
  intro u v he
  exact congrArg Prod.fst he

theorem initial_run (Δ : ℕ) : (start (V := V) Δ).run G (fun _ => ()) = fun v => [localData G Δ v] := rfl

theorem run_gossip {b : ℕ} (C : BitCode V b) (Δ R : ℕ) :
    (program C Δ R).run G (fun _ => ()) =
      (BoundedGossip.program (code C Δ) Δ 1 R).run G (fun v => [localData G Δ v]) := rfl

set_option maxHeartbeats 1000000 in
theorem records {b : ℕ} (C : BitCode V b) (Δ R : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (v : V) (a : Record V Δ) :
    a ∈ ((program C Δ R).run G (fun _ => ()) v) ↔
      ∃ u, ∃ p : G.Walk v u, p.length ≤ R ∧ a = localData G Δ u := by
  have hc := (BoundedGossip.correct G (code C Δ) Δ 1 R (fun v => [localData G Δ v]) hdeg
    (fun _ => by simp) (fun _ => by simp)).1 v
  rw [run_gossip]
  constructor
  · intro ha
    have hm : a ∈ GossipKnowledge.knowledge G (fun u => ([localData G Δ u]).toFinset) R v := by
      rw [← hc]
      exact List.mem_toFinset.mpr ha
    obtain ⟨u, p, hp, hau⟩ := GossipKnowledge.exists_walk G _ R v hm
    exact ⟨u, p, hp, by simpa using hau⟩
  · rintro ⟨u, p, hp, rfl⟩
    apply List.mem_toFinset.mp
    rw [hc]
    exact GossipKnowledge.of_walk G (fun u => ([localData G Δ u]).toFinset) p R hp (by simp)

theorem rounds {b : ℕ} (C : BitCode V b) (Δ R : ℕ) : (program C Δ R).rounds = R := by
  simp only [program, Program.rounds, start, BoundedGossip.program, Program.iterate_rounds,
    BoundedGossipRound.program, mul_one, zero_add]

theorem maxBits {b : ℕ} (C : BitCode V b) (Δ R : ℕ) :
    (program C Δ R).maxBits ≤ (Δ + 1) ^ (R + 1) * (b + 1) := by
  have hb : (BoundedGossip.program (code C Δ) Δ 1 R).maxBits ≤
      1 * (Δ + 1) ^ R * ((b + Δ * (b + 1)) + 1) :=
    Program.iterate_maxBits (BoundedGossipRound.program (V := V) (code C Δ) _) R
  have he : 1 * (Δ + 1) ^ R * ((b + Δ * (b + 1)) + 1) = (Δ + 1) ^ (R + 1) * (b + 1) := by
    rw [pow_succ]
    ring
  rw [he] at hb
  exact max_le (Nat.zero_le _) hb

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (Δ R c n : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C Δ R).maxBits ≤ ((Δ + 1) ^ (R + 1) * (c + 1)) * Nat.clog 2 (n + 2) :=
  (maxBits C Δ R).trans (ListPacket.logarithmic_width _ b c n hids)
end Paper.TopologyGather
