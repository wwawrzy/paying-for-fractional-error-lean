import Paper.Owners.Construction.OwnerFrameInterpreter

/-! Real bounded packets for canonical true low-owner topology frames.
Normalize only by public ID keys; no order/equality of whole frames needed. -/
namespace Paper.OwnerFramePayload
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def capacity (Δ r : ℕ) : ℕ := (Δ + 1) ^ r
abbrev Frame (V : Type) (Δ r : ℕ) := {l : List (TopologyGather.Record V Δ) // l.length ≤ capacity Δ r}

def code {b : ℕ} (C : BitCode V b) (Δ r : ℕ) :
    BitCode (Frame V Δ r) (capacity Δ r * ((b + Δ * (b + 1)) + 1)) :=
  ListPacket.bounded (TopologyGather.code C Δ) (capacity Δ r)

def packet (Δ r : ℕ) (xs : List (TopologyGather.Record V Δ)) : Frame V Δ r :=
  TaggedDictionary.bounded (capacity Δ r) xs

def program {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) :
    Program V (Bool × Bool) (Frame V Δ r × OwnerVirtualPrepare.Env V) :=
  .seq (OwnerTopologyGather.program C L Δ r) (.local fun _ _ s => (packet Δ r s.1, s.2))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

theorem frame_keys {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) :
    TaggedDictionary.keys (((program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1).val =
      NeighborBalls.ball (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u) v r := by
  change TaggedDictionary.keys (packet Δ r (OwnerFrameInterpreter.received G C D S L Δ r v)).val = _
  rw [packet, capacity, TaggedDictionary.keys_bounded_eq _ _ (OwnerFrameInterpreter.key_count G C D S hcover L Δ r v)]
  exact OwnerFrameInterpreter.keys G C D S hcover L Δ r v

theorem record_true {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) (a : TopologyGather.Record V Δ)
    (ha : a ∈ (((program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1).val) :
    a.2.val.toFinset = (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset a.1 := by
  have hm := TaggedDictionary.bounded_mem (capacity Δ r)
    (OwnerFrameInterpreter.received G C D S L Δ r v) a ha
  exact OwnerFrameInterpreter.consistent G C D S hcover L Δ r v a hm

theorem env {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) :
    ((program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).2 =
      OwnerVirtualCorrect.learned G C D S L Δ v := by
  change ((OwnerTopologyGather.program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).2 = _
  rw [OwnerTopologyGather.run_program G C D S hcover L Δ r]

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) : (program C L Δ r).rounds = 10 + 4 * r := by
  simp only [program, Program.rounds, OwnerTopologyGather.rounds, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r : ℕ) :
    (program C L Δ r).maxBits = (OwnerTopologyGather.program C L Δ r).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]
end Paper.OwnerFramePayload
