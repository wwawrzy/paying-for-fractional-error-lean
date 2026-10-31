import Paper.Preliminaries.FrameInterpreter
import Paper.Owners.Construction.OwnerTopologyGather

/-! The local interpreter is fed by actual physical BC topology gathering.
Private finite seed tables are carried without messages. -/
namespace Paper.OwnerFrameInterpreter
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def program {In Out : Type} {b : ℕ} (C : BitCode V b) (L Δ r : ℕ)
    (P : Program V In Out) : Program V ((Bool × Bool) × (List (V × In) × In)) Out :=
  .seq (ProgramMemory.carry (OwnerTopologyGather.program C L Δ r))
    (.local fun v _ s => FrameInterpreter.evaluate P s.1.1 s.2.1 s.2.2 v)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

def received {b : ℕ} (C : BitCode V b) (D S : Finset V) (L Δ r : ℕ) (v : V) :=
  ((OwnerTopologyGather.program C L Δ r).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1

theorem consistent {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) : ∀ p ∈ received G C D S L Δ r v,
      p.2.val.toFinset = (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset p.1 := by
  intro p hp
  obtain ⟨u, _, _, hk, hn⟩ := OwnerTopologyGather.record_true G C D S hcover L Δ r v p hp
  rw [hn, hk]
  exact Finset.sort_toFinset _ _

theorem keys {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) : TaggedDictionary.keys (received G C D S L Δ r v) =
      NeighborBalls.ball (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u) v r := by
  ext k
  rw [TaggedDictionary.mem_keys]
  constructor
  · rintro ⟨a, ha, hk⟩
    obtain ⟨u, p, hp, he⟩ := (OwnerTopologyGather.records G C D S hcover L Δ r v a).mp ha
    have huk : u = k := by rw [he] at hk; exact hk
    exact huk ▸ NeighborBallGraph.walk_mem _ p r hp
  · intro hk
    obtain ⟨p, hp⟩ := NeighborBallGraph.exists_walk _ v k r hk
    exact ⟨TopologyGather.localData _ Δ k,
      (OwnerTopologyGather.records G C D S hcover L Δ r v _).mpr ⟨k, p, hp, rfl⟩, rfl⟩

theorem correct {In Out : Type} {b : ℕ} (C : BitCode V b)
    (D S : Finset V) (hcover : S ⊆ covered G D) (L Δ r : ℕ) (P : Program V In Out)
    (hr : P.rounds ≤ r) (seeds : V → List (V × In)) (fallback : V → In)
    (s : V → In) (v : V)
    (hs : TaggedDictionary.Consistent s (seeds v))
    (hkeys : NeighborBalls.ball
      (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u)
      v P.rounds ⊆ TaggedDictionary.keys (seeds v)) :
    (program C L Δ r P).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ S)), (seeds u, fallback u))) v =
      P.run (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) s v := by
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G (OwnerTopologyGather.program C L Δ r)]
  apply FrameInterpreter.correct _ P (received G C D S L Δ r v) (seeds v) (fallback v) s v
    (consistent G C D S hcover L Δ r v) hs _ hkeys
  rw [keys G C D S hcover L Δ r v]
  exact NeighborBalls.monotone _ v hr

theorem rounds {In Out : Type} {b : ℕ} (C : BitCode V b) (L Δ r : ℕ)
    (P : Program V In Out) : (program C L Δ r P).rounds = 10 + 4 * r := by
  simp only [program, Program.rounds, ProgramMemory.rounds, Nat.add_zero, OwnerTopologyGather.rounds]

theorem maxBits {In Out : Type} {b : ℕ} (C : BitCode V b) (L Δ r : ℕ)
    (P : Program V In Out) : (program C L Δ r P).maxBits = (OwnerTopologyGather.program C L Δ r).maxBits := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero]

theorem logarithmic_bits {In Out : Type} {b : ℕ} (C : BitCode V b) (L Δ r n c : ℕ)
    (P : Program V In Out) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C L Δ r P).maxBits ≤
      ((L + Δ + 4) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2)) * Nat.clog 2 (n + 2) := by
  rw [maxBits]
  exact OwnerTopologyGather.logarithmic_bits C L Δ r n c hids

theorem key_count {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) : (TaggedDictionary.keys (received G C D S L Δ r v)).card ≤ (Δ + 1) ^ r := by
  rw [keys G C D S hcover L Δ r v]
  exact NeighborBallGraph.graph_card_bound _ Δ (PublicOwners.degree_bound G D S L Δ) v r
end Paper.OwnerFrameInterpreter
