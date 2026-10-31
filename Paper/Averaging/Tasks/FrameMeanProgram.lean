import Paper.Averaging.Tasks.FiniteLocalMean
import Paper.Owners.Construction.OwnerFrameInterpreter

/-! A concrete bounded-numerator local averaging algorithm. All seed
arrays have a fixed public length, even when the received ball is smaller. -/
namespace Paper.FrameMeanProgram
open BroadcastModel
variable {V A : Type} [LinearOrder V] [Fintype A]

def compute {Δ : ℕ} (xs : List (TopologyGather.Record V Δ)) (K M : ℕ)
    (P : Program V A (Fin (M + 1))) (fallback : A) (v : V) :
    Fin (FiniteLocalMean.denominator A K * M + 1) :=
  let l := (TaggedDictionary.keys xs).sort (· ≤ ·)
  if hK : l.length ≤ K then
    ⟨FiniteLocalMean.numerator l hK (fun ys => (FrameInterpreter.evaluate P xs ys fallback v).val),
      Nat.lt_succ_of_le (FiniteLocalMean.numerator_le l hK _ M (fun _ => Nat.le_of_lt_succ (Fin.isLt _)))⟩
  else ⟨0, Nat.zero_lt_succ _⟩

def program {b : ℕ} (C : BitCode V b) (L Δ r M : ℕ)
    (P : Program V A (Fin (M + 1))) (fallback : A) :
    Program V (Bool × Bool) (Fin (FiniteLocalMean.denominator A ((Δ + 1) ^ r) * M + 1)) :=
  .seq (OwnerTopologyGather.program C L Δ r)
    (.local fun v _ s => compute s.1 ((Δ + 1) ^ r) M P fallback v)

variable [Fintype V] [Nonempty A] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem compute_mean {Δ : ℕ} (xs : List (TopologyGather.Record V Δ)) (K M : ℕ)
    (P : Program V A (Fin (M + 1))) (fallback : A) (v : V)
    (hxs : ∀ p ∈ xs, p.2.val.toFinset = G.neighborFinset p.1)
    (hx : NeighborBalls.ball (fun u => G.neighborFinset u) v P.rounds ⊆ TaggedDictionary.keys xs)
    (hK : (TaggedDictionary.keys xs).card ≤ K) :
    ((compute xs K M P fallback v).val : ℝ) / FiniteLocalMean.denominator A K =
      (∑ σ : V → A, ((P.run G σ v).val : ℝ)) / (Fintype.card (V → A) : ℝ) := by
  let l := (TaggedDictionary.keys xs).sort (· ≤ ·)
  have hlen : l.length ≤ K := by simpa only [l, Finset.length_sort] using hK
  have hl : l.Nodup := Finset.sort_nodup _ _
  have hcover : NeighborBalls.ball (fun u => G.neighborFinset u) v P.rounds ⊆ l.toFinset := by
    simpa only [l, Finset.sort_toFinset] using hx
  dsimp only [compute]
  rw [dif_pos hlen]
  rw [FiniteLocalMean.numerator_mean_eq l hl hlen]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [LocalSeedRecords.evaluate_base G P xs l σ fallback v hxs hx hcover]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

theorem correct {b : ℕ} (C : BitCode V b) (D S : Finset V)
    (hcover : S ⊆ SevenFoundation.covered G D) (L Δ r M : ℕ)
    (P : Program V A (Fin (M + 1))) (fallback : A) (hr : P.rounds ≤ r) (v : V) :
    (((program C L Δ r M P fallback).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).val : ℝ) /
        FiniteLocalMean.denominator A ((Δ + 1) ^ r) =
      (∑ σ : V → A, ((P.run (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) σ v).val : ℝ)) /
        (Fintype.card (V → A) : ℝ) := by
  change ((compute (OwnerFrameInterpreter.received G C D S L Δ r v) ((Δ + 1) ^ r) M P fallback v).val : ℝ) / _ = _
  apply compute_mean _ _ _ M P fallback v (OwnerFrameInterpreter.consistent G C D S hcover L Δ r v) _
    (OwnerFrameInterpreter.key_count G C D S hcover L Δ r v)
  rw [OwnerFrameInterpreter.keys G C D S hcover L Δ r v]
  exact NeighborBalls.monotone _ v hr

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r M : ℕ)
    (P : Program V A (Fin (M + 1))) (fallback : A) :
    (program C L Δ r M P fallback).rounds = 10 + 4 * r := by
  simp only [program, Program.rounds, OwnerTopologyGather.rounds, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r M : ℕ)
    (P : Program V A (Fin (M + 1))) (fallback : A) :
    (program C L Δ r M P fallback).maxBits = (OwnerTopologyGather.program C L Δ r).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ r M n c : ℕ)
    (P : Program V A (Fin (M + 1))) (fallback : A)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C L Δ r M P fallback).maxBits ≤
      ((L + Δ + 4) * (c + (Δ + 1) ^ (r + 1) * (c + 1) + 2)) * Nat.clog 2 (n + 2) := by
  rw [maxBits]
  exact OwnerTopologyGather.logarithmic_bits C L Δ r n c hids
end Paper.FrameMeanProgram
