import Paper.Preliminaries.LowBoundarySeedScore
import Paper.Averaging.Tasks.FrameMeanProgram

/-! A genuine deterministic physical BC computes the exact expected
boundary indicator by finite local enumeration, with fixed denominator. -/
namespace Paper.OwnerBoundaryMean
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def radius (k n : ℕ) : ℕ := n * (3 * k + 1) + 1
def slots (Δ k n : ℕ) : ℕ := (Δ + 1) ^ radius k n
def denominator (Δ k Q n : ℕ) : ℕ :=
  FiniteLocalMean.denominator (PriorityPartitionBroadcast.Table Δ k Q n) (slots Δ k n)

theorem denominator_explicit (Δ k Q n : ℕ) :
    denominator Δ k Q n = (Q ^ (n * 2 ^ ((Δ + 1) ^ k))) ^ ((Δ + 1) ^ radius k n) := by
  simp only [denominator, FiniteLocalMean.denominator, slots, PriorityPartitionBroadcast.Table,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]

theorem denominator_pos (Δ k Q n : ℕ) (hQ : 0 < Q) : 0 < denominator Δ k Q n := by
  rw [denominator_explicit]
  exact pow_pos (pow_pos hQ _) _

def compute {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q)
    (xs : List (TopologyGather.Record V Δ)) (v : V) : Fin (denominator Δ k Q n + 1) :=
  let out := FrameMeanProgram.compute xs (slots Δ k n) 1
    (LowBoundarySeedScore.program C Δ k t Q n hQ) (fun _ => ⟨0, hQ⟩) v
  ⟨out.val, by simpa only [Nat.mul_one] using out.isLt⟩

def program {b : ℕ} (C : BitCode V b) (L Δ k t Q n : ℕ) (hQ : 0 < Q) :
    Program V (Bool × Bool) (Fin (denominator Δ k Q n + 1)) :=
  .seq (OwnerTopologyGather.program C L Δ (radius k n))
    (.local fun v _ s => if s.2.low then compute C Δ k t Q n hQ s.1 v else ⟨0, Nat.zero_lt_succ _⟩)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

theorem root_correct {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q n : ℕ) (hQ : 0 < Q) (v : V)
    (hv : v ∈ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) :
    (((program C L Δ k t Q n hQ).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).val : ℝ) /
        denominator Δ k Q n =
      (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q n,
        ((decide (v ∈ BoundaryOwners.vertices
          (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ))
          (PriorityPartition.partition (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
            k hk (1 / (t : ℝ)) (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) n
            (PriorityNormalization.localSeed (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
              Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts)).toNat : ℝ)) /
        (Fintype.card (V → PriorityPartitionBroadcast.Table Δ k Q n) : ℝ) := by
  letI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hflag : (((OwnerTopologyGather.program C L Δ (radius k n)).run G
      (fun u => (decide (u ∈ D), decide (u ∈ S))) v).2).low = true := by
    rw [OwnerTopologyGather.run_program G C D S hcover L Δ (radius k n)]
    rw [(OwnerVirtualCorrect.spec G C D S hcover L Δ v).2.1, decide_eq_true hv]
  dsimp only [program, Program.run]
  simp only [hflag, ↓reduceIte]
  change ((FrameMeanProgram.compute (OwnerFrameInterpreter.received G C D S L Δ (radius k n) v)
    (slots Δ k n) 1 (LowBoundarySeedScore.program C Δ k t Q n hQ) (fun _ => ⟨0, hQ⟩) v).val : ℝ) / _ = _
  dsimp only [denominator, slots]
  rw [FrameMeanProgram.compute_mean
    (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) _ _ 1
    (LowBoundarySeedScore.program C Δ k t Q n hQ) (fun _ => ⟨0, hQ⟩) v
    (OwnerFrameInterpreter.consistent G C D S hcover L Δ (radius k n) v)
    (by
      rw [OwnerFrameInterpreter.keys G C D S hcover L Δ (radius k n) v, LowBoundarySeedScore.rounds]
      exact Finset.Subset.refl _)
    (OwnerFrameInterpreter.key_count G C D S hcover L Δ (radius k n) v)]
  congr 1
  apply Finset.sum_congr rfl
  intro ζ _
  rw [LowBoundarySeedScore.root_correct G C D S L Δ k hk t ht Q n hQ ζ v hv]

theorem outside {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ k t Q n : ℕ) (hQ : 0 < Q) (v : V)
    (hv : v ∉ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) :
    ((program C L Δ k t Q n hQ).run G (fun u => (decide (u ∈ D), decide (u ∈ S))) v).val = 0 := by
  have hflag : (((OwnerTopologyGather.program C L Δ (radius k n)).run G
      (fun u => (decide (u ∈ D), decide (u ∈ S))) v).2).low = false := by
    rw [OwnerTopologyGather.run_program G C D S hcover L Δ (radius k n)]
    rw [(OwnerVirtualCorrect.spec G C D S hcover L Δ v).2.1, decide_eq_false hv]
  dsimp only [program, Program.run]
  simp only [hflag, Bool.false_eq_true, ↓reduceIte]

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ k t Q n : ℕ) (hQ : 0 < Q) :
    (program C L Δ k t Q n hQ).rounds = 10 + 4 * radius k n := by
  simp only [program, Program.rounds, OwnerTopologyGather.rounds, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ k t Q n : ℕ) (hQ : 0 < Q) :
    (program C L Δ k t Q n hQ).maxBits = (OwnerTopologyGather.program C L Δ (radius k n)).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (L Δ k t Q n : ℕ) (hQ : 0 < Q)
    (N c : ℕ) (hids : b ≤ c * Nat.clog 2 (N + 2)) :
    (program C L Δ k t Q n hQ).maxBits ≤
      ((L + Δ + 4) * (c + (Δ + 1) ^ (radius k n + 1) * (c + 1) + 2)) * Nat.clog 2 (N + 2) := by
  rw [maxBits]
  exact OwnerTopologyGather.logarithmic_bits C L Δ (radius k n) N c hids
end Paper.OwnerBoundaryMean
