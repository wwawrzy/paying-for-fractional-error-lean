import Paper.Partitions.Local.PriorityBoundaryBroadcast
import Paper.Communication.ProgramMemory

/-! The actual virtual partition protocol exposes both a vertex's own
part and its boundary flag. The part is preserved privately in the final
boundary broadcast; no additional message is needed. -/
namespace Paper.PriorityTaskView
open BroadcastModel
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    Program V (PriorityPartitionBroadcast.Input Δ k Q n) (Bool × Finset V) :=
  .seq (PriorityPartitionBroadcast.program C Δ k t Q n hQ (PriorityTableCode.code Δ k Q n))
    (.seq (.local fun _ _ s => (s, s)) (ProgramMemory.carry (PartBoundaryBroadcast.program C k)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {b : ℕ} (C : BitCode V b) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (Q n : ℕ) (hQ : 0 < Q) (T : Finset V)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q n) (hdeg : ∀ u, G.degree u ≤ Δ) (v : V) :
    (program C Δ k t Q n hQ).run G (fun u => (decide (u ∈ T), ζ u)) v =
      (decide (v ∈ BoundaryOwners.vertices G T
        (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
          (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts),
       DisjointPartLabels.label
        (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
          (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts v) := by
  have he : (PriorityPartitionBroadcast.program C Δ k t Q n hQ (PriorityTableCode.code Δ k Q n)).run G
      (fun u => (decide (u ∈ T), ζ u)) =
        DisjointPartLabels.label (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
          (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts := by
    funext u
    exact PriorityPartitionBroadcast.correct G C Δ k hk t ht Q n hQ _ T ζ hdeg u
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G (PartBoundaryBroadcast.program C k)]
  dsimp only
  rw [he, PartBoundaryBroadcast.correct G C T k _ v]

theorem rounds {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    (program C Δ k t Q n hQ).rounds = n * (3 * k + 1) + 1 := by
  simp only [program, Program.rounds, ProgramMemory.rounds, PriorityPartitionBroadcast.rounds,
    PartBoundaryBroadcast.rounds, Nat.zero_add]

theorem maxBits {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    (program C Δ k t Q n hQ).maxBits =
      (PriorityBoundaryBroadcast.program C Δ k t Q n hQ).maxBits := by
  simp only [program, PriorityBoundaryBroadcast.program, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]

end Paper.PriorityTaskView
