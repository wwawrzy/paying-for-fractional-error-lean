import Paper.Partitions.Local.PriorityTableCode
import Paper.Communication.PartBoundaryBroadcast

/-! Concrete virtual BC boundary flag for the actual priority partition. -/
namespace Paper.PriorityBoundaryBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    Program V (PriorityPartitionBroadcast.Input Δ k Q n) Bool :=
  .seq (PriorityPartitionBroadcast.program C Δ k t Q n hQ (PriorityTableCode.code Δ k Q n))
    (PartBoundaryBroadcast.program C k)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {b : ℕ} (C : BitCode V b) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (Q n : ℕ) (hQ : 0 < Q) (T : Finset V)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q n) (hdeg : ∀ u, G.degree u ≤ Δ) (v : V) :
    (program C Δ k t Q n hQ).run G (fun u => (decide (u ∈ T), ζ u)) v =
      decide (v ∈ BoundaryOwners.vertices G T
        (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
          (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts) := by
  have he : (PriorityPartitionBroadcast.program C Δ k t Q n hQ (PriorityTableCode.code Δ k Q n)).run G
      (fun u => (decide (u ∈ T), ζ u)) =
        DisjointPartLabels.label (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
          (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts := by
    funext u
    exact PriorityPartitionBroadcast.correct G C Δ k hk t ht Q n hQ _ T ζ hdeg u
  change (PartBoundaryBroadcast.program C k).run G
    ((PriorityPartitionBroadcast.program C Δ k t Q n hQ (PriorityTableCode.code Δ k Q n)).run G
      (fun u => (decide (u ∈ T), ζ u))) v = _
  rw [he]
  exact PartBoundaryBroadcast.correct G C T k _ v

theorem rounds {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q) :
    (program C Δ k t Q n hQ).rounds = n * (3 * k + 1) + 1 := by
  simp only [program, Program.rounds, PriorityPartitionBroadcast.rounds, PartBoundaryBroadcast.rounds]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q)
    (N c : ℕ) (hids : b ≤ c * Nat.clog 2 (N + 2)) :
    (program C Δ k t Q n hQ).maxBits ≤
      (((Δ + 1) ^ (n * (3 * k + 1)) * (Δ + (n * 2 ^ ((Δ + 1) ^ k)) * Q + 3) + k) *
        (c + 1)) * Nat.clog 2 (N + 2) := by
  change max (PriorityPartitionBroadcast.program C Δ k t Q n hQ (PriorityTableCode.code Δ k Q n)).maxBits
    (PartBoundaryBroadcast.program C k).maxBits ≤ _
  apply max_le
  · apply (PriorityPartitionBroadcast.logarithmic_bits C Δ k t Q n hQ (PriorityTableCode.code Δ k Q n) N c hids).trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ k))
  · rw [PartBoundaryBroadcast.maxBits]
    apply (ListPacket.logarithmic_width k b c N hids).trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left k _))
end Paper.PriorityBoundaryBroadcast
