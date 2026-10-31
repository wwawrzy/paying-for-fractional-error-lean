import Paper.Preliminaries.LabeledFrame
import Paper.Partitions.Local.PartitionFrameLocality

/-! A concrete bounded-degree BC priority partition: gather finite true
topology, active bits and own seed tables, then execute the finite kernel. -/
namespace Paper.PriorityPartitionBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev Table (Δ k Q n : ℕ) := (Fin n × (Fin ((Δ + 1) ^ k) → Bool)) → Fin Q
abbrev Input (Δ k Q n : ℕ) := Bool × Table Δ k Q n

def fallback (Δ k Q n : ℕ) (hQ : 0 < Q) : Input Δ k Q n := (false, fun _ => ⟨0, hQ⟩)

def active (Δ k Q n : ℕ) (hQ : 0 < Q)
    (xs : List (LabeledTopologyGather.Record V (Input Δ k Q n) Δ)) : Finset V :=
  (TaggedDictionary.keys xs).filter (fun u => (LabeledFrame.inputs xs (fallback Δ k Q n hQ) u).1 = true)

def evaluate (Δ k t Q n : ℕ) (hQ : 0 < Q)
    (xs : List (LabeledTopologyGather.Record V (Input Δ k Q n) Δ)) (v : V) : Finset V :=
  let N := LabeledFrame.neighbors xs
  let s := LabeledFrame.inputs xs (fallback Δ k Q n hQ)
  FinitePartLabels.label N k t (active Δ k Q n hQ xs) n
    (PartitionFrameLocality.seeds N Δ k v Q n (fun i u mask => (s u).2 (i, mask))) v

def program {b w : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q)
    (P : BitCode (Table Δ k Q n) w) : Program V (Input Δ k Q n) (Finset V) :=
  .seq (LabeledTopologyGather.program C (PacketCode.product BitCode.bool P) Δ (n * (3 * k + 1)))
    (.local fun v _ s => evaluate Δ k t Q n hQ s v)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem evaluate_correct (Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t)
    (Q n : ℕ) (hQ : 0 < Q) (T : Finset V) (ζ : V → Table Δ k Q n)
    (xs : List (LabeledTopologyGather.Record V (Input Δ k Q n) Δ)) (v : V)
    (hdeg : ∀ u, G.degree u ≤ Δ)
    (htrue : ∀ p ∈ xs, ∃ u, p = LabeledTopologyGather.localData G Δ (fun u => (decide (u ∈ T), ζ u)) u)
    (hcover : NeighborBalls.ball (fun u => G.neighborFinset u) v (n * (3 * k + 1)) ⊆ TaggedDictionary.keys xs) :
    evaluate Δ k t Q n hQ xs v =
      (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
        (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts.biUnion
          (fun U => if v ∈ U then U else ∅) := by
  have hi : ∀ u ∈ TaggedDictionary.keys xs,
      LabeledFrame.inputs xs (fallback Δ k Q n hQ) u = (decide (u ∈ T), ζ u) :=
    fun u hu => LabeledFrame.inputs_correct G xs _ _ htrue u hu
  have ha : active Δ k Q n hQ xs = TaggedDictionary.keys xs ∩ T := by
    ext u
    by_cases hu : u ∈ TaggedDictionary.keys xs
    · simp only [active, Finset.mem_filter, Finset.mem_inter, hi u hu, decide_eq_true_eq]
    · simp only [active, Finset.mem_filter, Finset.mem_inter, hu, false_and]
  unfold evaluate
  rw [ha]
  apply PartitionFrameLocality.local_math_label G (LabeledFrame.neighbors xs) (TaggedDictionary.keys xs) T v v
    Δ k hk t ht Q hQ n _ (fun i u mask => ζ u (i, mask))
  · exact fun u hu => LabeledFrame.neighbors_correct G xs _ hdeg htrue u hu
  · exact hcover
  · intro i u hu
    funext mask
    rw [hi u hu]

theorem correct {b w : ℕ} (C : BitCode V b) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (Q n : ℕ) (hQ : 0 < Q) (P : BitCode (Table Δ k Q n) w)
    (T : Finset V) (ζ : V → Table Δ k Q n) (hdeg : ∀ u, G.degree u ≤ Δ) (v : V) :
    (program C Δ k t Q n hQ P).run G (fun u => (decide (u ∈ T), ζ u)) v =
      (PriorityPartition.partition G k hk (1 / (t : ℝ)) T n
        (PriorityNormalization.localSeed G Δ k Q hQ n (fun p => ζ p.2.1 (p.1, p.2.2)))).parts.biUnion
          (fun U => if v ∈ U then U else ∅) := by
  dsimp only [program, Program.run]
  apply evaluate_correct G Δ k hk t ht Q n hQ T ζ _ v hdeg
  · exact LabeledFrame.gather_true G C (PacketCode.product BitCode.bool P) Δ _ hdeg _ v
  · rw [LabeledFrame.gather_keys G C (PacketCode.product BitCode.bool P) Δ _ hdeg _ v]

theorem rounds {b w : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q)
    (P : BitCode (Table Δ k Q n) w) : (program C Δ k t Q n hQ P).rounds = n * (3 * k + 1) := by
  simp only [program, Program.rounds, LabeledTopologyGather.rounds, Nat.add_zero]

theorem maxBits {b w : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q)
    (P : BitCode (Table Δ k Q n) w) : (program C Δ k t Q n hQ P).maxBits ≤
      (Δ + 1) ^ (n * (3 * k + 1)) * (b + (Δ * (b + 1) + (1 + w)) + 1) := by
  simp only [program, Program.maxBits, Nat.max_zero]
  exact LabeledTopologyGather.maxBits C (PacketCode.product BitCode.bool P) Δ _

theorem logarithmic_bits {b w : ℕ} (C : BitCode V b) (Δ k t Q n : ℕ) (hQ : 0 < Q)
    (P : BitCode (Table Δ k Q n) w) (N c : ℕ) (hids : b ≤ c * Nat.clog 2 (N + 2)) :
    (program C Δ k t Q n hQ P).maxBits ≤
      ((Δ + 1) ^ (n * (3 * k + 1)) * (Δ + w + 3) * (c + 1)) * Nat.clog 2 (N + 2) := by
  apply (maxBits C Δ k t Q n hQ P).trans
  calc
    _ ≤ ((Δ + 1) ^ (n * (3 * k + 1)) * (Δ + w + 3)) * (b + 1) := by
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith
    _ ≤ _ := ListPacket.logarithmic_width _ b c N hids
end Paper.PriorityPartitionBroadcast
