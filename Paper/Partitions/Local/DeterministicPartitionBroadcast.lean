import Paper.Partitions.Local.DeterministicPartitionLocality
import Paper.Preliminaries.LabeledFrame
import Paper.Preliminaries.SmallNumberCode
import Paper.Communication.EncodedProgram

/-! A concrete broadcast program for one deterministic greedy stage.
Its inputs are current active bits and supplied finite vertex colors. The
program gathers actual finite records and computes the candidate masks
locally. It does not compute the power coloring supplied as input. -/
namespace Paper.DeterministicPartitionBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev Input (Φ : ℕ) := Bool × Fin Φ

def fallback (Φ : ℕ) (hΦ : 0 < Φ) : Input Φ := (false, ⟨0, hΦ⟩)

def active (Φ : ℕ) (hΦ : 0 < Φ) {Δ : ℕ}
    (xs : List (LabeledTopologyGather.Record V (Input Φ) Δ)) : Finset V :=
  (TaggedDictionary.keys xs).filter (fun u => (LabeledFrame.inputs xs (fallback Φ hΦ) u).1 = true)

def evaluate (Δ k t Φ q : ℕ) (hΦ : 0 < Φ)
    (xs : List (LabeledTopologyGather.Record V (Input Φ) Δ)) (v : V) : Finset V :=
  let M := LabeledFrame.neighbors xs
  let s := LabeledFrame.inputs xs (fallback Φ hΦ)
  DeterministicPartitionLocality.part (FiniteEligibility.family M (active Φ hΦ xs) k t)
    (DeterministicPartitionColors.color M Δ k v Φ (fun u => (s u).2)) q v

def program {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) :
    Program V (Input Φ) (Finset V) :=
  .seq (LabeledTopologyGather.program C (PacketCode.product BitCode.bool (SmallNumberCode.code Φ))
      Δ (q * k + 2 * k + 1))
    (.local fun v _ xs => evaluate Δ k t Φ q hΦ xs v)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem evaluate_correct (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) (S : Finset V) (χ : V → Fin Φ)
    (xs : List (LabeledTopologyGather.Record V (Input Φ) Δ)) (v : V)
    (hdeg : ∀ u, G.degree u ≤ Δ)
    (htrue : ∀ p ∈ xs, ∃ u, p = LabeledTopologyGather.localData G Δ (fun u => (decide (u ∈ S), χ u)) u)
    (hcover : NeighborBalls.ball (fun u => G.neighborFinset u) v (q * k + 2 * k + 1) ⊆
      TaggedDictionary.keys xs) :
    evaluate Δ k t Φ q hΦ xs v =
      DeterministicPartitionLocality.part
        (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k v Φ χ) q v := by
  let M := LabeledFrame.neighbors xs
  let F := TaggedDictionary.keys xs
  let s := LabeledFrame.inputs xs (fallback Φ hΦ)
  have hi : ∀ u ∈ F, s u = (decide (u ∈ S), χ u) :=
    fun u hu => LabeledFrame.inputs_correct G xs _ _ htrue u hu
  have hm : ∀ u ∈ F, M u = G.neighborFinset u :=
    fun u hu => LabeledFrame.neighbors_correct G xs _ hdeg htrue u hu
  have ha : active Φ hΦ xs = F ∩ S := by
    ext u
    simp only [active, Finset.mem_filter, Finset.mem_inter]
    change (u ∈ F ∧ (s u).1 = true) ↔ (u ∈ F ∧ u ∈ S)
    by_cases hu : u ∈ F
    · rw [hi u hu]
      simp only [decide_eq_true_eq]
    · simp only [hu, false_and]
  let E := FiniteEligibility.family M (F ∩ S) k t
  have hcolors : ∀ U ∈ E,
      DeterministicPartitionColors.color M Δ k v Φ (fun u => (s u).2) U =
        DeterministicPartitionColors.color M Δ k v Φ χ U := by
    intro U hU
    have hh := (FiniteEligibility.mem_family M (F ∩ S) U k t).mp hU
    have hne : U.Nonempty := by
      by_contra hn
      have hc := hh.2.1
      simp only [FiniteConnectivity.connected, dif_neg hn, Bool.false_eq_true] at hc
    have hl : FinitePriorityIndex.leader U v ∈ F := by
      apply Finset.inter_subset_left (hh.1 ?_)
      rw [FinitePriorityIndex.leader, dif_pos hne]
      exact Finset.min'_mem U hne
    have hχ : (s (FinitePriorityIndex.leader U v)).2 = χ (FinitePriorityIndex.leader U v) :=
      congrArg Prod.snd (hi _ hl)
    exact congrArg (fun a : Fin Φ =>
      (finProdFinEquiv (a, PriorityTableCode.masks ((Δ + 1) ^ k)
        (FinitePriorityIndex.index M Δ k U v).2)).val) hχ
  have he := DeterministicPartitionGreedy.congr_colors E
    (DeterministicPartitionColors.color M Δ k v Φ (fun u => (s u).2))
    (DeterministicPartitionColors.color M Δ k v Φ χ) hcolors q
  unfold evaluate
  rw [ha]
  change DeterministicPartitionLocality.part E
      (DeterministicPartitionColors.color M Δ k v Φ (fun u => (s u).2)) q v = _
  unfold DeterministicPartitionLocality.part DeterministicPartitionLocality.atVertex
  rw [he]
  exact DeterministicPartitionLocality.colored_part_eq G M F S v Δ k t v Φ χ q hm hcover

theorem correct {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ)
    (S : Finset V) (χ : V → Fin Φ) (hdeg : ∀ u, G.degree u ≤ Δ) (v : V) :
    (program C Δ k t Φ q hΦ).runEncoded G (fun u => (decide (u ∈ S), χ u)) v =
      DeterministicPartitionLocality.part
        (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k v Φ χ) q v := by
  rw [Program.runEncoded_eq_run]
  dsimp only [program, Program.run]
  apply evaluate_correct G Δ k t Φ q hΦ S χ _ v hdeg
  · exact LabeledFrame.gather_true G C (PacketCode.product BitCode.bool (SmallNumberCode.code Φ))
      Δ _ hdeg _ v
  · rw [LabeledFrame.gather_keys G C (PacketCode.product BitCode.bool (SmallNumberCode.code Φ))
      Δ _ hdeg _ v]

/-- Every root evaluates the same global candidate coloring: the
fallback identifier never affects any nonempty eligible candidate. -/
theorem correct_with_fallback {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ)
    (ht : 0 < t) (hΦ : 0 < Φ) (S : Finset V) (χ : V → Fin Φ)
    (hdeg : ∀ u, G.degree u ≤ Δ) (fallback : V) (v : V) :
    (program C Δ k t Φ q hΦ).runEncoded G (fun u => (decide (u ∈ S), χ u)) v =
      DeterministicPartitionLocality.part
        (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
        (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k fallback Φ χ) q v := by
  rw [correct G C Δ k t Φ q hΦ S χ hdeg v]
  unfold DeterministicPartitionLocality.part DeterministicPartitionLocality.atVertex
  rw [DeterministicPartitionGreedy.congr_colors
    (FiniteEligibility.family (fun u => G.neighborFinset u) S k t)
    (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k v Φ χ)
    (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k fallback Φ χ)
    (fun U hU => DeterministicPartitionColors.fallback_eq _ Δ k v fallback Φ χ U
      (DeterministicPartitionProgress.eligible_nonempty G S k t ht U hU)) q]

theorem output_part {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ)
    (ht : 0 < t) (hΦ : 0 < Φ) (S : Finset V) (χ : V → Fin Φ)
    (hdeg : ∀ u, G.degree u ≤ Δ) (fallback : V)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (U : Finset V)
    (hU : U ∈ DeterministicPartitionProgress.accepted (fun u => G.neighborFinset u) S k t
      (DeterministicPartitionColors.color (fun u => G.neighborFinset u) Δ k fallback Φ χ) q)
    (v : V) (hv : v ∈ U) :
    (program C Δ k t Φ q hΦ).runEncoded G (fun u => (decide (u ∈ S), χ u)) v = U := by
  rw [correct_with_fallback G C Δ k t Φ q ht hΦ S χ hdeg fallback v]
  exact DeterministicPartitionLocality.part_of_mem _ _
    (DeterministicPartitionColors.proper_eligible G Δ k hdeg fallback Φ χ hpower S t) q v U hU hv

theorem rounds {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) :
    (program C Δ k t Φ q hΦ).rounds = q * k + 2 * k + 1 := by
  simp only [program, Program.rounds, LabeledTopologyGather.rounds, Nat.add_zero]

theorem maxBits {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ) :
    (program C Δ k t Φ q hΦ).maxBits ≤
      (Δ + 1) ^ (q * k + 2 * k + 1) * (ids + (Δ * (ids + 1) + (1 + Φ)) + 1) := by
  simp only [program, Program.maxBits, Nat.max_zero]
  exact LabeledTopologyGather.maxBits C (PacketCode.product BitCode.bool (SmallNumberCode.code Φ)) Δ _

theorem logarithmic_bits {ids : ℕ} (C : BitCode V ids) (Δ k t Φ q : ℕ) (hΦ : 0 < Φ)
    (N c : ℕ) (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (program C Δ k t Φ q hΦ).maxBits ≤
      ((Δ + 1) ^ (q * k + 2 * k + 1) * (Δ + Φ + 3) * (c + 1)) * Nat.clog 2 (N + 2) := by
  apply (maxBits C Δ k t Φ q hΦ).trans
  calc
    _ ≤ ((Δ + 1) ^ (q * k + 2 * k + 1) * (Δ + Φ + 3)) * (ids + 1) := by
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith
    _ ≤ _ := ListPacket.logarithmic_width _ ids c N hids

end Paper.DeterministicPartitionBroadcast

#print axioms Paper.DeterministicPartitionBroadcast.correct
#print axioms Paper.DeterministicPartitionBroadcast.logarithmic_bits

#print axioms Paper.DeterministicPartitionBroadcast.output_part
