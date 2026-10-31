import Paper.Partitions.Local.HumanPartition
import Paper.Partitions.Local.PriorityTableCode
import Paper.Communication.EncodedProgram

/-! Uniform finite-bit partitions with an actual broadcast implementation.
Each vertex supplies an independent Boolean table of fixed size. A bijection
with uniform finite priorities transports the exact finite expectation. -/
namespace Paper.CurrentFiniteBitPartition
open BroadcastModel
open scoped BigOperators

abbrev Index (Δ k n : ℕ) := Fin n × (Fin ((Δ + 1) ^ k) → Bool)
abbrev Bits (Δ k b n : ℕ) := Index Δ k n → Fin b → Bool

def table (Δ k b n : ℕ) (β : Bits Δ k b n) :
    PriorityPartitionBroadcast.Table Δ k (2 ^ b) n :=
  fun i => PriorityTableCode.masks b (β i)

/-- Every possible assignment of local fair bits has exactly one finite
priority assignment, and conversely. Thus no biased sampling is hidden. -/
def sourceEquiv (V : Type) (Δ k b n : ℕ) :
    (V → Bits Δ k b n) ≃ ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b)) where
  toFun β p := PriorityTableCode.masks b (β p.2.1 (p.1, p.2.2))
  invFun ω v i := (PriorityTableCode.masks b).symm (ω (i.1, v, i.2))
  left_inv β := by funext v i; exact (PriorityTableCode.masks b).symm_apply_apply _
  right_inv ω := by funext p; exact (PriorityTableCode.masks b).apply_symm_apply _

theorem bits_per_vertex (Δ k b n : ℕ) :
    Fintype.card (Index Δ k n × Fin b) = n * 2 ^ ((Δ + 1) ^ k) * b := by
  simp [Index, Fintype.card_prod]

variable {V : Type} [LinearOrder V]

def program {ids : ℕ} (C : BitCode V ids) (Δ k t b n : ℕ) :
    Program V (Bits Δ k b n) (Finset V) :=
  .seq (.local fun _ _ β => (true, table Δ k b n β))
    (PriorityPartitionBroadcast.program C Δ k t (2 ^ b) n (by positivity)
      (PriorityTableCode.code Δ k (2 ^ b) n))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def partition (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ)
    (β : V → Bits Δ k b n) : SmallParts.Data G Finset.univ k :=
  PriorityPartition.partition G k hk (1 / (t : ℝ)) Finset.univ n
    (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n
      (sourceEquiv V Δ k b n β))

theorem output_eq {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (program C Δ k t b n).runEncoded G β v =
      (partition G Δ k hk t b n β).parts.biUnion (fun U => if v ∈ U then U else ∅) := by
  rw [Program.runEncoded_eq_run]
  have hh := PriorityPartitionBroadcast.correct G C Δ k hk t ht (2 ^ b) n
    (by positivity) (PriorityTableCode.code Δ k (2 ^ b) n) Finset.univ
    (fun u => table Δ k b n (β u)) hdeg v
  simpa only [program, Program.run, Finset.mem_univ, decide_true, table, partition,
    sourceEquiv, Equiv.coe_fn_mk] using hh

/-- The complete output at a vertex is its unique connected part, not
merely a part identifier or a boundary bit. -/
theorem output_part {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    let U := (program C Δ k t b n).runEncoded G β v
    U ∈ (partition G Δ k hk t b n β).parts ∧ v ∈ U ∧
      U.card ≤ k ∧ (G.induce (U : Set V)).Connected := by
  classical
  let P := partition G Δ k hk t b n β
  obtain ⟨U, hU, hv⟩ := P.covers v (Finset.mem_univ v)
  have he : P.parts.biUnion (fun W => if v ∈ W then W else ∅) = U := by
    apply Finset.Subset.antisymm
    · intro u hu
      obtain ⟨W, hW, hu⟩ := Finset.mem_biUnion.mp hu
      split_ifs at hu with hvW
      · have hWU : W = U := by
          by_contra hn
          exact Finset.disjoint_left.mp (P.disjoint hW hU hn) hvW hv
        simpa only [hWU] using hu
      · exact False.elim (Finset.notMem_empty _ hu)
    · intro u hu
      exact Finset.mem_biUnion.mpr ⟨U, hU, by simpa only [if_pos hv] using hu⟩
  dsimp only
  rw [output_eq G C Δ k hk t ht b n β hdeg v]
  change P.parts.biUnion _ ∈ P.parts ∧ _
  rw [he]
  exact ⟨hU, hv, P.size U hU, P.connected U hU⟩

theorem rounds {ids : ℕ} (C : BitCode V ids) (Δ k t b n : ℕ) :
    (program C Δ k t b n).rounds = n * (3 * k + 1) := by
  simp only [program, Program.rounds, PriorityPartitionBroadcast.rounds, Nat.zero_add]

theorem logarithmic_bits {ids : ℕ} (C : BitCode V ids) (Δ k t b n N c : ℕ)
    (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (program C Δ k t b n).maxBits ≤
      ((Δ + 1) ^ (n * (3 * k + 1)) *
        (Δ + (n * 2 ^ ((Δ + 1) ^ k)) * 2 ^ b + 3) * (c + 1)) * Nat.clog 2 (N + 2) := by
  simpa only [program, Program.maxBits, Nat.zero_max] using
    PriorityPartitionBroadcast.logarithmic_bits C Δ k t (2 ^ b) n (by positivity)
      (PriorityTableCode.code Δ k (2 ^ b) n) N c hids

/-- The local frame contains topology and bits only in the gathered ball.
The complete neighbor lists at its boundary are available within one extra
radius layer, so radius n*(3*k+1)+1 suffices for the local model. -/
theorem local_output {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (β γ : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) (M : V → Finset V) (F : Finset V) (v : V)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) v (n * (3 * k + 1)) ⊆ F)
    (hs : ∀ u ∈ F, β u = γ u) :
    FinitePartLabels.label M k t F n
        (PartitionFrameLocality.seeds M Δ k v (2 ^ b) n
          (fun i u mask => table Δ k b n (β u) (i, mask))) v =
      (program C Δ k t b n).runEncoded G γ v := by
  rw [output_eq G C Δ k hk t ht b n γ hdeg v]
  have hh := PartitionFrameLocality.local_math_label G M F Finset.univ v v
    Δ k hk t ht (2 ^ b) (by positivity) n
    (fun i u mask => table Δ k b n (β u) (i, mask))
    (fun i u mask => table Δ k b n (γ u) (i, mask)) hm hF
    (fun i u hu => by dsimp only; rw [hs u hu])
  simpa only [Finset.inter_univ, table, partition, sourceEquiv, Equiv.coe_fn_mk] using hh

noncomputable def cut (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ)
    (β : V → Bits Δ k b n) : ℕ := by
  classical
  exact PriorityCut.cut G k hk (1 / (t : ℝ)) Finset.univ n
    (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n
      (sourceEquiv V Δ k b n β))

theorem cut_eq (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (β : V → Bits Δ k b n) :
    cut G Δ k hk t b n β = by
      classical
      exact (PartCut.graph G Finset.univ (partition G Δ k hk t b n β).parts).edgeFinset.card := by
  unfold cut PriorityCut.cut partition
  congr 1

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Align the order-derived equality test in `cut` with the classical test
used by the finite-priority expectation theorem, without reducing the cut. -/
theorem cut_source_eq (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ)
    (β : V → Bits Δ k b n) :
    cut G Δ k hk t b n β =
      PriorityCut.cut G k hk (1 / (t : ℝ)) Finset.univ n
        (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n
          (sourceEquiv V Δ k b n β)) := by
  unfold cut
  have hde : (fun a b : V => LinearOrder.toDecidableEq a b) = Classical.decEq V :=
    Subsingleton.elim _ _
  rw [hde]

/-- Uniform fixed parameters for connected small parts and expected cut.
The expectation is the exact average over all independent Boolean tables. -/
theorem parameters (C₀ : ℝ) (hC : 0 ≤ C₀) (Δ : ℕ) (η : ℚ) (hη : 0 < η) :
    ∃ t k b n : ℕ, ∃ _ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SeparatorBalance.Bound G C₀ (2 / 3) → (∀ v, G.degree v ≤ Δ) →
        (∑ β : V → Bits Δ k b n, (cut G Δ k hk t b n β : ℝ)) ≤
          (η : ℝ) * Fintype.card (V → Bits Δ k b n) * Fintype.card V := by
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη
  obtain ⟨t, k, b, n, ht, hk, hparams⟩ := HumanPartition.parameters C₀ hC Δ (η : ℝ) hηR
  refine ⟨t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hprofile hdeg
  have hh := hparams G hprofile hdeg Finset.univ
  have he := Equiv.sum_comp (sourceEquiv V Δ k b n)
    (fun ω => (PriorityCut.cut G k hk (1 / (t : ℝ)) Finset.univ n
      (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n ω) : ℝ))
  have hc := Fintype.card_congr (sourceEquiv V Δ k b n)
  simp only [cut_source_eq]
  calc
    _ = ∑ ω : (Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b),
        (PriorityCut.cut G k hk (1 / (t : ℝ)) Finset.univ n
          (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n ω) : ℝ) := he
    _ ≤ (η : ℝ) * Fintype.card ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b)) *
        Fintype.card V := by simpa only [Finset.card_univ] using hh
    _ = _ := congrArg (fun m : ℕ => (η : ℝ) * m * Fintype.card V) hc.symm

end Paper.CurrentFiniteBitPartition

#print axioms Paper.CurrentFiniteBitPartition.cut_source_eq
#print axioms Paper.CurrentFiniteBitPartition.parameters
#print axioms Paper.CurrentFiniteBitPartition.cut_eq
#print axioms Paper.CurrentFiniteBitPartition.output_part
#print axioms Paper.CurrentFiniteBitPartition.local_output
#print axioms Paper.CurrentFiniteBitPartition.bits_per_vertex
#print axioms Paper.CurrentFiniteBitPartition.rounds
#print axioms Paper.CurrentFiniteBitPartition.logarithmic_bits
