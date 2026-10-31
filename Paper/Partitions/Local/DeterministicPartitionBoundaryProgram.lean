import Paper.Partitions.Local.DeterministicPartitionEndpoint
import Paper.Communication.PartBoundaryBroadcast

/-! Actual computed partition followed by its one-round boundary test.
The full part label is private memory through PartBoundaryBroadcast, and the
output is (full part, exact boundary flag). No partition/boundary oracle is
an executable input. This is partition-local execution, not owner routing or D. -/
namespace Paper.DeterministicPartitionBoundaryProgram
open BroadcastModel DeterministicColorReductionLogStar DeterministicPartitionComputedProgram
variable {V : Type} [LinearOrder V]

def duplicate : Program V (Finset V) (Finset V × Finset V) := .local fun _ _ s => (s, s)

def restore : Program V (Bool × Finset V) (Finset V × Bool) := .local fun _ _ s => (s.2, s.1)

def boundary {ids : ℕ} (I : BitCode V ids) (k : ℕ) : Program V (Finset V) (Finset V × Bool) :=
  .seq duplicate (.seq (ProgramMemory.carry (X := Finset V) (PartBoundaryBroadcast.program I k)) restore)

def program {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) : Program V Bool (Finset V × Bool) :=
  .seq (DeterministicPartitionComputedProgram.program I Δ k t T) (boundary I k)

theorem boundary_rounds {ids : ℕ} (I : BitCode V ids) (k : ℕ) : (boundary I k).rounds = 1 := by
  simp only [boundary, duplicate, restore, Program.rounds, ProgramMemory.rounds,
    PartBoundaryBroadcast.program, Program.rounds, Nat.zero_add, Nat.add_zero]

theorem boundary_bits {ids : ℕ} (I : BitCode V ids) (k : ℕ) :
    (boundary I k).maxBits = k * (ids + 1) := by
  simp only [boundary, duplicate, restore, Program.maxBits, ProgramMemory.maxBits,
    PartBoundaryBroadcast.program, Program.maxBits, Nat.zero_max, Nat.max_zero]

theorem rounds {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) :
    (program I Δ k t T).rounds = (DeterministicPartitionComputedProgram.program I Δ k t T).rounds + 1 := by
  simp only [program, Program.rounds, boundary_rounds]

theorem maxBits {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) :
    (program I Δ k t T).maxBits =
      max (DeterministicPartitionComputedProgram.program I Δ k t T).maxBits (k * (ids + 1)) := by
  simp only [program, Program.maxBits, boundary_bits]

def roundCoefficient (Δ k T c p d : ℕ) : ℕ :=
  DeterministicPartitionEndpoint.roundCoefficient Δ k T c p d + 1

def boundaryBitCoefficient (k c p d : ℕ) : ℕ :=
  k * (DeterministicColorReductionIdentifiers.bitFactor c p d + 1)

def bitCoefficient (Δ k c p d : ℕ) : ℕ :=
  DeterministicPartitionEndpoint.bitCoefficient Δ k c p d + boundaryBitCoefficient k c p d

section Costs
variable [Fintype V]

theorem costs {ids : ℕ} (I : BitCode V ids) (Δ k t T c p d M : ℕ)
    (hbits : ids ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program I Δ k t T).rounds ≤ roundCoefficient Δ k T c p d * (1 + logStar (Fintype.card V)) ∧
    (program I Δ k t T).maxBits ≤ bitCoefficient Δ k c p d * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := DeterministicPartitionEndpoint.costs I Δ k t T c p d M hbits hM
  have hi := DeterministicColorReductionIdentifiers.public_length_bound
    (Fintype.card V) ids c p d M hbits hM
  have hb : k * (ids + 1) ≤ boundaryBitCoefficient k c p d * Nat.clog 2 (Fintype.card V + 2) :=
    ListPacket.logarithmic_width k ids (DeterministicColorReductionIdentifiers.bitFactor c p d)
      (Fintype.card V) hi
  constructor
  · rw [rounds]
    calc
      _ ≤ DeterministicPartitionEndpoint.roundCoefficient Δ k T c p d *
          (1 + logStar (Fintype.card V)) + (1 + logStar (Fintype.card V)) :=
        Nat.add_le_add hp.1 (by omega)
      _ = _ := by unfold roundCoefficient; ring
  · have hc1 : DeterministicPartitionEndpoint.bitCoefficient Δ k c p d ≤ bitCoefficient Δ k c p d := by
      unfold bitCoefficient
      omega
    have hc2 : boundaryBitCoefficient k c p d ≤ bitCoefficient Δ k c p d := by
      unfold bitCoefficient
      omega
    rw [maxBits]
    exact max_le (hp.2.trans (Nat.mul_le_mul_right _ hc1)) (hb.trans (Nat.mul_le_mul_right _ hc2))

end Costs

/-- Proof-only adjacency for exact crossing-edge counts, matching the received APIs. -/
private noncomputable local instance partCutDecidable {W : Type} [Fintype W] [LinearOrder W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) (P : Finset (Finset W)) :
    DecidableRel (PartCut.graph H S P).Adj := fun _ _ => Classical.propDecidable _

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem boundary_run {ids : ℕ} (I : BitCode V ids) (k : ℕ) (s : V → Finset V) (v : V) :
    (boundary I k).run G s v = (s v, (PartBoundaryBroadcast.program I k).run G s v) := rfl

theorem preserves_part {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (s : V → Bool) (v : V) :
    ((program I Δ k t T).runEncoded G s v).1 =
      (DeterministicPartitionComputedProgram.program I Δ k t T).runEncoded G s v := rfl

theorem labels_correct {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) :
    (DeterministicPartitionComputedProgram.program I Δ k t T).runEncoded G (fun u => decide (u ∈ S)) =
      DisjointPartLabels.label (partition G I Δ hdeg k hk t ht S T).parts := by
  funext v
  have hf := partition_parts G I Δ hdeg k hk t ht S T
  exact (DeterministicPartitionComputedProgram.correct G I Δ k t T S hdeg v).trans
    (congrArg (fun F : Finset (Finset V) => DisjointPartLabels.label F v) hf.symm)

/-- Both fields of the actual encoded output refer to the same computed family. -/
theorem correct {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) (v : V) :
    (program I Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v =
      (DisjointPartLabels.label (partition G I Δ hdeg k hk t ht S T).parts v,
        decide (v ∈ BoundaryOwners.vertices G S (partition G I Δ hdeg k hk t ht S T).parts)) := by
  have he : (DeterministicPartitionComputedProgram.program I Δ k t T).run G
        (fun u => decide (u ∈ S)) = DisjointPartLabels.label (partition G I Δ hdeg k hk t ht S T).parts :=
    (Program.runEncoded_eq_run G (DeterministicPartitionComputedProgram.program I Δ k t T)
      (fun u => decide (u ∈ S))).symm.trans (labels_correct G I Δ k t T hk ht hdeg S)
  rw [Program.runEncoded_eq_run]
  change (boundary I k).run G ((DeterministicPartitionComputedProgram.program I Δ k t T).run G
    (fun u => decide (u ∈ S))) v = _
  rw [boundary_run, he]
  exact congrArg (fun b : Bool => (DisjointPartLabels.label (partition G I Δ hdeg k hk t ht S T).parts v, b))
    (PartBoundaryBroadcast.correct G I S k (partition G I Δ hdeg k hk t ht S T) v)

theorem output_part {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) (v : V) (hv : v ∈ S) :
    let U := ((program I Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v).1
    U ∈ (partition G I Δ hdeg k hk t ht S T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (G.induce (U : Set V)).Connected := by
  have he := preserves_part G I Δ k t T (fun u => decide (u ∈ S)) v
  exact (congrArg (fun U : Finset V =>
    U ∈ (partition G I Δ hdeg k hk t ht S T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (G.induce (U : Set V)).Connected) he).mpr
    (DeterministicPartitionComputedProgram.output_part G I Δ k t T hk ht S hdeg v hv)

def flagged {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ((program I Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v).2 = true)

def flaggedAll {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) : Finset V :=
  Finset.univ.filter (fun v => ((program I Δ k t T).runEncoded G (fun _ => true) v).2 = true)

theorem flagged_all_eq {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) :
    flaggedAll G I Δ k t T = flagged G I Δ k t T Finset.univ := by
  have hin : (fun u : V => decide (u ∈ (Finset.univ : Finset V))) = fun _ => true := by
    funext u
    simp
  unfold flaggedAll flagged
  rw [hin]

theorem flagged_eq {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) :
    flagged G I Δ k t T S = BoundaryOwners.vertices G S (partition G I Δ hdeg k hk t ht S T).parts := by
  ext v
  simp only [flagged, Finset.mem_filter, Finset.mem_univ, true_and,
    correct G I Δ k t T hk ht hdeg S v, decide_eq_true_eq]

theorem flagged_subset {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) : flagged G I Δ k t T S ⊆ S := by
  rw [flagged_eq G I Δ k t T hk ht hdeg S]
  exact BoundaryOwners.subset G S _

theorem boundary_count {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) :
    (flagged G I Δ k t T S).card ≤
      2 * (PartCut.graph G S (partition G I Δ hdeg k hk t ht S T).parts).edgeFinset.card := by
  rw [flagged_eq G I Δ k t T hk ht hdeg S]
  exact BoundaryOwners.count G S _

theorem boundary_eta {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) (η : ℝ) (Kr Kb : ℕ)
    (h : DeterministicPartitionEndpoint.ActiveContract G I Δ k t T hk ht hdeg η Kr Kb S) :
    ((flagged G I Δ k t T S).card : ℝ) ≤ 2 * η * S.card := by
  have hn := boundary_count G I Δ k t T hk ht hdeg S
  have hr : ((flagged G I Δ k t T S).card : ℝ) ≤
      2 * ((PartCut.graph G S (partition G I Δ hdeg k hk t ht S T).parts).edgeFinset.card : ℝ) := by
    exact_mod_cast hn
  have hc := mul_le_mul_of_nonneg_left h.cut (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem correct_all {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (program I Δ k t T).runEncoded G (fun _ => true) v =
      (DisjointPartLabels.label (partition G I Δ hdeg k hk t ht Finset.univ T).parts v,
        decide (v ∈ BoundaryOwners.vertices G Finset.univ
          (partition G I Δ hdeg k hk t ht Finset.univ T).parts)) := by
  have hin : (fun u : V => decide (u ∈ (Finset.univ : Finset V))) = fun _ => true := by
    funext u
    simp
  have he := congrArg (fun s : V → Bool => (program I Δ k t T).runEncoded G s v) hin
  exact he.symm.trans (correct G I Δ k t T hk ht hdeg Finset.univ v)

theorem boundary_eta_all {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (η : ℝ) (Kr Kb : ℕ)
    (h : DeterministicPartitionEndpoint.WholeContract G I Δ k t T hk ht hdeg η Kr Kb) :
    ((flaggedAll G I Δ k t T).card : ℝ) ≤ 2 * η * Fintype.card V := by
  rw [flagged_all_eq]
  simpa only [Finset.card_univ] using boundary_eta G I Δ k t T hk ht hdeg Finset.univ η Kr Kb h.active

theorem inactive {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) (v : V) (hv : v ∉ S) :
    (program I Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v = (∅, false) := by
  have hl := DisjointPartLabels.outside G S k (partition G I Δ hdeg k hk t ht S T) v hv
  have hb : v ∉ BoundaryOwners.vertices G S (partition G I Δ hdeg k hk t ht S T).parts :=
    fun h => hv (BoundaryOwners.subset G S _ h)
  simpa only [hl, show decide (v ∈ BoundaryOwners.vertices G S
    (partition G I Δ hdeg k hk t ht S T).parts) = false by simp [hb]] using
    correct G I Δ k t T hk ht hdeg S v

theorem flagged_empty_active {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) : flagged G I Δ k t T ∅ = ∅ := by
  have hs := flagged_subset G I Δ k t T hk ht hdeg ∅
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (hs hv))

theorem flagged_empty_graph [IsEmpty V] {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (S : Finset V) :
    flagged G I Δ k t T S = ∅ := by
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun v => isEmptyElim v)

end Graph

structure Contract {W : Type} [Fintype W] [LinearOrder W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {ids : ℕ} (I : BitCode W ids)
    (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ v, H.degree v ≤ Δ)
    (η : ℝ) (Kr Kb : ℕ) (S : Finset W) : Prop where
  output : ∀ v, (program I Δ k t T).runEncoded H (fun u => decide (u ∈ S)) v =
    (DisjointPartLabels.label (partition H I Δ hdeg k hk t ht S T).parts v,
      decide (v ∈ BoundaryOwners.vertices H S (partition H I Δ hdeg k hk t ht S T).parts))
  part : ∀ v ∈ S,
    let U := ((program I Δ k t T).runEncoded H (fun u => decide (u ∈ S)) v).1
    U ∈ (partition H I Δ hdeg k hk t ht S T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (H.induce (U : Set W)).Connected
  count : (flagged H I Δ k t T S).card ≤
    2 * (PartCut.graph H S (partition H I Δ hdeg k hk t ht S T).parts).edgeFinset.card
  eta : ((flagged H I Δ k t T S).card : ℝ) ≤ 2 * η * S.card
  subset : flagged H I Δ k t T S ⊆ S
  rounds : (program I Δ k t T).rounds ≤ Kr * (1 + logStar (Fintype.card W))
  bits : (program I Δ k t T).maxBits ≤ Kb * Nat.clog 2 (Fintype.card W + 2)
  small : Fintype.card W ≤ 1 → (program I Δ k t T).rounds ≤ Kr ∧ (program I Δ k t T).maxBits ≤ Kb * 2
  empty : Fintype.card W = 0 → flagged H I Δ k t T S = ∅

/-- Public natural boundary coefficients are selected before graph/order/ID data. -/
theorem uniform_parameters (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) (c p d : ℕ) :
    ∃ t k T Kr Kb : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {W : Type} [Fintype W] [LinearOrder W] (H : SimpleGraph W) [DecidableRel H.Adj],
        SeparatorBalance.Bound H C (2 / 3) → (hdeg : ∀ v, H.degree v ≤ Δ) →
        ∀ {ids : ℕ} (I : BitCode W ids) (M : ℕ),
          ids ≤ c * Nat.clog 2 M → M ≤ p * (Fintype.card W + 2) ^ d →
          ∀ S : Finset W, Contract H I Δ k t T hk ht hdeg η Kr Kb S := by
  obtain ⟨t, k, T, oldKr, oldKb, ht, hk, h⟩ :=
    DeterministicPartitionEndpoint.uniform_active_partition C hC Δ η hη c p d
  refine ⟨t, k, T, roundCoefficient Δ k T c p d, bitCoefficient Δ k c p d, ht, hk, ?_⟩
  intro W _ _ H _ hprofile hdeg ids I M hbits hM S
  have hp := h H hprofile hdeg I M hbits hM S
  have hcost := costs I Δ k t T c p d M hbits hM
  refine {
    output := correct H I Δ k t T hk ht hdeg S
    part := output_part H I Δ k t T hk ht hdeg S
    count := boundary_count H I Δ k t T hk ht hdeg S
    eta := boundary_eta H I Δ k t T hk ht hdeg S η oldKr oldKb hp
    subset := flagged_subset H I Δ k t T hk ht hdeg S
    rounds := hcost.1
    bits := hcost.2
    small := ?_
    empty := ?_ }
  · intro hn
    have hl : Nat.clog 2 (Fintype.card W + 2) ≤ 2 := Nat.clog_le_of_le_pow (by norm_num; omega)
    constructor
    · simpa only [logStar_small (Fintype.card W) hn, Nat.add_zero, Nat.mul_one] using hcost.1
    · exact hcost.2.trans (Nat.mul_le_mul_left _ hl)
  · intro hn
    letI : IsEmpty W := Fintype.card_eq_zero_iff.mp hn
    exact flagged_empty_graph H I Δ k t T S

end Paper.DeterministicPartitionBoundaryProgram

#print axioms Paper.DeterministicPartitionBoundaryProgram.correct
#print axioms Paper.DeterministicPartitionBoundaryProgram.preserves_part
#print axioms Paper.DeterministicPartitionBoundaryProgram.correct_all
#print axioms Paper.DeterministicPartitionBoundaryProgram.boundary_count
#print axioms Paper.DeterministicPartitionBoundaryProgram.boundary_eta
#print axioms Paper.DeterministicPartitionBoundaryProgram.boundary_eta_all
#print axioms Paper.DeterministicPartitionBoundaryProgram.rounds
#print axioms Paper.DeterministicPartitionBoundaryProgram.maxBits
#print axioms Paper.DeterministicPartitionBoundaryProgram.costs
#print axioms Paper.DeterministicPartitionBoundaryProgram.uniform_parameters
