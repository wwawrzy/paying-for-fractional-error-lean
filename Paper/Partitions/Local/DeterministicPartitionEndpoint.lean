import Paper.Partitions.Local.DeterministicPartitionComputedProgram

/-! The computed sc:det-partition contract, including physical communication.
All natural parameters and cost coefficients precede the graph and its public
identifier representation. Real separator/accuracy parameters select only these
fixed naturals; the executable is the received graph-independent Bool-input
ComputedProgram. No coloring, expected cut or final remaining-set oracle occurs.
This endpoint does not compose the partition with the approximation solver of D. -/
namespace Paper.DeterministicPartitionEndpoint
open BroadcastModel DeterministicColorReductionLogStar DeterministicPartitionComputedProgram

def stageRounds (Δ k : ℕ) : ℕ := candidateColors Δ k * k + 2 * k + 1

def roundCoefficient (Δ k T c p d : ℕ) : ℕ :=
  DeterministicColorReductionPhysicalProgram.roundConstant (2 * k) c p d + T * stageRounds Δ k

def stageBitCoefficient (Δ k c p d : ℕ) : ℕ :=
  (Δ + 1) ^ stageRounds Δ k * (Δ + palette Δ k + 3) *
    (DeterministicColorReductionIdentifiers.bitFactor c p d + 1)

def bitCoefficient (Δ k c p d : ℕ) : ℕ :=
  DeterministicColorReductionPhysicalProgram.messageConstant Δ (2 * k) c p d +
    stageBitCoefficient Δ k c p d

section Costs
variable {V : Type} [Fintype V] [LinearOrder V]

theorem costs {ids : ℕ} (I : BitCode V ids) (Δ k t T c p d M : ℕ)
    (hbits : ids ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program I Δ k t T).rounds ≤ roundCoefficient Δ k T c p d * (1 + logStar (Fintype.card V)) ∧
    (program I Δ k t T).maxBits ≤ bitCoefficient Δ k c p d * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := DeterministicColorReductionPhysicalProgram.parameters I Δ (2 * k) c p d M hbits hM
  have hi := DeterministicColorReductionIdentifiers.public_length_bound
    (Fintype.card V) ids c p d M hbits hM
  constructor
  · rw [DeterministicPartitionComputedProgram.rounds]
    change _ + T * stageRounds Δ k ≤ _
    have hs : T * stageRounds Δ k ≤ T * stageRounds Δ k * (1 + logStar (Fintype.card V)) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (T * stageRounds Δ k)
        (by omega : 1 ≤ 1 + logStar (Fintype.card V))
    calc
      _ ≤ DeterministicColorReductionPhysicalProgram.roundConstant (2 * k) c p d *
          (1 + logStar (Fintype.card V)) + T * stageRounds Δ k * (1 + logStar (Fintype.card V)) :=
        Nat.add_le_add hp.1 hs
      _ = _ := by unfold roundCoefficient; ring
  · have hc : (coloring I Δ k).maxBits ≤
        DeterministicColorReductionPhysicalProgram.messageConstant Δ (2 * k) c p d *
          Nat.clog 2 (Fintype.card V + 2) := by
      rw [coloring_maxBits]
      exact hp.2.1
    have ht : (iteration I Δ k t T).maxBits ≤
        stageBitCoefficient Δ k c p d * Nat.clog 2 (Fintype.card V + 2) :=
      DeterministicPartitionIterationProgram.logarithmic_bits I Δ k t (palette Δ k)
        (candidateColors Δ k) T (palette_pos Δ k) (Fintype.card V)
        (DeterministicColorReductionIdentifiers.bitFactor c p d) hi
    have hcoef1 : DeterministicColorReductionPhysicalProgram.messageConstant Δ (2 * k) c p d ≤
        bitCoefficient Δ k c p d := by unfold bitCoefficient; omega
    have hcoef2 : stageBitCoefficient Δ k c p d ≤ bitCoefficient Δ k c p d := by
      unfold bitCoefficient
      omega
    have hm : max (coloring I Δ k).maxBits (iteration I Δ k t T).maxBits ≤
        bitCoefficient Δ k c p d * Nat.clog 2 (Fintype.card V + 2) :=
      max_le (hc.trans (Nat.mul_le_mul_right _ hcoef1)) (ht.trans (Nat.mul_le_mul_right _ hcoef2))
    simpa only [program, holdActive, attachColor, Program.maxBits, ProgramMemory.maxBits,
      Nat.zero_max] using hm

end Costs

/-- Proof-only crossing-graph test, matching the received exact PartCut theorem.
It is not an input or dependency of the executable program or its encoding. -/
private noncomputable local instance partCutDecidable {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (P : Finset (Finset V)) :
    DecidableRel (PartCut.graph G S P).Adj := fun _ _ => Classical.propDecidable _

/-- Every field refers to the same computed partition and actual encoded program. -/
structure ActiveContract {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ids : ℕ} (I : BitCode V ids)
    (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ v, G.degree v ≤ Δ)
    (η : ℝ) (Kround Kbits : ℕ) (S : Finset V) : Prop where
  disjoint : ((partition G I Δ hdeg k hk t ht S T).parts : Set (Finset V)).Pairwise Disjoint
  covers : ∀ v ∈ S, ∃ U ∈ (partition G I Δ hdeg k hk t ht S T).parts, v ∈ U
  parts_valid : ∀ U ∈ (partition G I Δ hdeg k hk t ht S T).parts,
    U.Nonempty ∧ U ⊆ S ∧ U.card ≤ k ∧ (G.induce (U : Set V)).Connected
  cut : ((PartCut.graph G S (partition G I Δ hdeg k hk t ht S T).parts).edgeFinset.card : ℝ) ≤ η * S.card
  exact_output : ∀ v, (program I Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v =
    (partition G I Δ hdeg k hk t ht S T).parts.biUnion (fun U => if v ∈ U then U else ∅)
  local_output : ∀ v ∈ S,
    let U := (program I Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v
    U ∈ (partition G I Δ hdeg k hk t ht S T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (G.induce (U : Set V)).Connected
  rounds : (program I Δ k t T).rounds ≤ Kround * (1 + logStar (Fintype.card V))
  bits : (program I Δ k t T).maxBits ≤ Kbits * Nat.clog 2 (Fintype.card V + 2)
  small : Fintype.card V ≤ 1 → (program I Δ k t T).rounds ≤ Kround ∧
    (program I Δ k t T).maxBits ≤ Kbits * 2
  empty : Fintype.card V = 0 → (partition G I Δ hdeg k hk t ht S T).parts = ∅

section Contracts
variable {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem active_contract {ids : ℕ} (I : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (η : ℝ) (c p d M : ℕ) (S : Finset V)
    (hbits : ids ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d)
    (hcut : ((PartCut.graph G S (partition G I Δ hdeg k hk t ht S T).parts).edgeFinset.card : ℝ) ≤ η * S.card) :
    ActiveContract G I Δ k t T hk ht hdeg η (roundCoefficient Δ k T c p d) (bitCoefficient Δ k c p d) S := by
  let P := partition G I Δ hdeg k hk t ht S T
  have hcost := costs I Δ k t T c p d M hbits hM
  refine {
    disjoint := P.disjoint
    covers := P.covers
    parts_valid := ?_
    cut := hcut
    exact_output := ?_
    local_output := ?_
    rounds := hcost.1
    bits := hcost.2
    small := ?_
    empty := ?_ }
  · intro U hU
    exact ⟨P.nonempty U hU, P.subset U hU, P.size U hU, P.connected U hU⟩
  · intro v
    rw [partition_parts G I Δ hdeg k hk t ht S T]
    exact DeterministicPartitionComputedProgram.correct G I Δ k t T S hdeg v
  · intro v hv
    exact DeterministicPartitionComputedProgram.output_part G I Δ k t T hk ht S hdeg v hv
  · intro hn
    have hl : Nat.clog 2 (Fintype.card V + 2) ≤ 2 := Nat.clog_le_of_le_pow (by norm_num; omega)
    constructor
    · simpa only [logStar_small (Fintype.card V) hn, Nat.add_zero, Nat.mul_one] using hcost.1
    · exact hcost.2.trans (Nat.mul_le_mul_left _ hl)
  · intro hn
    letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro U hU
    obtain ⟨v, _⟩ := P.nonempty U hU
    exact isEmptyElim v

end Contracts

/-- The all-vertices specialization has literal true local inputs. -/
structure WholeContract {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ids : ℕ} (I : BitCode V ids)
    (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ v, G.degree v ≤ Δ)
    (η : ℝ) (Kround Kbits : ℕ) : Prop where
  active : ActiveContract G I Δ k t T hk ht hdeg η Kround Kbits Finset.univ
  cut_count : ((PartCut.graph G Finset.univ
    (partition G I Δ hdeg k hk t ht Finset.univ T).parts).edgeFinset.card : ℝ) ≤ η * Fintype.card V
  exact_output : ∀ v, (program I Δ k t T).runEncoded G (fun _ => true) v =
    (partition G I Δ hdeg k hk t ht Finset.univ T).parts.biUnion (fun U => if v ∈ U then U else ∅)
  local_output : ∀ v,
    let U := (program I Δ k t T).runEncoded G (fun _ => true) v
    U ∈ (partition G I Δ hdeg k hk t ht Finset.univ T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (G.induce (U : Set V)).Connected

theorem whole_contract {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ids : ℕ} (I : BitCode V ids)
    (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ v, G.degree v ≤ Δ)
    (η : ℝ) (Kround Kbits : ℕ) (h : ActiveContract G I Δ k t T hk ht hdeg η Kround Kbits Finset.univ) :
    WholeContract G I Δ k t T hk ht hdeg η Kround Kbits := by
  have hin : (fun u : V => decide (u ∈ (Finset.univ : Finset V))) = fun _ => true := by
    funext u
    simp
  refine ⟨h, ?_, ?_, ?_⟩
  · simpa only [Finset.card_univ] using h.cut
  · intro v
    have he := congrArg (fun s : V → Bool => (program I Δ k t T).runEncoded G s v) hin
    exact he.symm.trans (h.exact_output v)
  · intro v
    have he := congrArg (fun s : V → Bool => (program I Δ k t T).runEncoded G s v) hin
    exact (congrArg (fun U : Finset V =>
      U ∈ (partition G I Δ hdeg k hk t ht Finset.univ T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
        (G.induce (U : Set V)).Connected) he).mp (h.local_output v (Finset.mem_univ v))

/-- Fixed public parameters precede every graph, identifier code and capacity. -/
theorem uniform_active_partition (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) (c p d : ℕ) :
    ∃ t k T Kround Kbits : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SeparatorBalance.Bound G C (2 / 3) → (hdeg : ∀ v, G.degree v ≤ Δ) →
        ∀ {ids : ℕ} (I : BitCode V ids) (M : ℕ),
          ids ≤ c * Nat.clog 2 M → M ≤ p * (Fintype.card V + 2) ^ d →
          ∀ S : Finset V, ActiveContract G I Δ k t T hk ht hdeg η Kround Kbits S := by
  obtain ⟨t, k, T, ht, hk, hcut⟩ := DeterministicPartitionComputedProgram.uniform_cut C hC Δ η hη
  refine ⟨t, k, T, roundCoefficient Δ k T c p d, bitCoefficient Δ k c p d, ht, hk, ?_⟩
  intro V _ _ G _ hprofile hdeg ids I M hbits hM S
  exact active_contract G I Δ k t T hk ht hdeg η c p d M S hbits hM
    (hcut G hprofile hdeg I S)

/-- sc:det-partition with actual computed colors, physical broadcasts and complete-part output. -/
theorem sc_det_partition (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) (c p d : ℕ) :
    ∃ t k T Kround Kbits : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SeparatorBalance.Bound G C (2 / 3) → (hdeg : ∀ v, G.degree v ≤ Δ) →
        ∀ {ids : ℕ} (I : BitCode V ids) (M : ℕ),
          ids ≤ c * Nat.clog 2 M → M ≤ p * (Fintype.card V + 2) ^ d →
          WholeContract G I Δ k t T hk ht hdeg η Kround Kbits := by
  obtain ⟨t, k, T, Kround, Kbits, ht, hk, h⟩ := uniform_active_partition C hC Δ η hη c p d
  refine ⟨t, k, T, Kround, Kbits, ht, hk, ?_⟩
  intro V _ _ G _ hprofile hdeg ids I M hbits hM
  exact whole_contract G I Δ k t T hk ht hdeg η Kround Kbits
    (h G hprofile hdeg I M hbits hM Finset.univ)

/-- A concrete numerical representation realizes the public encoding factor c=2. -/
theorem sc_det_partition_numeric (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) (p d : ℕ) :
    ∃ t k T Kround Kbits : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SeparatorBalance.Bound G C (2 / 3) → (hdeg : ∀ v, G.degree v ≤ Δ) →
        ∀ (M : ℕ) (D : DeterministicColorReductionIdentifiers.IdentifierRep V M),
          M ≤ p * (Fintype.card V + 2) ^ d →
          WholeContract G (DeterministicColorReductionIdentifiers.identifierCode D)
            Δ k t T hk ht hdeg η Kround Kbits := by
  obtain ⟨t, k, T, Kround, Kbits, ht, hk, h⟩ := sc_det_partition C hC Δ η hη 2 p d
  refine ⟨t, k, T, Kround, Kbits, ht, hk, ?_⟩
  intro V _ _ G _ hprofile hdeg M D hM
  exact h G hprofile hdeg (DeterministicColorReductionIdentifiers.identifierCode D) M le_rfl hM

end Paper.DeterministicPartitionEndpoint

#print axioms Paper.DeterministicPartitionEndpoint.costs
#print axioms Paper.DeterministicPartitionEndpoint.active_contract
#print axioms Paper.DeterministicPartitionEndpoint.whole_contract
#print axioms Paper.DeterministicPartitionEndpoint.uniform_active_partition
#print axioms Paper.DeterministicPartitionEndpoint.sc_det_partition
#print axioms Paper.DeterministicPartitionEndpoint.sc_det_partition_numeric
