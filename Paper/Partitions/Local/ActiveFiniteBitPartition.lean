import Paper.Partitions.Local.CurrentFiniteBitPartition
import Paper.Communication.PartBoundaryBroadcast
import Paper.Communication.ProgramMemory

/-! Active finite-bit partition and one real boundary broadcast. Runtime input
is the local active Bool and independent fixed-size Boolean table only.
All averages concern the SAME actual partition on S, with scale |S|. -/
namespace Paper.ActiveFiniteBitPartition
open BroadcastModel
open scoped BigOperators

abbrev Bits := CurrentFiniteBitPartition.Bits
abbrev Input (Δ k b n : ℕ) := Bool × Bits Δ k b n

variable {V : Type} [LinearOrder V]

def partsProgram {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) :
    Program V (Input Δ k b n) (Finset V) :=
  .seq (.local (fun _ _ s => (s.1, CurrentFiniteBitPartition.table Δ k b n s.2)))
    (PriorityPartitionBroadcast.program I Δ k t (2 ^ b) n (by positivity)
      (PriorityTableCode.code Δ k (2 ^ b) n))

def duplicate : Program V (Finset V) (Finset V × Finset V) := .local (fun _ _ s => (s, s))
def restore : Program V (Bool × Finset V) (Finset V × Bool) := .local (fun _ _ s => (s.2, s.1))

def boundaryProgram {ids : ℕ} (I : BitCode V ids) (k : ℕ) : Program V (Finset V) (Finset V × Bool) :=
  .seq duplicate (.seq (ProgramMemory.carry (X := Finset V) (PartBoundaryBroadcast.program I k)) restore)

def program {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) :
    Program V (Input Δ k b n) (Finset V × Bool) :=
  .seq (partsProgram I Δ k t b n) (boundaryProgram I k)

variable [Fintype V]

theorem bits_per_vertex (Δ k b n : ℕ) :
    Fintype.card (CurrentFiniteBitPartition.Index Δ k n × Fin b) = n * 2 ^ ((Δ + 1) ^ k) * b :=
  CurrentFiniteBitPartition.bits_per_vertex Δ k b n

theorem parts_rounds {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) :
    (partsProgram I Δ k t b n).rounds = n * (3 * k + 1) := by
  simp only [partsProgram, Program.rounds, PriorityPartitionBroadcast.rounds, Nat.zero_add]

theorem boundary_rounds {ids : ℕ} (I : BitCode V ids) (k : ℕ) : (boundaryProgram I k).rounds = 1 := by
  simp only [boundaryProgram, duplicate, restore, Program.rounds, ProgramMemory.rounds,
    PartBoundaryBroadcast.rounds, Nat.zero_add, Nat.add_zero]

theorem boundary_bits {ids : ℕ} (I : BitCode V ids) (k : ℕ) :
    (boundaryProgram I k).maxBits = k * (ids + 1) := by
  simp only [boundaryProgram, duplicate, restore, Program.maxBits, ProgramMemory.maxBits,
    PartBoundaryBroadcast.maxBits, Nat.zero_max, Nat.max_zero]

theorem rounds {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) :
    (program I Δ k t b n).rounds = n * (3 * k + 1) + 1 := by
  simp only [program, Program.rounds, parts_rounds, boundary_rounds]

def tableWidth (Δ k b n : ℕ) : ℕ := (n * 2 ^ ((Δ + 1) ^ k)) * 2 ^ b

def packetBound (ids Δ k b n : ℕ) : ℕ :=
  (Δ + 1) ^ (n * (3 * k + 1)) * (ids + (Δ * (ids + 1) + (1 + tableWidth Δ k b n)) + 1)

def bitCoefficient (Δ k b n c : ℕ) : ℕ :=
  max ((Δ + 1) ^ (n * (3 * k + 1)) * (Δ + tableWidth Δ k b n + 3) * (c + 1)) (k * (c + 1))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def partition (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (S : Finset V)
    (β : V → Bits Δ k b n) : SmallParts.Data G S k :=
  PriorityPartition.partition G k hk (1 / (t : ℝ)) S n
    (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n
      (CurrentFiniteBitPartition.sourceEquiv V Δ k b n β))

theorem parts_correct {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) :
    (partsProgram I Δ k t b n).runEncoded G (fun u => (decide (u ∈ S), β u)) =
      DisjointPartLabels.label (partition G Δ k hk t b n S β).parts := by
  funext v
  rw [Program.runEncoded_eq_run]
  have hh := PriorityPartitionBroadcast.correct G I Δ k hk t ht (2 ^ b) n
    (by positivity) (PriorityTableCode.code Δ k (2 ^ b) n) S
    (fun u => CurrentFiniteBitPartition.table Δ k b n (β u)) hdeg v
  simpa only [partsProgram, Program.run, CurrentFiniteBitPartition.table, partition,
    CurrentFiniteBitPartition.sourceEquiv, Equiv.coe_fn_mk, DisjointPartLabels.label] using hh

theorem boundary_run {ids : ℕ} (I : BitCode V ids) (k : ℕ) (s : V → Finset V) (v : V) :
    (boundaryProgram I k).run G s v = (s v, (PartBoundaryBroadcast.program I k).run G s v) := rfl

/-- Both fields of the actual encoded output refer to the same partition on S. -/
theorem correct {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (program I Δ k t b n).runEncoded G (fun u => (decide (u ∈ S), β u)) v =
      (DisjointPartLabels.label (partition G Δ k hk t b n S β).parts v,
        decide (v ∈ BoundaryOwners.vertices G S (partition G Δ k hk t b n S β).parts)) := by
  have he : (partsProgram I Δ k t b n).run G (fun u => (decide (u ∈ S), β u)) =
      DisjointPartLabels.label (partition G Δ k hk t b n S β).parts :=
    (Program.runEncoded_eq_run G (partsProgram I Δ k t b n) (fun u => (decide (u ∈ S), β u))).symm.trans
      (parts_correct G I Δ k hk t ht b n S β hdeg)
  rw [Program.runEncoded_eq_run]
  change (boundaryProgram I k).run G ((partsProgram I Δ k t b n).run G (fun u => (decide (u ∈ S), β u))) v = _
  rw [boundary_run, he]
  exact congrArg (fun flag : Bool => (DisjointPartLabels.label (partition G Δ k hk t b n S β).parts v, flag))
    (PartBoundaryBroadcast.correct G I S k (partition G Δ k hk t b n S β) v)

theorem output_part {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) (hv : v ∈ S) :
    let U := ((program I Δ k t b n).runEncoded G (fun u => (decide (u ∈ S), β u)) v).1
    U ∈ (partition G Δ k hk t b n S β).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (G.induce (U : Set V)).Connected := by
  rw [correct G I Δ k hk t ht b n S β hdeg v]
  obtain ⟨U, hU, hvU, he⟩ := DisjointPartLabels.exists_part G S k (partition G Δ k hk t b n S β) v hv
  dsimp only
  rw [he]
  exact ⟨hU, hvU, (partition G Δ k hk t b n S β).size U hU,
    (partition G Δ k hk t b n S β).connected U hU⟩

theorem inactive {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) (hv : v ∉ S) :
    (program I Δ k t b n).runEncoded G (fun u => (decide (u ∈ S), β u)) v = (∅, false) := by
  rw [correct G I Δ k hk t ht b n S β hdeg v, DisjointPartLabels.outside G S k (partition G Δ k hk t b n S β) v hv]
  have hn : v ∉ BoundaryOwners.vertices G S (partition G Δ k hk t b n S β).parts :=
    fun h => hv (BoundaryOwners.subset G S _ h)
  simp only [hn, decide_false]

theorem partition_empty (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (β : V → Bits Δ k b n) :
    (partition G Δ k hk t b n ∅ β).parts = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro U hU
  obtain ⟨v, hv⟩ := (partition G Δ k hk t b n ∅ β).nonempty U hU
  exact Finset.notMem_empty v ((partition G Δ k hk t b n ∅ β).subset U hU hv)

theorem empty_active {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (β : V → Bits Δ k b n) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (program I Δ k t b n).runEncoded G (fun u => (false, β u)) v = (∅, false) :=
  inactive G I Δ k hk t ht b n ∅ β hdeg v (Finset.notMem_empty v)

theorem empty_physical [IsEmpty V] {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (s : V → Input Δ k b n) :
    (program I Δ k t b n).runEncoded G s = fun _ => (∅, false) := by
  funext v
  exact isEmptyElim v

def flagged {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n) : Finset V :=
  Finset.univ.filter (fun v => ((program I Δ k t b n).runEncoded G (fun u => (decide (u ∈ S), β u)) v).2 = true)

theorem flagged_eq {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) :
    flagged G I Δ k t b n S β = BoundaryOwners.vertices G S (partition G Δ k hk t b n S β).parts := by
  ext v
  simp only [flagged, Finset.mem_filter, Finset.mem_univ, true_and,
    correct G I Δ k hk t ht b n S β hdeg v, decide_eq_true_eq]

noncomputable def cut (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n) : ℕ := by
  classical
  exact PriorityCut.cut G k hk (1 / (t : ℝ)) S n
    (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n
      (CurrentFiniteBitPartition.sourceEquiv V Δ k b n β))

theorem cut_eq (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n) :
    cut G Δ k hk t b n S β = by
      classical
      exact (PartCut.graph G S (partition G Δ k hk t b n S β).parts).edgeFinset.card := by
  unfold cut PriorityCut.cut partition
  congr 1

theorem boundary_count {ids : ℕ} (I : BitCode V ids) (Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n)
    (hdeg : ∀ v, G.degree v ≤ Δ) : (flagged G I Δ k t b n S β).card ≤ 2 * cut G Δ k hk t b n S β := by
  rw [flagged_eq G I Δ k hk t ht b n S β hdeg, cut_eq G Δ k hk t b n S β]
  exact BoundaryOwners.count G S (partition G Δ k hk t b n S β).parts

theorem maxBits {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) :
    (program I Δ k t b n).maxBits ≤ max (packetBound ids Δ k b n) (k * (ids + 1)) := by
  have hp := PriorityPartitionBroadcast.maxBits I Δ k t (2 ^ b) n (by positivity)
    (PriorityTableCode.code Δ k (2 ^ b) n)
  simpa only [program, partsProgram, Program.maxBits, Nat.zero_max, boundary_bits,
    packetBound, tableWidth] using max_le_max hp (le_refl (k * (ids + 1)))

theorem logarithmic_bits {ids : ℕ} (I : BitCode V ids) (Δ k t b n N c : ℕ)
    (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (program I Δ k t b n).maxBits ≤ bitCoefficient Δ k b n c * Nat.clog 2 (N + 2) := by
  have hp := PriorityPartitionBroadcast.logarithmic_bits I Δ k t (2 ^ b) n (by positivity)
    (PriorityTableCode.code Δ k (2 ^ b) n) N c hids
  have hb := ListPacket.logarithmic_width k ids c N hids
  simpa only [program, partsProgram, Program.maxBits, Nat.zero_max, boundary_bits,
    bitCoefficient, tableWidth, Nat.mul_max_mul_right] using max_le_max hp hb

section Expectation
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Same narrow order/classical equality-decision bridge as the frozen
CurrentFiniteBitPartition, with the actual active S retained. -/
theorem cut_source_eq (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (S : Finset V) (β : V → Bits Δ k b n) :
    cut G Δ k hk t b n S β = PriorityCut.cut G k hk (1 / (t : ℝ)) S n
      (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n
        (CurrentFiniteBitPartition.sourceEquiv V Δ k b n β)) := by
  unfold cut
  have hde : (fun a b : V => LinearOrder.toDecidableEq a b) = Classical.decEq V := Subsingleton.elim _ _
  rw [hde]

noncomputable def meanCut (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (S : Finset V) : ℝ :=
  (∑ β : V → Bits Δ k b n, (cut G Δ k hk t b n S β : ℝ)) / Fintype.card (V → Bits Δ k b n)

noncomputable def meanBoundary {ids : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ) (S : Finset V) : ℝ :=
  (∑ β : V → Bits Δ k b n, ((flagged G I Δ k t b n S β).card : ℝ)) / Fintype.card (V → Bits Δ k b n)

/-- Exact average over independent per-vertex Boolean tables; all parameters
precede V,G,S and the public ID codec. Every scale factor is |S|. -/
theorem parameters (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {W : Type} [Fintype W] [LinearOrder W] (H : SimpleGraph W) [DecidableRel H.Adj],
        SeparatorBalance.Bound H C (2 / 3) → (∀ v, H.degree v ≤ Δ) → ∀ (S : Finset W) {ids : ℕ} (I : BitCode W ids),
        (∑ β : W → Bits Δ k b n, (cut H Δ k hk t b n S β : ℝ)) ≤
          η * Fintype.card (W → Bits Δ k b n) * S.card ∧
        (∑ β : W → Bits Δ k b n, ((flagged H I Δ k t b n S β).card : ℝ)) ≤
          2 * η * Fintype.card (W → Bits Δ k b n) * S.card ∧
        meanCut H Δ k hk t b n S ≤ η * S.card ∧ meanBoundary H I Δ k t b n S ≤ 2 * η * S.card := by
  obtain ⟨t, k, b, n, ht, hk, hparams⟩ := HumanPartition.parameters C hC Δ η hη
  refine ⟨t, k, b, n, ht, hk, ?_⟩
  intro W _ _ H _ hprofile hdeg S ids I
  have hh := hparams H hprofile hdeg S
  have he := Equiv.sum_comp (CurrentFiniteBitPartition.sourceEquiv W Δ k b n)
    (fun ω => (PriorityCut.cut H k hk (1 / (t : ℝ)) S n
      (PriorityNormalization.localSeed H Δ k (2 ^ b) (by positivity) n ω) : ℝ))
  have hc := Fintype.card_congr (CurrentFiniteBitPartition.sourceEquiv W Δ k b n)
  have hcut : (∑ β : W → Bits Δ k b n, (cut H Δ k hk t b n S β : ℝ)) ≤
      η * Fintype.card (W → Bits Δ k b n) * S.card := by
    simp only [cut_source_eq]
    calc
      _ = ∑ ω : (Fin n × PriorityNormalization.Coordinate W Δ k) → Fin (2 ^ b),
          (PriorityCut.cut H k hk (1 / (t : ℝ)) S n
            (PriorityNormalization.localSeed H Δ k (2 ^ b) (by positivity) n ω) : ℝ) := he
      _ ≤ η * Fintype.card ((Fin n × PriorityNormalization.Coordinate W Δ k) → Fin (2 ^ b)) * S.card := hh
      _ = _ := congrArg (fun m : ℕ => η * m * S.card) hc.symm
  have hpoint (β : W → Bits Δ k b n) : ((flagged H I Δ k t b n S β).card : ℝ) ≤
      2 * (cut H Δ k hk t b n S β : ℝ) := by
    exact_mod_cast boundary_count H I Δ k hk t ht b n S β hdeg
  have hsum := Finset.sum_le_sum (fun β (_ : β ∈ (Finset.univ : Finset (W → Bits Δ k b n))) => hpoint β)
  rw [← Finset.mul_sum] at hsum
  have hbdy : (∑ β : W → Bits Δ k b n, ((flagged H I Δ k t b n S β).card : ℝ)) ≤
      2 * η * Fintype.card (W → Bits Δ k b n) * S.card := by
    calc
      _ ≤ 2 * ∑ β : W → Bits Δ k b n, (cut H Δ k hk t b n S β : ℝ) := hsum
      _ ≤ 2 * (η * Fintype.card (W → Bits Δ k b n) * S.card) := mul_le_mul_of_nonneg_left hcut (by norm_num)
      _ = _ := by ring
  have hposN : 0 < Fintype.card (W → Bits Δ k b n) :=
    Fintype.card_pos_iff.mpr ⟨fun _ _ _ => false⟩
  have hpos : (0 : ℝ) < Fintype.card (W → Bits Δ k b n) := by exact_mod_cast hposN
  refine ⟨hcut, hbdy, (div_le_iff₀ hpos).mpr ?_, (div_le_iff₀ hpos).mpr ?_⟩
  · calc
      _ ≤ η * Fintype.card (W → Bits Δ k b n) * S.card := hcut
      _ = _ := by ring
  · calc
      _ ≤ 2 * η * Fintype.card (W → Bits Δ k b n) * S.card := hbdy
      _ = _ := by ring
end Expectation

end Paper.ActiveFiniteBitPartition

#print axioms Paper.ActiveFiniteBitPartition.bits_per_vertex
#print axioms Paper.ActiveFiniteBitPartition.parts_rounds
#print axioms Paper.ActiveFiniteBitPartition.rounds
#print axioms Paper.ActiveFiniteBitPartition.boundary_bits
#print axioms Paper.ActiveFiniteBitPartition.parts_correct
#print axioms Paper.ActiveFiniteBitPartition.correct
#print axioms Paper.ActiveFiniteBitPartition.output_part
#print axioms Paper.ActiveFiniteBitPartition.inactive
#print axioms Paper.ActiveFiniteBitPartition.partition_empty
#print axioms Paper.ActiveFiniteBitPartition.empty_active
#print axioms Paper.ActiveFiniteBitPartition.empty_physical
#print axioms Paper.ActiveFiniteBitPartition.flagged_eq
#print axioms Paper.ActiveFiniteBitPartition.cut_eq
#print axioms Paper.ActiveFiniteBitPartition.boundary_count
#print axioms Paper.ActiveFiniteBitPartition.maxBits
#print axioms Paper.ActiveFiniteBitPartition.logarithmic_bits
#print axioms Paper.ActiveFiniteBitPartition.cut_source_eq
#print axioms Paper.ActiveFiniteBitPartition.parameters
