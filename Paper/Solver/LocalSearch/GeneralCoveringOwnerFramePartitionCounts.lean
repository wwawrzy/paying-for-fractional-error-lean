import Paper.Solver.LocalSearch.GeneralCoveringOwnerFramePartition
import Paper.Averaging.Tasks.FiniteLocalMean

/-! Local enumeration of actual FramePartition coin arrays. Part names are
finsets; the joint event also tests the computed boundary Bool at the anchor.
UniformProjection explicitly accounts for unused padding coordinates. Only
unique frame addresses embed into V; the full slot type never needs to do so.
No task score or physical fractional-output mean is asserted here. -/
namespace Paper.GeneralCoveringOwnerFramePartitionCounts
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry GeneralCoveringOwnerFramePartition
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def vertexBits (Δ k b n : ℕ) : ℕ := n * 2 ^ ((Δ + 1) ^ k) * b
def totalBits (Δ k b n : ℕ) : ℕ := slots Δ k n * vertexBits Δ k b n
def denominator (Δ k b n : ℕ) : ℕ := FiniteLocalMean.denominator (Bits Δ k b n) (slots Δ k n)
def paddingMultiplicity (Δ k b n used : ℕ) : ℕ := Fintype.card (Bits Δ k b n) ^ (slots Δ k n - used)

theorem card_bits (Δ k b n : ℕ) : Fintype.card (Bits Δ k b n) = 2 ^ vertexBits Δ k b n := by
  have hp := CurrentFiniteBitPartition.bits_per_vertex Δ k b n
  rw [Fintype.card_prod, Fintype.card_fin] at hp
  have he : b * Fintype.card (CurrentFiniteBitPartition.Index Δ k n) = vertexBits Δ k b n :=
    (Nat.mul_comm b _).trans hp
  change Fintype.card (CurrentFiniteBitPartition.Index Δ k n → Fin b → Bool) = _
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, he]

theorem denominator_power (Δ k b n : ℕ) : denominator Δ k b n = 2 ^ totalBits Δ k b n := by
  rw [denominator, FiniteLocalMean.denominator, card_bits, ← pow_mul]
  exact congrArg (fun m => 2 ^ m) (Nat.mul_comm _ _)

theorem card_coins (Δ k b n : ℕ) : Fintype.card (Coins Δ k b n) = denominator Δ k b n := by
  simp only [Coins, Fintype.card_fun, Fintype.card_fin, denominator, FiniteLocalMean.denominator]

theorem denominator_pos (Δ k b n : ℕ) : 0 < denominator Δ k b n := by
  rw [denominator_power]
  positivity

theorem denominator_b_zero (Δ k n : ℕ) : denominator Δ k 0 n = 1 := by
  rw [denominator_power]
  simp only [totalBits, vertexBits, Nat.mul_zero, pow_zero]

theorem denominator_n_zero (Δ k b : ℕ) : denominator Δ k b 0 = 1 := by
  rw [denominator_power]
  simp only [totalBits, vertexBits, Nat.zero_mul, Nat.mul_zero, pow_zero]

theorem padding_power (Δ k b n used : ℕ) :
    paddingMultiplicity Δ k b n used = 2 ^ (vertexBits Δ k b n * (slots Δ k n - used)) := by
  rw [paddingMultiplicity, card_bits, ← pow_mul]

def joint (T : Finset V) (flag : Bool) (value : Option (Finset V × Bool)) : Bool :=
  match value with
  | none => false
  | some z => decide (z = (T, flag))

def rawCount (Δ k b n : ℕ) (obs : Coins Δ k b n → Option (Finset V × Bool))
    (E : Option (Finset V × Bool) → Bool) : ℕ := ∑ ω : Coins Δ k b n, (E (obs ω)).toNat

theorem rawCount_le (Δ k b n : ℕ) (obs : Coins Δ k b n → Option (Finset V × Bool))
    (E : Option (Finset V × Bool) → Bool) : rawCount Δ k b n obs E ≤ denominator Δ k b n := by
  calc
    _ ≤ ∑ _ω : Coins Δ k b n, 1 := by
      apply Finset.sum_le_sum
      intro ω _
      cases E (obs ω) <;> decide
    _ = Fintype.card (Coins Δ k b n) := by simp
    _ = _ := card_coins Δ k b n

def boundedCount (Δ k b n : ℕ) (obs : Coins Δ k b n → Option (Finset V × Bool))
    (E : Option (Finset V × Bool) → Bool) : Fin (denominator Δ k b n + 1) :=
  ⟨rawCount Δ k b n obs E, Nat.lt_succ_of_le (rawCount_le Δ k b n obs E)⟩

theorem part_split (Δ k b n : ℕ) (obs : Coins Δ k b n → Option (Finset V × Bool)) (T : Finset V) :
    rawCount Δ k b n obs (fun value => occurs value T) =
      rawCount Δ k b n obs (joint T false) + rawCount Δ k b n obs (joint T true) := by
  unfold rawCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  cases ho : obs ω with
  | none => rfl
  | some z =>
    rcases z with ⟨S, flag⟩
    cases flag <;> by_cases h : S = T <;> simp [occurs, joint, h]

structure Output (V : Type) (L Δ k b n : ℕ) where
  source : GeneralCoveringOwnerFramePartition.Output V L Δ k b n
  partCount : V → Finset V → Fin (denominator Δ k b n + 1)
  jointCount : V → Finset V → Bool → Fin (denominator Δ k b n + 1)

/-- A repeated list representation is still one canonical full-part name. -/
def namedCount {L Δ k b n : ℕ} (s : Output V L Δ k b n) (a : V) (name : List V) :
    Fin (denominator Δ k b n + 1) := s.partCount a name.toFinset

theorem name_repetition {L Δ k b n : ℕ} (s : Output V L Δ k b n) (a : V) (name : List V) :
    namedCount s a (name ++ name) = namedCount s a name := by
  simp only [namedCount, List.toFinset_append, Finset.union_self]

def finish {L Δ k b n : ℕ} (s : GeneralCoveringOwnerFramePartition.Output V L Δ k b n) : Output V L Δ k b n :=
  ⟨s, fun a T => boundedCount Δ k b n (s.answer a) (fun value => occurs value T),
    fun a T flag => boundedCount Δ k b n (s.answer a) (joint T flag)⟩

/-- All enumeration domains/denominators precede the graph. The source
program executes once; its retained answer is a pure local finite query. -/
def program {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (Output V L Δ k b n) :=
  .seq (GeneralCoveringOwnerFramePartition.program ids L Δ k t b n) (.local fun _ _ s => finish s)

def frameCount {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (E : Option (Finset V × Bool) → Bool) : ℕ :=
  rawCount Δ k b n (fun ω => some (evaluate ids Δ k t b n xs a ω)) E

def arrayFromRecords {Δ : ℕ} (k b n : ℕ) (xs : List (TopologyGather.Record V Δ))
    (ys : List (V × Bits Δ k b n)) : Coins Δ k b n :=
  restrict k b n xs (FrameInterpreter.inputs ys (zeroBits Δ k b n))

def eventRecords {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (E : Option (Finset V × Bool) → Bool)
    (ys : List (V × Bits Δ k b n)) : ℕ :=
  (E (some (evaluate ids Δ k t b n xs a (arrayFromRecords k b n xs ys)))).toNat

/-- Exact independence of every unused slot, before choosing zero padding. -/
theorem evaluate_used_slots {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (h : (addresses xs).length ≤ slots Δ k n)
    (ω ν : Coins Δ k b n)
    (he : ∀ i, ω (LocalSeedRecords.slot (addresses xs) h i) = ν (LocalSeedRecords.slot (addresses xs) h i)) :
    evaluate ids Δ k t b n xs a ω = evaluate ids Δ k t b n xs a ν := by
  have hs : seedRecords k b n xs ω = seedRecords k b n xs ν := by
    simp only [seedRecords, dif_pos h, LocalSeedRecords.records]
    apply congrArg (LocalSeedRecords.base (addresses xs))
    funext i
    exact congrArg (fun z => (true, z)) (he i)
  exact congrArg (fun ys => FrameInterpreter.evaluate (ActiveFiniteBitPartition.program ids Δ k t b n)
    xs ys (true, zeroBits Δ k b n) a) hs

theorem zero_padding {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (h : (addresses xs).length ≤ slots Δ k n) (ω : Coins Δ k b n) :
    evaluate ids Δ k t b n xs a (restrict k b n xs (extend k b n xs ω)) = evaluate ids Δ k t b n xs a ω := by
  apply evaluate_used_slots ids Δ k t b n xs a h
  intro i
  rw [restrict_slot k b n xs _ h i, extend_slot k b n xs ω h i]

theorem records_event {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (h : (addresses xs).length ≤ slots Δ k n)
    (E : Option (Finset V × Bool) → Bool) (ω : Coins Δ k b n) :
    eventRecords ids Δ k t b n xs a E (LocalSeedRecords.records (addresses xs) h ω) =
      (E (some (evaluate ids Δ k t b n xs a ω))).toNat := by
  have he : FrameInterpreter.inputs (LocalSeedRecords.records (addresses xs) h ω) (zeroBits Δ k b n) =
      extend k b n xs ω := by
    unfold extend coinRecords
    rw [dif_pos h] <;> rfl
  have hval := (congrArg (fun σ => evaluate ids Δ k t b n xs a (restrict k b n xs σ)) he).trans
    (zero_padding ids Δ k t b n xs a h ω)
  exact congrArg (fun value => (E (some value)).toNat) hval

theorem base_event {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (E : Option (Finset V × Bool) → Bool)
    (β : V → Bits Δ k b n) :
    eventRecords ids Δ k t b n xs a E (LocalSeedRecords.base (addresses xs) (fun i => β ((addresses xs).get i))) =
      (E (some (evaluate ids Δ k t b n xs a (restrict k b n xs β)))).toNat := by
  have he : arrayFromRecords k b n xs (LocalSeedRecords.base (addresses xs) (fun i => β ((addresses xs).get i))) =
      restrict k b n xs β := by
    funext j
    unfold arrayFromRecords restrict
    split_ifs with hj
    · exact LocalSeedRecords.inputs_base (addresses xs) β (zeroBits Δ k b n) _ ((addresses xs).get_mem _)
    · rfl
  exact congrArg (fun ω => (E (some (evaluate ids Δ k t b n xs a ω))).toNat) he

theorem frame_count_numerator {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (h : (addresses xs).length ≤ slots Δ k n)
    (E : Option (Finset V × Bool) → Bool) :
    frameCount ids Δ k t b n xs a E =
      FiniteLocalMean.numerator (addresses xs) h (eventRecords ids Δ k t b n xs a E) := by
  unfold frameCount rawCount FiniteLocalMean.numerator
  apply Finset.sum_congr rfl
  intro ω _
  exact (records_event ids Δ k t b n xs a h E ω).symm

/-- Every assignment on used slots has exactly the displayed padding factor.
This has no hypothesis comparing slots with the physical vertex count. -/
theorem padding_fibers {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (h : (addresses xs).length ≤ slots Δ k n)
    (E : Option (Finset V × Bool) → Bool) :
    (frameCount ids Δ k t b n xs a E : ℝ) =
      paddingMultiplicity Δ k b n (addresses xs).length *
        ∑ τ : Fin (addresses xs).length → Bits Δ k b n,
          (eventRecords ids Δ k t b n xs a E (LocalSeedRecords.base (addresses xs) τ) : ℝ) := by
  let e := LocalSeedRecords.slot (addresses xs) h
  have hinj : Function.Injective e := LocalSeedRecords.slot_injective (addresses xs) h
  let f := fun τ : Fin (addresses xs).length → Bits Δ k b n =>
    (eventRecords ids Δ k t b n xs a E (LocalSeedRecords.base (addresses xs) τ) : ℝ)
  have hp := UniformProjection.sum_scaled e hinj f
  have hc : Fintype.card (Coins Δ k b n) =
      Fintype.card (Fin (addresses xs).length → Bits Δ k b n) *
        paddingMultiplicity Δ k b n (addresses xs).length := by
    simp only [Coins, Fintype.card_fun, Fintype.card_fin, paddingMultiplicity]
    have hexp : (addresses xs).length + (slots Δ k n - (addresses xs).length) = slots Δ k n := by omega
    rw [← pow_add, hexp]
  have hn : (frameCount ids Δ k t b n xs a E : ℝ) =
      ∑ ω : Coins Δ k b n, f (fun i => ω (e i)) := by
    rw [frame_count_numerator ids Δ k t b n xs a h E, FiniteLocalMean.numerator, Nat.cast_sum]
    rfl
  have hpos : (Fintype.card (Fin (addresses xs).length → Bits Δ k b n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Fin (addresses xs).length → Bits Δ k b n)))
  rw [hn]
  apply mul_left_cancel₀ hpos
  calc
    _ = (Fintype.card (Coins Δ k b n) : ℝ) * ∑ τ, f τ := hp
    _ = _ := by rw [hc, Nat.cast_mul]; ring

/-- An empty supplied frame is constant over every coin assignment. It is
not confused with the native missing-anchor event, whose count is zero. -/
theorem empty_frame_count {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ) (a : V)
    (E : Option (Finset V × Bool) → Bool) :
    frameCount ids Δ k t b n [] a E = denominator Δ k b n *
      (E (some (evaluate ids Δ k t b n [] a (fun _ => zeroBits Δ k b n)))).toNat := by
  have hl : (addresses ([] : List (TopologyGather.Record V Δ))).length = 0 := by
    simp [addresses, TaggedDictionary.keys]
  have hsize : (addresses ([] : List (TopologyGather.Record V Δ))).length ≤ slots Δ k n := by
    rw [hl]
    exact Nat.zero_le _
  have he : ∀ ω : Coins Δ k b n, evaluate ids Δ k t b n [] a ω =
      evaluate ids Δ k t b n [] a (fun _ => zeroBits Δ k b n) := by
    intro ω
    apply evaluate_used_slots ids Δ k t b n [] a hsize
    intro i
    have hi := i.isLt
    omega
  simp only [frameCount, rawCount, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_coins, Nat.cast_id]

variable [Fintype V]

theorem addresses_injective {Δ : ℕ} (xs : List (TopologyGather.Record V Δ)) :
    Function.Injective (addresses xs).get := by
  have hnodup : (addresses xs).Nodup := Finset.sort_nodup _ _
  exact hnodup.injective_get

/-- The two finite projections are used separately by the received API. -/
theorem frame_mean {idBits : ℕ} (ids : BitCode V idBits) (Δ k t b n : ℕ)
    (xs : List (TopologyGather.Record V Δ)) (a : V) (h : (addresses xs).length ≤ slots Δ k n)
    (E : Option (Finset V × Bool) → Bool) :
    (frameCount ids Δ k t b n xs a E : ℝ) / denominator Δ k b n =
      (∑ β : V → Bits Δ k b n, ((E (some (evaluate ids Δ k t b n xs a (restrict k b n xs β)))).toNat : ℝ)) /
        Fintype.card (V → Bits Δ k b n) := by
  have hnodup : (addresses xs).Nodup := Finset.sort_nodup _ _
  have hm := FiniteLocalMean.numerator_mean_eq (addresses xs) hnodup h (eventRecords ids Δ k t b n xs a E)
  rw [frame_count_numerator ids Δ k t b n xs a h E]
  apply hm.trans
  apply congrArg (fun z : ℝ => z / Fintype.card (V → Bits Δ k b n))
  apply Finset.sum_congr rfl
  intro β _
  exact congrArg (fun z : ℕ => (z : ℝ)) (base_event ids Δ k t b n xs a E β)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem post_run {In X Y : Type} (P : Program V In X) (f : X → Y) (input : V → In) :
    (Program.seq P (Program.local fun _ _ s => f s)).runEncoded G input = fun v => f (P.runEncoded G input v) := rfl

def produced {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) (input : V → GeneralCoveringOwners.Input V) :=
  (GeneralCoveringOwnerFramePartition.program ids L Δ k t b n).runEncoded G input

theorem run_program {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ k t b n).runEncoded G input = fun v => finish (produced G ids L Δ k t b n input v) :=
  post_run G _ _ input

theorem source_retained {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ k t b n).runEncoded G input v).source = produced G ids L Δ k t b n input v := by
  rw [run_program] <;> rfl

theorem part_run {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V) (T : Finset V) :
    (((program ids L Δ k t b n).runEncoded G input v).partCount a T).val =
      rawCount Δ k b n ((produced G ids L Δ k t b n input v).answer a) (fun value => occurs value T) := by
  rw [run_program] <;> rfl

theorem joint_run {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V) (T : Finset V) (flag : Bool) :
    (((program ids L Δ k t b n).runEncoded G input v).jointCount a T flag).val =
      rawCount Δ k b n ((produced G ids L Δ k t b n input v).answer a) (joint T flag) := by
  rw [run_program] <;> rfl

theorem private_input_retained {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ k t b n).runEncoded G input v).source.source.source.env.metadata.owned.input = input v := by
  rw [source_retained]
  exact GeneralCoveringOwnerFramePartition.private_input_retained G ids L Δ k t b n input v

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).Adj := fun _ _ => Classical.propDecidable _

section Correct
variable (C targets : V → Finset V) (D R : Finset V) (L Δ k t b n : ℕ)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q

theorem answer_frame {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (ω : Coins Δ k b n) :
    (produced G ids L Δ k t b n input v).answer a ω = some (evaluate ids Δ k t b n (frame G ids L Δ k n input v a) a ω) := by
  have he : TaggedDictionary.lookup (snapshot G ids L Δ k n input v).frames a =
      some (frame G ids L Δ k n input v a) :=
    GeneralCoveringOwnerRoleFrames.frame_lookup G ids L Δ (outerRadius k n) k (radius k n) input v a ha
  exact (GeneralCoveringOwnerFramePartition.native_query G ids L Δ k t b n input v a ω).trans
    (congrArg (fun value : Option (List (TopologyGather.Record V Δ)) => value.map (fun xs => evaluate ids Δ k t b n xs a ω)) he)

theorem native_frame_count {idBits : ℕ} (ids : BitCode V idBits) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (E : Option (Finset V × Bool) → Bool) :
    rawCount Δ k b n ((produced G ids L Δ k t b n input v).answer a) E =
      frameCount ids Δ k t b n (frame G ids L Δ k n input v a) a E := by
  unfold frameCount rawCount
  apply Finset.sum_congr rfl
  intro ω _
  exact congrArg (fun value => (E value).toNat) (answer_frame G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha ω)

theorem native_law {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (E : Option (Finset V × Bool) → Bool) :
    (rawCount Δ k b n ((produced G ids L Δ k t b n input v).answer a) E : ℝ) / denominator Δ k b n =
      (∑ β : V → Bits Δ k b n,
        ((E (some (DisjointPartLabels.label (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts a,
          decide (a ∈ BoundaryOwners.vertices J U (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts)))).toNat : ℝ)) /
        Fintype.card (V → Bits Δ k b n) := by
  rw [native_frame_count G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha E]
  apply (frame_mean ids Δ k t b n (frame G ids L Δ k n input v a) a
    (GeneralCoveringOwnerFramePartition.frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) E).trans
  apply congrArg (fun z : ℝ => z / Fintype.card (V → Bits Δ k b n))
  apply Finset.sum_congr rfl
  intro β _
  have he := (GeneralCoveringOwnerFramePartition.evaluate_restricted G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha β).trans
    (ActiveFiniteBitPartition.correct J ids Δ k hk t ht b n U β (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a)
  exact congrArg (fun value => ((E (some value)).toNat : ℝ)) he

theorem part_spec {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (T : Finset V) :
    ((((program ids L Δ k t b n).runEncoded G input v).partCount a T).val : ℝ) / denominator Δ k b n =
      (∑ β : V → Bits Δ k b n,
        ((decide (DisjointPartLabels.label (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts a = T)).toNat : ℝ)) /
        Fintype.card (V → Bits Δ k b n) := by
  rw [part_run]
  exact native_law G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v a ha (fun value => occurs value T)

theorem joint_spec {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v a : V)
    (ha : a ∈ (snapshot G ids L Δ k n input v).anchors) (T : Finset V) (flag : Bool) :
    ((((program ids L Δ k t b n).runEncoded G input v).jointCount a T flag).val : ℝ) / denominator Δ k b n =
      (∑ β : V → Bits Δ k b n,
        ((decide ((DisjointPartLabels.label (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts a,
          decide (a ∈ BoundaryOwners.vertices J U (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts)) = (T, flag))).toNat : ℝ)) /
        Fintype.card (V → Bits Δ k b n) := by
  rw [joint_run]
  exact native_law G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v a ha (joint T flag)

theorem common_count {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v w a : V)
    (hv : a ∈ (snapshot G ids L Δ k n input v).anchors) (hw : a ∈ (snapshot G ids L Δ k n input w).anchors)
    (E : Option (Finset V × Bool) → Bool) :
    rawCount Δ k b n ((produced G ids L Δ k t b n input v).answer a) E =
      rawCount Δ k b n ((produced G ids L Δ k t b n input w).answer a) E := by
  have hmean := (native_law G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v a hv E).trans
    (native_law G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht w a hw E).symm
  have hden : (denominator Δ k b n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos Δ k b n))
  exact_mod_cast (div_left_inj' hden).mp hmean

theorem part_common {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v w a : V)
    (hv : a ∈ (snapshot G ids L Δ k n input v).anchors) (hw : a ∈ (snapshot G ids L Δ k n input w).anchors)
    (T : Finset V) :
    ((program ids L Δ k t b n).runEncoded G input v).partCount a T =
      ((program ids L Δ k t b n).runEncoded G input w).partCount a T := by
  apply Fin.ext
  exact (part_run G ids L Δ k t b n input v a T).trans
    ((common_count G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v w a hv hw
      (fun value => occurs value T)).trans (part_run G ids L Δ k t b n input w a T).symm)

theorem joint_common {idBits : ℕ} (ids : BitCode V idBits) (hk : 0 < k) (ht : 0 < t) (v w a : V)
    (hv : a ∈ (snapshot G ids L Δ k n input v).anchors) (hw : a ∈ (snapshot G ids L Δ k n input w).anchors)
    (T : Finset V) (flag : Bool) :
    ((program ids L Δ k t b n).runEncoded G input v).jointCount a T flag =
      ((program ids L Δ k t b n).runEncoded G input w).jointCount a T flag := by
  apply Fin.ext
  exact (joint_run G ids L Δ k t b n input v a T flag).trans
    ((common_count G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v w a hv hw
      (joint T flag)).trans (joint_run G ids L Δ k t b n input w a T flag).symm)

theorem empty_low {idBits : ℕ} (ids : BitCode V idBits) [IsEmpty (Low D Q)] (v a : V) (T : Finset V) (flag : Bool) :
    (((program ids L Δ k t b n).runEncoded G input v).partCount a T).val = 0 ∧
      (((program ids L Δ k t b n).runEncoded G input v).jointCount a T flag).val = 0 := by
  have he : ∀ ω : Coins Δ k b n, (produced G ids L Δ k t b n input v).answer a ω = none :=
    fun ω => GeneralCoveringOwnerFramePartition.empty_low G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ω
  rw [part_run, joint_run]
  simp only [rawCount, he, occurs, joint, Bool.toNat_false, Finset.sum_const_zero, and_self]
end Correct

theorem no_anchor {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v a : V) (ha : a ∉ (snapshot G ids L Δ k n input v).anchors)
    (T : Finset V) (flag : Bool) :
    (((program ids L Δ k t b n).runEncoded G input v).partCount a T).val = 0 ∧
      (((program ids L Δ k t b n).runEncoded G input v).jointCount a T flag).val = 0 := by
  have he : ∀ ω : Coins Δ k b n, (produced G ids L Δ k t b n input v).answer a ω = none :=
    fun ω => GeneralCoveringOwnerFramePartition.no_anchor G ids L Δ k t b n input v a ω ha
  rw [part_run, joint_run]
  simp only [rawCount, he, occurs, joint, Bool.toNat_false, Finset.sum_const_zero, and_self]

theorem empty_physical [IsEmpty V] {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ k t b n).runEncoded G input = fun v => isEmptyElim v := by
  funext v
  exact isEmptyElim v

theorem rounds {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) :
    (program ids L Δ k t b n).rounds = 12 + 4 * outerRadius k n := by
  simp only [program, Program.rounds, GeneralCoveringOwnerFramePartition.rounds, Nat.add_zero]

theorem maxBits_eq {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n : ℕ) :
    (program ids L Δ k t b n).maxBits = (GeneralCoveringOwnerFramePartition.program ids L Δ k t b n).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]

theorem logarithmic_public_card {idBits : ℕ} (ids : BitCode V idBits) (L Δ k t b n c : ℕ)
    (hids : idBits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids L Δ k t b n).maxBits ≤ max
      ((L + Δ + 3) * (c + (Δ + 1) ^ (outerRadius k n + 1) * (c + 1) + 2))
      (c + GeneralCoveringOwnerRootFrames.capacity Δ (outerRadius k n) * (c + Δ * (c + 1) + 1) + 1) *
        Nat.clog 2 (Fintype.card V + 2) := by
  rw [maxBits_eq]
  exact GeneralCoveringOwnerFramePartition.logarithmic_public_card ids L Δ k t b n c hids

end Paper.GeneralCoveringOwnerFramePartitionCounts

#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.card_bits
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.denominator_power
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.card_coins
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.denominator_pos
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.denominator_b_zero
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.denominator_n_zero
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.padding_power
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.rawCount_le
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.part_split
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.name_repetition
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.evaluate_used_slots
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.zero_padding
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.records_event
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.base_event
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.frame_count_numerator
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.padding_fibers
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.empty_frame_count
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.addresses_injective
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.frame_mean
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.run_program
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.source_retained
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.part_run
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.joint_run
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.private_input_retained
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.answer_frame
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.native_frame_count
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.native_law
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.part_spec
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.joint_spec
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.common_count
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.part_common
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.joint_common
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.empty_low
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.no_anchor
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.empty_physical
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.rounds
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.maxBits_eq
#print axioms Paper.GeneralCoveringOwnerFramePartitionCounts.logarithmic_public_card
