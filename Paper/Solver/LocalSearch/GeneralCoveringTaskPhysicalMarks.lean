import Paper.Solver.LocalSearch.GeneralCoveringTaskPartitionMarks
import Paper.Solver.LocalSearch.GeneralCoveringOwnerSimulation

/-! Physical preparation ONCE, then the actual Marks client translated through
the learned arbitrary-C low-owner graph. Active is read from Env.low; original
cost stays private. The unchanged Env survives for later task aggregation.
No active mask, part label, boundary or virtual neighbor list is external input.
This does not assert a separator profile, small eta cut or the full endpoint. -/
namespace Paper.GeneralCoveringTaskPhysicalMarks
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringOwners.Input V × Fin (B + 1)
abbrev Output (V : Type) (B : ℕ) := GeneralCoveringTaskRoles.Fields V B × GeneralCoveringOwnerVirtualPrepare.Env V

def initState (B : ℕ) : Program V (GeneralCoveringOwnerVirtualPrepare.Env V × Fin (B + 1))
    (GeneralCoveringTaskPartitionMarks.Input B × GeneralCoveringOwnerVirtualPrepare.Env V) :=
  .local (fun _ _ s => ((s.1.low, s.2), s.1))

/-- Exactly one physical preparer; translate never invokes execute/preparation. -/
def program {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ) : Program V (Input V B) (Output V B) :=
  .seq (ProgramMemory.carry (X := Fin (B + 1)) (GeneralCoveringOwnerVirtualPrepare.program ids L Δ))
    (.seq (initState B) (GeneralCoveringOwnerSimulation.translate ids L Δ
      (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem prepared_run {B : ℕ} {Out : Type}
    (prep : Program V (GeneralCoveringOwners.Input V) (GeneralCoveringOwnerVirtualPrepare.Env V))
    (client : Program V (GeneralCoveringTaskPartitionMarks.Input B × GeneralCoveringOwnerVirtualPrepare.Env V) Out)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) :
    (Program.seq (ProgramMemory.carry (X := Fin (B + 1)) prep) (Program.seq (initState B) client)).runEncoded G
      (fun v => (input v, c v)) =
      client.run G (fun v => (((prep.runEncoded G input v).low, c v), prep.runEncoded G input v)) := by
  rw [Program.runEncoded_eq_run]
  change client.run G ((initState B).run G
    ((ProgramMemory.carry (X := Fin (B + 1)) prep).run G (fun v => (input v, c v)))) = _
  rw [ProgramMemory.run G prep]
  change client.run G (fun v => (((prep.run G input v).low, c v), prep.run G input v)) = _
  rw [Program.runEncoded_eq_run G prep]

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) :
    (program ids L Δ k t T B).runEncoded G (fun v => (input v, c v)) =
      (GeneralCoveringOwnerSimulation.translate ids L Δ (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B)).run G
        (fun v => (( (GeneralCoveringOwnerSimulation.learned G ids L Δ input v).low, c v),
          GeneralCoveringOwnerSimulation.learned G ids L Δ input v)) := by
  exact prepared_run G (GeneralCoveringOwnerVirtualPrepare.program ids L Δ)
    (GeneralCoveringOwnerSimulation.translate ids L Δ (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B)) input c

theorem env_retained {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (v : V) :
    ((program ids L Δ k t T B).runEncoded G (fun u => (input u, c u)) v).2 =
      GeneralCoveringOwnerSimulation.learned G ids L Δ input v := by
  rw [run_program]
  exact GeneralCoveringOwnerSimulation.env_preserved G ids L Δ
    (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B) _ v

theorem private_input_retained {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (v : V) :
    ((program ids L Δ k t T B).runEncoded G (fun u => (input u, c u)) v).2.metadata.owned.input = input v := by
  exact (congrArg (fun e : GeneralCoveringOwnerVirtualPrepare.Env V => e.metadata.owned.input)
    (env_retained G ids L Δ k t T B input c v)).trans
    (GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v)

theorem incidences_retained {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (v : V) :
    ((program ids L Δ k t T B).runEncoded G (fun u => (input u, c u)) v).2.metadata.owned.input.candidates =
      (input v).candidates ∧
    ((program ids L Δ k t T B).runEncoded G (fun u => (input u, c u)) v).2.metadata.owned.input.targets =
      (input v).targets := by
  have h := private_input_retained G ids L Δ k t T B input c v
  exact ⟨congrArg GeneralCoveringOwners.Input.candidates h, congrArg GeneralCoveringOwners.Input.targets h⟩

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G cover D R L).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance lowAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G cover D R L Q).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance publicAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G cover D R L Q).Adj :=
  fun _ _ => Classical.propDecidable _

theorem embedding_eq (D : Finset V) (Q : Finset D) :
    GeneralCoveringOwnerVirtualPrepare.embedding D Q = GeneralCoveringTaskPartitionMarks.lowEmbedding D Q := rfl

theorem image_eq (D : Finset V) (Q : Finset D) : GeneralCoveringOwnerVirtualPrepare.image D Q =
    GeneralCoveringTaskPartitionMarks.activeImage (GeneralCoveringTaskPartitionMarks.lowEmbedding D Q) := rfl

theorem publicGraph_eq (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    GeneralCoveringOwnerVirtualPrepare.publicGraph G cover D R L Q =
      PublicEmbedding.graph (graph G cover D R L Q) (GeneralCoveringTaskPartitionMarks.lowEmbedding D Q) := rfl

/-- Actual induced low degree, derived from the producer's public degree theorem. -/
theorem low_degree (cover : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (i : Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)) :
    (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)).degree i ≤ Δ := by
  have h := GeneralCoveringOwnerVirtualPrepare.public_degree_bound G cover D R L Δ i.val.val
  refine le_trans (le_of_eq ?_) h
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← Finset.card_image_of_injective _ (GeneralCoveringOwnerVirtualPrepare.embedding D
    (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)).injective]
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  let J := graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)
  let e := GeneralCoveringOwnerVirtualPrepare.embedding D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)
  constructor
  · rintro ⟨j, hij, he⟩
    exact (PublicEmbedding.adj_iff J e (e i) v).mpr ⟨i, j, hij, rfl, he⟩
  · intro hv
    obtain ⟨a, j, haj, ha, hj⟩ := (PublicEmbedding.adj_iff J e (e i) v).mp hv
    have hai : a = i := e.injective ha
    exact ⟨j, hai ▸ haj, hj⟩

/-- Full encoded execution on physical G equals the actual Marks client on
the actual public low graph, with Q=the computed high set and original cost. -/
theorem correct {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) :
    (program ids L Δ k t T B).runEncoded G (fun v => (input v, c v)) = fun v =>
      ((GeneralCoveringTaskPartitionMarks.program ids Δ k t T B).runEncoded
        (GeneralCoveringOwnerVirtualPrepare.publicGraph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))
        (fun u => (decide (u ∈ GeneralCoveringOwnerVirtualPrepare.image D
          (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)), c u)) v,
        GeneralCoveringOwnerSimulation.learned G ids L Δ input v) := by
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids cover targets D R L Δ hinc hlocal input hD hR hC ht
  have hin : (fun v => ((GeneralCoveringOwnerSimulation.learned G ids L Δ input v).low, c v)) =
      fun v => (decide (v ∈ GeneralCoveringOwnerVirtualPrepare.image D
        (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)), c v) := by
    funext v
    exact Prod.ext (hs.2.2.1 v) rfl
  rw [run_program, GeneralCoveringOwnerSimulation.translate_correct G ids cover targets D R L Δ
    hinc hlocal input hD hR hC ht (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B), hin,
    Program.runEncoded_eq_run]

/-- Proof-side actual partition, pulled from the physically simulated computed output. -/
noncomputable def partition {bits : ℕ} (ids : BitCode V bits) (cover : V → Finset V)
    (D R : Finset V) (L Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) :
    SmallParts.Data (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)) Finset.univ k :=
  GeneralCoveringTaskPartitionMarks.pulledPartition
    (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))
    (GeneralCoveringTaskPartitionMarks.lowEmbedding D _) ids Δ k t T hk ht (low_degree G cover D R L Δ)

/-- The physical output supplies exactly the cost/name/excluded/interior fields
required by later aggregation, plus the original immutable learned environment. -/
theorem fields_spec {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ) (hk : 0 < k) (ht' : 0 < t)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) :
    let Q := GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ
    let P := partition G ids cover D R L Δ k t T hk ht'
    let out := (program ids L Δ k t T B).runEncoded G (fun v => (input v, c v))
    (∀ v, (out v).1.cost = c v) ∧
      (∀ (U : Finset (Low D Q)) (hU : U ∈ P.parts) (i : Low D Q), i ∈ U →
        (out i.val.val).1.role = some (GeneralCoveringTaskRoles.name D Q U (P.nonempty U hU))) ∧
      (∀ d : D, d ∈ Q → (out d.val).1.role = none) ∧
      (∀ i : Low D Q, (out i.val.val).1.interior =
        decide (i ∉ BoundaryOwners.vertices (graph G cover D R L Q) Finset.univ P.parts)) ∧
      (∀ v, (out v).2 = GeneralCoveringOwnerSimulation.learned G ids L Δ input v) ∧
      (∀ v, (out v).2.metadata.owned.input = input v) := by
  dsimp only
  rw [correct G ids L Δ k t T B cover targets D R hinc hlocal input c hD hR hC ht]
  have hm := GeneralCoveringTaskPartitionMarks.low_fields G cover D R L
    (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ) ids Δ k t T B hk ht' (low_degree G cover D R L Δ) c
  refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, fun _ => rfl, ?_⟩
  intro v
  exact GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v

theorem outside_low {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) (v : V)
    (hv : v ∉ GeneralCoveringOwnerVirtualPrepare.image D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)) :
    (program ids L Δ k t T B).runEncoded G (fun u => (input u, c u)) v =
      (⟨c v, none, false⟩, GeneralCoveringOwnerSimulation.learned G ids L Δ input v) := by
  have he := congrFun (correct G ids L Δ k t T B cover targets D R hinc hlocal input c hD hR hC ht) v
  have hm := GeneralCoveringTaskPartitionMarks.inactive
    (GeneralCoveringOwnerVirtualPrepare.publicGraph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))
    ids Δ k t T B (fun u => (decide (u ∈ GeneralCoveringOwnerVirtualPrepare.image D
      (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)), c u)) v (decide_eq_false hv)
  exact he.trans (congrArg (fun f : GeneralCoveringTaskRoles.Fields V B =>
    (f, GeneralCoveringOwnerSimulation.learned G ids L Δ input v)) hm)

theorem empty_centers {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (cover targets : V → Finset V) (D R : Finset V) (hEmpty : D = ∅)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) (v : V) :
    (program ids L Δ k t T B).runEncoded G (fun u => (input u, c u)) v =
      (⟨c v, none, false⟩, GeneralCoveringOwnerSimulation.learned G ids L Δ input v) := by
  apply outside_low G ids L Δ k t T B cover targets D R hinc hlocal input c hD hR hC ht v
  intro hv
  obtain ⟨i, _, _⟩ := (GeneralCoveringOwnerVirtualPrepare.mem_image D _ v).mp hv
  have hi : i.val ∈ (∅ : Finset V) :=
    (congrArg (fun S : Finset V => (i.val : V) ∈ S) hEmpty).mp i.property
  exact Finset.notMem_empty _ hi

theorem empty_low {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (cover targets : V → Finset V) (D R : Finset V)
    [IsEmpty (Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))]
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) (v : V) :
    (program ids L Δ k t T B).runEncoded G (fun u => (input u, c u)) v =
      (⟨c v, none, false⟩, GeneralCoveringOwnerSimulation.learned G ids L Δ input v) := by
  apply outside_low G ids L Δ k t T B cover targets D R hinc hlocal input c hD hR hC ht v
  intro hv
  obtain ⟨i, _, _⟩ := Finset.mem_image.mp hv
  exact isEmptyElim i

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) :
    (program ids L Δ k t T B).runEncoded G (fun v => (input v, c v)) =
      fun v => (⟨c v, none, false⟩, GeneralCoveringOwnerSimulation.learned G ids L Δ input v) := by
  funext v
  exact isEmptyElim v

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ) :
    (program ids L Δ k t T B).rounds = 10 + 4 * (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B).rounds := by
  simp only [program, initState, Program.rounds, ProgramMemory.rounds, GeneralCoveringOwnerVirtualPrepare.rounds,
    GeneralCoveringOwnerSimulation.rounds, Nat.zero_add]

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ) :
    (program ids L Δ k t T B).maxBits ≤
      (L + Δ + 3) * (bits + (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B).maxBits + 2) := by
  simp only [program, initState, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]
  apply max_le
  · exact (GeneralCoveringOwnerVirtualPrepare.maxBits ids L Δ).trans (by nlinarith)
  · exact (GeneralCoveringOwnerSimulation.maxBits ids L Δ
      (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B)).trans (by nlinarith)

def roundCoefficient (L Δ k T c p d : ℕ) : ℕ :=
  10 + 4 * DeterministicPartitionBoundaryProgram.roundCoefficient Δ k T c p d

def bitCoefficient (L Δ k c p d : ℕ) : ℕ := (L + Δ + 3) *
  (DeterministicColorReductionIdentifiers.bitFactor c p d + DeterministicPartitionBoundaryProgram.bitCoefficient Δ k c p d + 2)

theorem costs {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B c p d M : ℕ)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program ids L Δ k t T B).rounds ≤ roundCoefficient L Δ k T c p d *
      (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
    (program ids L Δ k t T B).maxBits ≤ bitCoefficient L Δ k c p d * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := GeneralCoveringTaskPartitionMarks.costs ids Δ k t T B c p d M hbits hM
  have hi := DeterministicColorReductionIdentifiers.public_length_bound (Fintype.card V) bits c p d M hbits hM
  have hl : 1 ≤ Nat.clog 2 (Fintype.card V + 2) := Nat.clog_pos (by omega) (by omega)
  constructor
  · rw [rounds]
    unfold roundCoefficient
    nlinarith [hp.1]
  · have hb : bits + (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B).maxBits + 2 ≤
        (DeterministicColorReductionIdentifiers.bitFactor c p d +
          DeterministicPartitionBoundaryProgram.bitCoefficient Δ k c p d + 2) * Nat.clog 2 (Fintype.card V + 2) := by
      nlinarith [hp.2]
    apply (maxBits ids L Δ k t T B).trans
    simpa only [bitCoefficient, Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb

end Paper.GeneralCoveringTaskPhysicalMarks

#print axioms Paper.GeneralCoveringTaskPhysicalMarks.run_program
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.env_retained
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.private_input_retained
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.incidences_retained
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.embedding_eq
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.image_eq
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.publicGraph_eq
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.low_degree
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.correct
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.partition
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.fields_spec
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.outside_low
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.empty_centers
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.empty_low
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.empty_physical
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.rounds
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.maxBits
#print axioms Paper.GeneralCoveringTaskPhysicalMarks.costs
