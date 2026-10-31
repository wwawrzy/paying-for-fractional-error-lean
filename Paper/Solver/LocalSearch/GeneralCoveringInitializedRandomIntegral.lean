import Paper.Solver.LocalSearch.GeneralCoveringRandomIntegralPhysical

/-! One actual initializer, retaining original private incidence data, cost
and the SAME public-vertex coins, then one actual random integral physical
program. Its center bit is the received initializer selection. This is a
pointwise execution/coverage/additive-cost contract; uniform expected
approximation and quantitative initializer substitution are separate. -/
namespace Paper.GeneralCoveringInitializedRandomIntegral
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Coins := GeneralCoveringTaskRandomPhysicalMarks.Coins
abbrev Input (V : Type) (B Δ k b n : ℕ) := GeneralCoveringInitializerRun.Input V × (Fin (B + 1) × Coins Δ k b n)
abbrev Saved (V : Type) (B Δ k b n : ℕ) := GeneralCoveringRequests.Output × Input V B Δ k b n
abbrev Output (V : Type) (B Δ k b n : ℕ) := GeneralCoveringRandomIntegralPhysical.Output V B Δ k b n × Saved V B Δ k b n

def repairInput {B Δ k b n : ℕ} (out : GeneralCoveringRequests.Output) (s : Input V B Δ k b n) :
    GeneralCoveringRandomIntegralPhysical.Input V B Δ k b n :=
  (⟨out.selected, s.1.residual, s.1.candidates, s.1.targets⟩, s.2)

private def chain {I O J K C : Type} (P : Program V I O) (Q : Program V J K)
    (f : O → (I × C) → J) : Program V (I × C) (K × (O × (I × C))) :=
  .seq (.local (fun _ _ s => (s.1, s)))
    (.seq (ProgramMemory.carry P)
      (.seq (.local (fun _ _ z => (f z.1 z.2, z))) (ProgramMemory.carry Q)))

/-- Public natural parameters and ID codec precede graph/private data.
The original input contains no center, partition, field or task mask. -/
def program {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B Δ k b n) (Output V B Δ k b n) :=
  chain (GeneralCoveringInitializerRun.program ids j h f U)
    (GeneralCoveringRandomIntegralPhysical.program ids L Δ a k t b n B hB) repairInput

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem chain_run {I O J K C : Type} (P : Program V I O) (Q : Program V J K)
    (f : O → (I × C) → J) (s : V → I × C) :
    (chain P Q f).runEncoded G s = fun v =>
      (Q.runEncoded G (fun u => f (P.runEncoded G (fun w => (s w).1) u) (s u)) v,
        (P.runEncoded G (fun w => (s w).1) v, s v)) := by
  rw [Program.runEncoded_eq_run]
  change (ProgramMemory.carry Q).run G
    (fun v => (f (((ProgramMemory.carry P).run G (fun u => ((s u).1, s u)) v).1)
      (((ProgramMemory.carry P).run G (fun u => ((s u).1, s u)) v).2),
      (ProgramMemory.carry P).run G (fun u => ((s u).1, s u)) v)) = _
  rw [ProgramMemory.run G P, ProgramMemory.run G Q]
  simp only [Program.runEncoded_eq_run]

def initialState {bits : ℕ} (ids : BitCode V bits) (j h f U B Δ k b n : ℕ) (s : V → Input V B Δ k b n) :=
  (GeneralCoveringInitializerRun.program ids j h f U).runEncoded G (fun v => (s v).1)

def physicalInput {bits : ℕ} (ids : BitCode V bits) (j h f U B Δ k b n : ℕ) (s : V → Input V B Δ k b n) :=
  fun v => repairInput (initialState G ids j h f U B Δ k b n s v) (s v)

def centers {bits : ℕ} (ids : BitCode V bits) (j h f U B Δ k b n : ℕ) (s : V → Input V B Δ k b n) : Finset V :=
  GeneralCoveringInitializerRun.output G ids j h f U (fun v => (s v).1)

theorem run_program {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (program ids j h f U L Δ a k t b n B hB).runEncoded G s = fun v =>
      ((GeneralCoveringRandomIntegralPhysical.program ids L Δ a k t b n B hB).runEncoded G
        (physicalInput G ids j h f U B Δ k b n s) v, (initialState G ids j h f U B Δ k b n s v, s v)) :=
  chain_run G (GeneralCoveringInitializerRun.program ids j h f U)
    (GeneralCoveringRandomIntegralPhysical.program ids L Δ a k t b n B hB) repairInput s

theorem retained {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    ((program ids j h f U L Δ a k t b n B hB).runEncoded G s v).2 =
      (initialState G ids j h f U B Δ k b n s v, s v) := by rw [run_program]

theorem center_eq {bits : ℕ} (ids : BitCode V bits) (j h f U B Δ k b n : ℕ)
    (s : V → Input V B Δ k b n) (v : V) :
    (physicalInput G ids j h f U B Δ k b n s v).1.center = decide (v ∈ centers G ids j h f U B Δ k b n s) := by
  simp only [physicalInput, repairInput, initialState, centers, GeneralCoveringInitializerRun.output,
    Program.runEncoded_eq_run, Finset.mem_filter, Finset.mem_univ, true_and]
  cases he : ((GeneralCoveringInitializerRun.program ids j h f U).run G (fun u => (s u).1) v).selected <;> rfl

theorem input_retained {bits : ℕ} (ids : BitCode V bits) (j h f U B Δ k b n : ℕ)
    (s : V → Input V B Δ k b n) (v : V) :
    (physicalInput G ids j h f U B Δ k b n s v).1.demand = (s v).1.residual ∧
    (physicalInput G ids j h f U B Δ k b n s v).1.candidates = (s v).1.candidates ∧
    (physicalInput G ids j h f U B Δ k b n s v).1.targets = (s v).1.targets ∧
    (physicalInput G ids j h f U B Δ k b n s v).2 = (s v).2 := ⟨rfl, rfl, rfl, rfl⟩

/-- The actual downstream Env/Fields retain the original private lists/cost
and the very same own beta, not a reindexed draw on private Low. -/
theorem physical_private_retained {bits : ℕ} (ids : BitCode V bits)
    (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B) (s : V → Input V B Δ k b n) (v : V) :
    let out := (program ids j h f U L Δ a k t b n B hB).runEncoded G s v
    out.1.2.2.2.env.metadata.owned.input = (physicalInput G ids j h f U B Δ k b n s v).1 ∧
      out.1.2.2.2.fields.cost = (s v).2.1 ∧ out.1.2.2.2.coins = (s v).2.2 := by
  dsimp only
  rw [run_program]
  exact GeneralCoveringRandomIntegralPhysical.private_input_retained G ids L Δ a k t b n B hB
    (physicalInput G ids j h f U B Δ k b n s) v

theorem centers_coin_independent {bits : ℕ} (ids : BitCode V bits) (j h f U B Δ k b n : ℕ)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) (β γ : V → Coins Δ k b n) :
    centers G ids j h f U B Δ k b n (fun v => (input v, (c v, β v))) =
      centers G ids j h f U B Δ k b n (fun v => (input v, (c v, γ v))) := rfl

def output {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) : Finset V :=
  Finset.univ.filter (fun v => ((program ids j h f U L Δ a k t b n B hB).runEncoded G s v).1.1)

theorem output_eq {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    output G ids j h f U L Δ a k t b n B hB s = GeneralCoveringRandomIntegralPhysical.output G ids L Δ a k t b n B hB
      (physicalInput G ids j h f U B Δ k b n s) := by
  simp only [output, GeneralCoveringRandomIntegralPhysical.output, run_program]

/-- Interpretation of ORIGINAL private data only. No D, its cover property,
computed fields, partition, mark or desired output bound is supplied. -/
structure Original (B Δ k t b n : ℕ) (s : V → Input V B Δ k b n) where
  cover : V → Finset V
  targets : V → Finset V
  R : Finset V
  hk : 0 < k
  ht : 0 < t
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  local_rows : ∀ r ∈ R, cover r ⊆ closed G r
  nonempty_rows : ∀ r ∈ R, (cover r).Nonempty
  demand : ∀ v, (s v).1.residual = decide (v ∈ R)
  candidates : ∀ v, (s v).1.candidates = cover v
  inverse : ∀ v, (s v).1.targets = targets v

theorem initial_correct {bits j h f U B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hj : 1 ≤ j) (d : Original G B Δ k t b n s) :
    initialState G ids j h f U B Δ k b n s = fun v =>
      (⟨decide (v ∈ GeneralCoveringInitializerRun.selected d.cover j h f d.R U), false⟩ :
        GeneralCoveringRequests.Output) := by
  simp only [initialState, Program.runEncoded_eq_run]
  exact GeneralCoveringInitializerRun.correct G ids d.cover d.targets j h f U hj d.R
    d.incidence d.local_rows d.nonempty_rows (fun v => (s v).1) d.demand d.candidates d.inverse

theorem centers_selected {bits j h f U B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hj : 1 ≤ j) (d : Original G B Δ k t b n s) :
    centers G ids j h f U B Δ k b n s = GeneralCoveringInitializerRun.selected d.cover j h f d.R U :=
  GeneralCoveringInitializerRun.output_eq G ids d.cover d.targets j h f U hj d.R
    d.incidence d.local_rows d.nonempty_rows (fun v => (s v).1) d.demand d.candidates d.inverse

/-- Both center hypotheses are derived internally from the real Run.spec. -/
theorem centers_spec {bits j h f U B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hj : 1 ≤ j) (d : Original G B Δ k t b n s) :
    GeneralCoveringInitializerPass.Covers d.cover d.R (centers G ids j h f U B Δ k b n s) ∧
      centers G ids j h f U B Δ k b n s ⊆ CoveringSupport.admissible d.cover d.R := by
  have hi := GeneralCoveringInitializerRun.spec G ids d.cover d.targets j h f U hj d.R
    d.incidence d.local_rows d.nonempty_rows (fun v => (s v).1) d.demand d.candidates d.inverse
  exact ⟨hi.1, hi.2.1⟩

def original {bits j h f U B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (d : Original G B Δ k t b n s) :
    GeneralCoveringRandomIntegralPhysical.Original G B Δ k t b n (physicalInput G ids j h f U B Δ k b n s) where
  toOriginal := {
    cover := d.cover
    targets := d.targets
    D := centers G ids j h f U B Δ k b n s
    R := d.R
    incidence := d.incidence
    local_rows := d.local_rows
    center := center_eq G ids j h f U B Δ k b n s
    demand := d.demand
    candidates := d.candidates
    inverse := d.inverse }
  hk := d.hk
  ht := d.ht

noncomputable def boundary {bits j h f U L B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (d : Original G B Δ k t b n s) :=
  GeneralCoveringRandomIntegralPhysical.boundary G L
    (original (j := j) (h := h) (f := f) (U := U) G ids d)

/-- The charged boundary uses actual initialized centers and ORIGINAL beta. -/
theorem boundary_eq {bits j h f U L B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (d : Original G B Δ k t b n s) :
    boundary (j := j) (h := h) (f := f) (U := U) (L := L) G ids d =
      GeneralCoveringRandomBoundaryBound.boundary G d.cover (centers G ids j h f U B Δ k b n s)
        d.R L Δ k d.hk t b n (fun v => (s v).2.2) := rfl

theorem covers {bits j h f U L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hj : 1 ≤ j) (hB : 1 ≤ B) (d : Original G B Δ k t b n s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    output G ids j h f U L Δ a k t b n B hB s ⊆ CoveringSupport.admissible d.cover d.R ∧
      GeneralCoveringNormalizedIntegral.Covers d.cover d.R (output G ids j h f U L Δ a k t b n B hB s) := by
  have hi := centers_spec (j := j) (h := h) (f := f) (U := U) G ids hj d
  rw [output_eq]
  exact GeneralCoveringRandomIntegralPhysical.covers G ids hB
    (original (j := j) (h := h) (f := f) (U := U) G ids d) hi.1 hi.2 ha hden hc

theorem cost {bits j h f U L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hj : 1 ≤ j) (hB : 1 ≤ B) (d : Original G B Δ k t b n s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val)
    (W : Finset V) (hWadm : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) :
    (∑ v ∈ output G ids j h f U L Δ a k t b n B hB s, (s v).2.1.val) ≤ (∑ v ∈ W, (s v).2.1.val) +
      B * (GeneralCoveringOwnerSupport.heavy G d.cover (centers G ids j h f U B Δ k b n s) d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover (centers G ids j h f U B Δ k b n s) d.R L Δ).card +
        (boundary (j := j) (h := h) (f := f) (U := U) (L := L) G ids d).card) := by
  have hi := centers_spec (j := j) (h := h) (f := f) (U := U) G ids hj d
  rw [output_eq]
  exact GeneralCoveringRandomIntegralPhysical.cost G ids hB
    (original (j := j) (h := h) (f := f) (U := U) G ids d) hi.1 hi.2 ha hden hc W hWadm hW

theorem empty_demands {bits j h f U L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hj : 1 ≤ j) (hB : 1 ≤ B) (d : Original G B Δ k t b n s) (hR : d.R = ∅)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    output G ids j h f U L Δ a k t b n B hB s = ∅ := by
  have hi := centers_spec (j := j) (h := h) (f := f) (U := U) G ids hj d
  rw [output_eq]
  exact GeneralCoveringRandomIntegralPhysical.empty_demands G ids hB
    (original (j := j) (h := h) (f := f) (U := U) G ids d) hR hi.1 hi.2 ha hden hc

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ)
    (hB : 1 ≤ B) (s : V → Input V B Δ k b n) : output G ids j h f U L Δ a k t b n B hB s = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (fun v => isEmptyElim v)

theorem rounds_eq {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids j h f U L Δ a k t b n B hB).rounds = U * (5 + 2 * f) + 2 +
      (GeneralCoveringRandomIntegralPhysical.program ids L Δ a k t b n B hB).rounds := by
  simp only [program, chain, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringInitializerRun.rounds, Nat.zero_add]

theorem rounds {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids j h f U L Δ a k t b n B hB).rounds = U * (5 + 2 * f) + 2 +
      ((10 + 4 * (n * (3 * k + 1) + 1) + (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4)) + 2) := by
  rw [rounds_eq, GeneralCoveringRandomIntegralPhysical.rounds]

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids j h f U L Δ a k t b n B hB).maxBits =
      max (GeneralCoveringInitializerRun.program ids j h f U).maxBits
        (GeneralCoveringRandomIntegralPhysical.program ids L Δ a k t b n B hB).maxBits := by
  simp only [program, chain, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]

theorem message_bound {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids j h f U L Δ a k t b n B hB).maxBits ≤ max (max (bits + 1) (f * (bits + 1)))
      (GeneralCoveringRandomIntegralPhysical.program ids L Δ a k t b n B hB).maxBits := by
  rw [maxBits]
  exact max_le_max (GeneralCoveringInitializerRun.maxBits ids j h f U) (le_refl _)

theorem packet_bound {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids j h f U L Δ a k t b n B hB).maxBits ≤ max (max (bits + 1) (f * (bits + 1)))
      (max (max ((L + Δ + 3) *
        (bits + max (ActiveFiniteBitPartition.packetBound bits Δ k b n) (k * (bits + 1)) + 2))
        (max (bits + 2) (max 1 L * (bits + (GeneralCoveringTaskIntegral.program ids a B k hB).maxBits + 1)))) (bits + 1)) :=
  (message_bound ids j h f U L Δ a k t b n B hB).trans
    (max_le_max (le_refl _) (GeneralCoveringRandomIntegralPhysical.packet_bound ids L Δ a k t b n B hB))

def bitCoefficient (f L Δ a k b n B c : ℕ) : ℕ :=
  max (max (c + 1) (f * (c + 1))) (GeneralCoveringRandomIntegralPhysical.bitCoefficient L Δ a k b n B c)

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B c : ℕ) (hB : 1 ≤ B)
    (hids : bits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids j h f U L Δ a k t b n B hB).maxBits ≤
      bitCoefficient f L Δ a k b n B c * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := GeneralCoveringRandomIntegralPhysical.logarithmic_bits ids L Δ a k t b n B c hB hids
  have hi := (BroadcastModel.logarithmic_message_budget (Fintype.card V) bits c hids).1
  have hf : f * (bits + 1) ≤ (f * (c + 1)) * Nat.clog 2 (Fintype.card V + 2) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left f hi
  have hm := (message_bound ids j h f U L Δ a k t b n B hB).trans (max_le_max (max_le_max hi hf) hp)
  simpa only [bitCoefficient, Nat.mul_max_mul_right] using hm

theorem public_costs {bits : ℕ} (ids : BitCode V bits) (j h f U L Δ a k t b n B c p d M : ℕ) (hB : 1 ≤ B)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program ids j h f U L Δ a k t b n B hB).rounds = U * (5 + 2 * f) + 2 +
      ((10 + 4 * (n * (3 * k + 1) + 1) + (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4)) + 2) ∧
    (program ids j h f U L Δ a k t b n B hB).maxBits ≤
      bitCoefficient f L Δ a k b n B (DeterministicColorReductionIdentifiers.bitFactor c p d) *
        Nat.clog 2 (Fintype.card V + 2) :=
  ⟨rounds ids j h f U L Δ a k t b n B hB, logarithmic_bits ids j h f U L Δ a k t b n B _ hB
    (DeterministicColorReductionIdentifiers.public_length_bound (Fintype.card V) bits c p d M hbits hM)⟩

end Paper.GeneralCoveringInitializedRandomIntegral

#print axioms Paper.GeneralCoveringInitializedRandomIntegral.run_program
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.retained
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.center_eq
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.input_retained
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.physical_private_retained
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.centers_coin_independent
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.output_eq
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.initial_correct
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.centers_selected
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.centers_spec
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.original
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.boundary_eq
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.covers
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.cost
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.empty_demands
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.empty_physical
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.rounds_eq
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.rounds
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.maxBits
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.message_bound
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.packet_bound
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.logarithmic_bits
#print axioms Paper.GeneralCoveringInitializedRandomIntegral.public_costs
