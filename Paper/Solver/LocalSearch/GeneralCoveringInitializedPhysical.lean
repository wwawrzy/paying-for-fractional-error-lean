import Paper.Solver.LocalSearch.GeneralCoveringTaskPhysicalRepair

/-! One real initializer, with original private data retained, followed by
physical partition/task solving and repair. The center bit comes from the
initializer's selected output. Uniform epsilon parameters and substitution
of initializer/high/boundary cardinal bounds remain separate. -/
namespace Paper.GeneralCoveringInitializedPhysical
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringInitializerRun.Input V × Fin (B + 1)
abbrev Saved (V : Type) (B : ℕ) := GeneralCoveringRequests.Output × Input V B
abbrev Output (V : Type) (B : ℕ) := GeneralCoveringTaskPhysicalRepair.Output V B × Saved V B

def repairInput {B : ℕ} (out : GeneralCoveringRequests.Output) (s : Input V B) :
    GeneralCoveringTaskPhysicalRepair.Input V B :=
  (⟨out.selected, s.1.residual, s.1.candidates, s.1.targets⟩, s.2)

private def chain {I O J K C : Type} (P : Program V I O) (Q : Program V J K)
    (f : O → (I × C) → J) : Program V (I × C) (K × (O × (I × C))) :=
  .seq (.local (fun _ _ s => (s.1, s)))
    (.seq (ProgramMemory.carry P)
      (.seq (.local (fun _ _ z => (f z.1 z.2, z))) (ProgramMemory.carry Q)))

/-- All numeric parameters and the ID codec precede the physical graph.
Only original private residual/candidates/targets/cost are runtime inputs. -/
def program {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Output V B) :=
  chain (GeneralCoveringInitializerRun.program ids b h f U)
    (GeneralCoveringTaskPhysicalRepair.program ids L Δ a k t T B hB) repairInput

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

def initialState {bits : ℕ} (ids : BitCode V bits) (b h f U B : ℕ) (s : V → Input V B) :=
  (GeneralCoveringInitializerRun.program ids b h f U).runEncoded G (fun v => (s v).1)

def physicalInput {bits : ℕ} (ids : BitCode V bits) (b h f U B : ℕ) (s : V → Input V B) :=
  fun v => repairInput (initialState G ids b h f U B s v) (s v)

def centers {bits : ℕ} (ids : BitCode V bits) (b h f U B : ℕ) (s : V → Input V B) : Finset V :=
  GeneralCoveringInitializerRun.output G ids b h f U (fun v => (s v).1)

theorem run_program {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program ids b h f U L Δ a k t T B hB).runEncoded G s = fun v =>
      ((GeneralCoveringTaskPhysicalRepair.program ids L Δ a k t T B hB).runEncoded G
        (physicalInput G ids b h f U B s) v, (initialState G ids b h f U B s v, s v)) :=
  chain_run G (GeneralCoveringInitializerRun.program ids b h f U)
    (GeneralCoveringTaskPhysicalRepair.program ids L Δ a k t T B hB) repairInput s

theorem retained {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((program ids b h f U L Δ a k t T B hB).runEncoded G s v).2 =
      (initialState G ids b h f U B s v, s v) := by rw [run_program]

theorem center_eq {bits : ℕ} (ids : BitCode V bits) (b h f U B : ℕ) (s : V → Input V B) (v : V) :
    (physicalInput G ids b h f U B s v).1.center = decide (v ∈ centers G ids b h f U B s) := by
  simp only [physicalInput, repairInput, initialState, centers, GeneralCoveringInitializerRun.output,
    Program.runEncoded_eq_run, Finset.mem_filter, Finset.mem_univ, true_and]
  cases he : ((GeneralCoveringInitializerRun.program ids b h f U).run G (fun u => (s u).1) v).selected <;> rfl

theorem input_retained {bits : ℕ} (ids : BitCode V bits) (b h f U B : ℕ) (s : V → Input V B) (v : V) :
    (physicalInput G ids b h f U B s v).1.demand = (s v).1.residual ∧
    (physicalInput G ids b h f U B s v).1.candidates = (s v).1.candidates ∧
    (physicalInput G ids b h f U B s v).1.targets = (s v).1.targets ∧
    (physicalInput G ids b h f U B s v).2 = (s v).2 := ⟨rfl, rfl, rfl, rfl⟩

def output {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => ((program ids b h f U L Δ a k t T B hB).runEncoded G s v).1.1)

theorem output_eq {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    output G ids b h f U L Δ a k t T B hB s = GeneralCoveringTaskPhysicalRepair.output G ids L Δ a k t T B hB
      (physicalInput G ids b h f U B s) := by
  simp only [output, GeneralCoveringTaskPhysicalRepair.output, run_program]

/-- Proof-side interpretation of original private data. No center set,
owner, computed masks, partition or desired output bound occurs here. -/
structure Original (k t B : ℕ) (s : V → Input V B) where
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

theorem initial_correct {bits b h f U k t B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (hb : 1 ≤ b) (d : Original G k t B s) :
    initialState G ids b h f U B s = fun v =>
      (⟨decide (v ∈ GeneralCoveringInitializerRun.selected d.cover b h f d.R U), false⟩ :
        GeneralCoveringRequests.Output) := by
  simp only [initialState, Program.runEncoded_eq_run]
  exact GeneralCoveringInitializerRun.correct G ids d.cover d.targets b h f U hb d.R
    d.incidence d.local_rows d.nonempty_rows (fun v => (s v).1) d.demand d.candidates d.inverse

theorem centers_selected {bits b h f U k t B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (hb : 1 ≤ b) (d : Original G k t B s) :
    centers G ids b h f U B s = GeneralCoveringInitializerRun.selected d.cover b h f d.R U :=
  GeneralCoveringInitializerRun.output_eq G ids d.cover d.targets b h f U hb d.R
    d.incidence d.local_rows d.nonempty_rows (fun v => (s v).1) d.demand d.candidates d.inverse

/-- Derive both center hypotheses from the actual Run.spec, not a cover
oracle or a preselected center set. -/
theorem centers_spec {bits b h f U k t B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (hb : 1 ≤ b) (d : Original G k t B s) :
    GeneralCoveringInitializerPass.Covers d.cover d.R (centers G ids b h f U B s) ∧
      centers G ids b h f U B s ⊆ CoveringSupport.admissible d.cover d.R := by
  have hi := GeneralCoveringInitializerRun.spec G ids d.cover d.targets b h f U hb d.R
    d.incidence d.local_rows d.nonempty_rows (fun v => (s v).1) d.demand d.candidates d.inverse
  exact ⟨hi.1, hi.2.1⟩

def original {bits b h f U k t B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (d : Original G k t B s) :
    GeneralCoveringTaskPhysicalRepair.Original G k t B (physicalInput G ids b h f U B s) where
  cover := d.cover
  targets := d.targets
  D := centers G ids b h f U B s
  R := d.R
  hk := d.hk
  ht := d.ht
  incidence := d.incidence
  local_rows := d.local_rows
  center := center_eq G ids b h f U B s
  demand := d.demand
  candidates := d.candidates
  inverse := d.inverse

noncomputable def boundary {bits b h f U L Δ k t T B : ℕ} {s : V → Input V B}
    (ids : BitCode V bits) (d : Original G k t B s) :=
  GeneralCoveringTaskPhysicalRepair.boundary (L := L) (Δ := Δ) (T := T) G ids
    (original (b := b) (h := h) (f := f) (U := U) G ids d)

theorem covers {bits b h f U L Δ a k t T B : ℕ} {s : V → Input V B}
    (ids : BitCode V bits) (hb : 1 ≤ b) (hB : 1 ≤ B) (d : Original G k t B s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val) :
    output G ids b h f U L Δ a k t T B hB s ⊆ CoveringSupport.admissible d.cover d.R ∧
      GeneralCoveringNormalizedIntegral.Covers d.cover d.R (output G ids b h f U L Δ a k t T B hB s) := by
  have hi := centers_spec (b := b) (h := h) (f := f) (U := U) G ids hb d
  rw [output_eq]
  exact GeneralCoveringTaskPhysicalRepair.covers G ids hB
    (original (b := b) (h := h) (f := f) (U := U) G ids d) hi.1 hi.2 ha hden hc

theorem cost {bits b h f U L Δ a k t T B : ℕ} {s : V → Input V B}
    (ids : BitCode V bits) (hb : 1 ≤ b) (hB : 1 ≤ B) (d : Original G k t B s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val)
    (W : Finset V) (hWadm : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) :
    (∑ v ∈ output G ids b h f U L Δ a k t T B hB s, (s v).2.val) ≤ (∑ v ∈ W, (s v).2.val) +
      B * (GeneralCoveringOwnerSupport.heavy G d.cover (centers G ids b h f U B s) d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover (centers G ids b h f U B s) d.R L Δ).card +
        (boundary (b := b) (h := h) (f := f) (U := U) (L := L) (Δ := Δ) (T := T) G ids d).card) := by
  have hi := centers_spec (b := b) (h := h) (f := f) (U := U) G ids hb d
  rw [output_eq]
  exact GeneralCoveringTaskPhysicalRepair.cost G ids hB
    (original (b := b) (h := h) (f := f) (U := U) G ids d) hi.1 hi.2 ha hden hc W hWadm hW

theorem empty_demands {bits b h f U L Δ a k t T B : ℕ} {s : V → Input V B}
    (ids : BitCode V bits) (hb : 1 ≤ b) (hB : 1 ≤ B) (d : Original G k t B s) (hR : d.R = ∅)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val) :
    output G ids b h f U L Δ a k t T B hB s = ∅ := by
  have hi := centers_spec (b := b) (h := h) (f := f) (U := U) G ids hb d
  rw [output_eq]
  exact GeneralCoveringTaskPhysicalRepair.empty_demands G ids hB
    (original (b := b) (h := h) (f := f) (U := U) G ids d) hR hi.1 hi.2 ha hden hc

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ)
    (hB : 1 ≤ B) (s : V → Input V B) : output G ids b h f U L Δ a k t T B hB s = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (fun v => isEmptyElim v)

theorem rounds {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids b h f U L Δ a k t T B hB).rounds = U * (5 + 2 * f) + 2 +
      (GeneralCoveringTaskPhysicalRepair.program ids L Δ a k t T B hB).rounds := by
  simp only [program, chain, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringInitializerRun.rounds, Nat.zero_add]

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids b h f U L Δ a k t T B hB).maxBits =
      max (GeneralCoveringInitializerRun.program ids b h f U).maxBits
        (GeneralCoveringTaskPhysicalRepair.program ids L Δ a k t T B hB).maxBits := by
  simp only [program, chain, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]

theorem message_bound {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids b h f U L Δ a k t T B hB).maxBits ≤
      max (max (bits + 1) (f * (bits + 1)))
        (GeneralCoveringTaskPhysicalRepair.program ids L Δ a k t T B hB).maxBits := by
  rw [maxBits]
  exact max_le_max (GeneralCoveringInitializerRun.maxBits ids b h f U) (le_refl _)

def roundCoefficient (h f U L Δ a k T B c p d : ℕ) :=
  U * (5 + 2 * f) + 2 + GeneralCoveringTaskPhysicalRepair.roundCoefficient L Δ a k T B c p d

def bitCoefficient (f L Δ a k B c p d : ℕ) :=
  max (max (DeterministicColorReductionIdentifiers.bitFactor c p d + 1)
    (f * (DeterministicColorReductionIdentifiers.bitFactor c p d + 1)))
    (GeneralCoveringTaskPhysicalRepair.bitCoefficient L Δ a k B c p d)

theorem costs {bits : ℕ} (ids : BitCode V bits) (b h f U L Δ a k t T B c p d M : ℕ) (hB : 1 ≤ B)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program ids b h f U L Δ a k t T B hB).rounds ≤ roundCoefficient h f U L Δ a k T B c p d *
      (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
    (program ids b h f U L Δ a k t T B hB).maxBits ≤
      bitCoefficient f L Δ a k B c p d * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := GeneralCoveringTaskPhysicalRepair.costs ids L Δ a k t T B c p d M hB hbits hM
  have hi := DeterministicColorReductionIdentifiers.public_length_bound (Fintype.card V) bits c p d M hbits hM
  have hb := (BroadcastModel.logarithmic_message_budget (Fintype.card V) bits
    (DeterministicColorReductionIdentifiers.bitFactor c p d) hi).1
  constructor
  · rw [rounds]
    unfold roundCoefficient
    let A := U * (5 + 2 * f) + 2
    let q := 1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)
    have hq : 1 ≤ q := by dsimp only [q]; omega
    have hA : A ≤ A * q := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left A hq
    calc
      _ ≤ A * q + GeneralCoveringTaskPhysicalRepair.roundCoefficient L Δ a k T B c p d * q :=
        Nat.add_le_add hA hp.1
      _ = (A + GeneralCoveringTaskPhysicalRepair.roundCoefficient L Δ a k T B c p d) * q :=
        (Nat.add_mul A _ q).symm
  · have hf : f * (bits + 1) ≤
        (f * (DeterministicColorReductionIdentifiers.bitFactor c p d + 1)) * Nat.clog 2 (Fintype.card V + 2) := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left f hb
    have hm := max_le_max hb hf
    have hh := (message_bound ids b h f U L Δ a k t T B hB).trans (max_le_max hm hp.2)
    simpa only [bitCoefficient, Nat.mul_max_mul_right] using hh

end Paper.GeneralCoveringInitializedPhysical

#print axioms Paper.GeneralCoveringInitializedPhysical.run_program
#print axioms Paper.GeneralCoveringInitializedPhysical.retained
#print axioms Paper.GeneralCoveringInitializedPhysical.center_eq
#print axioms Paper.GeneralCoveringInitializedPhysical.input_retained
#print axioms Paper.GeneralCoveringInitializedPhysical.output_eq
#print axioms Paper.GeneralCoveringInitializedPhysical.initial_correct
#print axioms Paper.GeneralCoveringInitializedPhysical.centers_selected
#print axioms Paper.GeneralCoveringInitializedPhysical.centers_spec
#print axioms Paper.GeneralCoveringInitializedPhysical.covers
#print axioms Paper.GeneralCoveringInitializedPhysical.cost
#print axioms Paper.GeneralCoveringInitializedPhysical.empty_demands
#print axioms Paper.GeneralCoveringInitializedPhysical.empty_physical
#print axioms Paper.GeneralCoveringInitializedPhysical.rounds
#print axioms Paper.GeneralCoveringInitializedPhysical.maxBits
#print axioms Paper.GeneralCoveringInitializedPhysical.message_bound
#print axioms Paper.GeneralCoveringInitializedPhysical.costs
