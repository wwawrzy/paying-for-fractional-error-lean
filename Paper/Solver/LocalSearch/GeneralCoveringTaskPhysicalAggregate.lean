import Paper.Solver.LocalSearch.GeneralCoveringTaskPhysicalMarks
import Paper.Solver.LocalSearch.GeneralCoveringTaskAggregate

/-! Physical marks once, then the actual task aggregate CORE on physical G.
Its metadata/fields input is a local projection of the received state. Full
Env and Fields survive privately for later repair; no support/preparation is
repeated. Initializer cover/admissibility remain explicit proof premises.
No small eta cut, unrepaired original-R coverage or full A/D is asserted. -/
namespace Paper.GeneralCoveringTaskPhysicalAggregate
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringTaskPhysicalMarks.Input V B
abbrev Saved (V : Type) (B : ℕ) := GeneralCoveringTaskPhysicalMarks.Output V B
abbrev Output (V : Type) (B : ℕ) := Bool × Saved V B

def inputOf {B : ℕ} (s : Saved V B) : GeneralCoveringTaskAggregate.Input V B := (s.2.metadata, s.1)

def attach (B : ℕ) : Program V (Saved V B) (GeneralCoveringTaskAggregate.Input V B × Saved V B) :=
  .local (fun _ _ s => (inputOf s, s))

def program {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Output V B) :=
  .seq (GeneralCoveringTaskPhysicalMarks.program ids L Δ k t T B)
    (.seq (attach B) (ProgramMemory.carry (X := Saved V B) (GeneralCoveringTaskAggregate.program ids L a B k hB)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Opaque-program composition avoids elaborating the whole translated client. -/
private theorem compose_run {In S Mid Out : Type} (P : Program V In S) (Q : Program V Mid Out)
    (f : S → Mid) (s : V → In) :
    (Program.seq P (Program.seq (Program.local (fun _ _ x => (f x, x))) (ProgramMemory.carry Q))).runEncoded G s =
      fun v => (Q.runEncoded G (fun u => f (P.runEncoded G s u)) v, P.runEncoded G s v) := by
  rw [Program.runEncoded_eq_run]
  change (ProgramMemory.carry Q).run G (fun v => (f (P.run G s v), P.run G s v)) = _
  rw [ProgramMemory.run G Q]
  simp only [Program.runEncoded_eq_run]

def state {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ) (s : V → Input V B) : V → Saved V B :=
  (GeneralCoveringTaskPhysicalMarks.program ids L Δ k t T B).runEncoded G s

def clientState {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ) (s : V → Input V B) :
    V → GeneralCoveringTaskAggregate.Input V B := fun v => inputOf (state G ids L Δ k t T B s v)

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    (program ids L Δ a k t T B hB).runEncoded G s = fun v =>
      ((GeneralCoveringTaskAggregate.program ids L a B k hB).runEncoded G (clientState G ids L Δ k t T B s) v,
        state G ids L Δ k t T B s v) :=
  compose_run G (GeneralCoveringTaskPhysicalMarks.program ids L Δ k t T B)
    (GeneralCoveringTaskAggregate.program ids L a B k hB) inputOf s

theorem state_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((program ids L Δ a k t T B hB).runEncoded G s v).2 = state G ids L Δ k t T B s v := by
  rw [run_program]

theorem env_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (v : V) :
    ((program ids L Δ a k t T B hB).runEncoded G (fun u => (input u, c u)) v).2.2 =
      GeneralCoveringOwnerSimulation.learned G ids L Δ input v :=
  (congrArg Prod.snd (state_retained G ids L Δ a k t T B hB _ v)).trans
    (GeneralCoveringTaskPhysicalMarks.env_retained G ids L Δ k t T B input c v)

theorem private_input_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (v : V) :
    ((program ids L Δ a k t T B hB).runEncoded G (fun u => (input u, c u)) v).2.2.metadata.owned.input = input v :=
  (congrArg (fun s : Saved V B => s.2.metadata.owned.input)
    (state_retained G ids L Δ a k t T B hB _ v)).trans
    (GeneralCoveringTaskPhysicalMarks.private_input_retained G ids L Δ k t T B input c v)

def output {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => ((program ids L Δ a k t T B hB).runEncoded G s v).1)

theorem output_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    output G ids L Δ a k t T B hB s =
      GeneralCoveringTaskAggregate.output G ids L a B k hB (clientState G ids L Δ k t T B s) := by
  exact congrArg (fun out : V → Output V B => Finset.univ.filter (fun v => (out v).1))
    (run_program G ids L Δ a k t T B hB s)

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G cover D R L).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance lowAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G cover D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Derived geometry of the actual received client state, with no oracle fields. -/
noncomputable def geometry {bits : ℕ} (ids : BitCode V bits) (L Δ k t T B : ℕ) (hk : 0 < k) (ht' : 0 < t)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) :
    GeneralCoveringTaskRoles.Geometry G L B (clientState G ids L Δ k t T B (fun v => (input v, c v))) := by
  have hf := GeneralCoveringTaskPhysicalMarks.fields_spec G ids L Δ k t T B hk ht'
    cover targets D R hinc hlocal input c hD hR hC ht
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids cover targets D R L Δ hinc hlocal input hD hR hC ht
  have hm (v : V) : (state G ids L Δ k t T B (fun u => (input u, c u)) v).2.metadata =
      GeneralCoveringOwnerDiscoveryCorrect.metadata G cover D R L input v :=
    (congrArg GeneralCoveringOwnerVirtualPrepare.Env.metadata
      (GeneralCoveringTaskPhysicalMarks.env_retained G ids L Δ k t T B input c v)).trans (hs.1 v)
  exact {
    cover := cover
    targets := targets
    D := D
    R := R
    Q := GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ
    k := k
    P := GeneralCoveringTaskPhysicalMarks.partition G ids cover D R L Δ k t T hk ht'
    Bdy := BoundaryOwners.vertices (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))
      Finset.univ (GeneralCoveringTaskPhysicalMarks.partition G ids cover D R L Δ k t T hk ht').parts
    local_rows := hlocal
    owner := fun v => congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.owner) (hm v)
    admissible := fun v => congrArg GeneralCoveringOwnerSupport.State.admissible (hm v)
    heavy := fun v => congrArg GeneralCoveringOwnerSupport.State.heavy (hm v)
    residual := fun v => congrArg GeneralCoveringOwnerSupport.State.residual (hm v)
    candidates := fun v => (congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.input.candidates) (hm v)).trans (hC v)
    inverse := fun v => (congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.input.targets) (hm v)).trans (ht v)
    incidence := hinc
    low_role := hf.2.1
    excluded_role := hf.2.2.1
    interior := hf.2.2.2.1 }

/-- Native support/coverage/cost for the actual task union. D's original cover
and admissibility are explicit intermediate premises, not an initialized endpoint. -/
theorem spec {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (hk : 0 < k) (ht' : 0 < t)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D) (hadm : D ⊆ CoveringSupport.admissible cover R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v)
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val) :
    let Q := GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ
    let P := GeneralCoveringTaskPhysicalMarks.partition G ids cover D R L Δ k t T hk ht'
    let Bdy := BoundaryOwners.vertices (graph G cover D R L Q) Finset.univ P.parts
    let O := output G ids L Δ a k t T B hB (fun v => (input v, c v))
    O ⊆ P.parts.biUnion (fun I => service G cover D R L Q I Bdy) ∧
      O ⊆ CoveringSupport.admissible cover R ∧
      GeneralCoveringNormalizedIntegral.Covers cover (P.parts.biUnion (fun I => demands G cover D R L Q I Bdy)) O ∧
      ∀ W : Finset V, W ⊆ CoveringSupport.admissible cover R →
        GeneralCoveringNormalizedIntegral.Covers cover R W → (∑ v ∈ O, (c v).val) ≤ ∑ v ∈ W, (c v).val := by
  dsimp only
  rw [output_eq]
  let cs := clientState G ids L Δ k t T B (fun v => (input v, c v))
  let g := geometry G ids L Δ k t T B hk ht' cover targets D R hinc hlocal input c hD hR hC ht
  have hcost : ∀ v, (cs v).2.cost = c v :=
    (GeneralCoveringTaskPhysicalMarks.fields_spec G ids L Δ k t T B hk ht'
      cover targets D R hinc hlocal input c hD hR hC ht).1
  have hpositive : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (cs v).2.cost.val := by
    intro v hv
    rw [hcost v]
    exact hc v hv
  have hs := GeneralCoveringTaskAggregate.aggregate_spec G ids g hcover hadm a ha hden hB hpositive rfl
  have hsum (U : Finset V) : (∑ v ∈ U, (cs v).2.cost.val) = ∑ v ∈ U, (c v).val := by
    apply Finset.sum_congr rfl
    intro v _
    exact congrArg Fin.val (hcost v)
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
  intro W _hWadm hW
  calc
    _ = ∑ v ∈ GeneralCoveringTaskAggregate.output G ids L a B k hB cs, (cs v).2.cost.val := (hsum _).symm
    _ ≤ ∑ v ∈ W, (cs v).2.cost.val := (hs.2.2.2 W hW).2
    _ = ∑ v ∈ W, (c v).val := hsum W

/-- Even after solving, full computed Fields and the learned Env remain available. -/
theorem fields_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((program ids L Δ a k t T B hB).runEncoded G s v).2.1 = (state G ids L Δ k t T B s v).1 :=
  congrArg Prod.fst (state_retained G ids L Δ a k t T B hB s v)

theorem empty_low {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (hk : 0 < k) (ht' : 0 < t)
    (cover targets : V → Finset V) (D R : Finset V)
    [IsEmpty (Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))]
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) :
    output G ids L Δ a k t T B hB (fun v => (input v, c v)) = ∅ ∧
      ∀ v, ((program ids L Δ a k t T B hB).runEncoded G (fun u => (input u, c u)) v).1 = false := by
  let g := geometry G ids L Δ k t T B hk ht' cover targets D R hinc hlocal input c hD hR hC ht
  have he : g.P.parts = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro U hU
    obtain ⟨i, _⟩ := g.P.nonempty U hU
    exact isEmptyElim (show Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ) from i)
  have hs := GeneralCoveringTaskAggregate.empty_parts G ids g he a hB
  constructor
  · rw [output_eq]
    exact hs.1
  · intro v
    rw [run_program]
    exact hs.2 v

theorem empty_centers {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (hk : 0 < k) (ht' : 0 < t)
    (cover targets : V → Finset V) (D R : Finset V) (hEmpty : D = ∅)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1))
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = cover v) (ht : ∀ v, (input v).targets = targets v) :
    output G ids L Δ a k t T B hB (fun v => (input v, c v)) = ∅ ∧
      ∀ v, ((program ids L Δ a k t T B hB).runEncoded G (fun u => (input u, c u)) v).1 = false := by
  letI : IsEmpty (Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)) := ⟨fun i =>
    Finset.notMem_empty i.val.val
      ((congrArg (fun S : Finset V => (i.val.val : V) ∈ S) hEmpty).mp i.val.property)⟩
  exact empty_low G ids L Δ a k t T B hB hk ht' cover targets D R hinc hlocal input c hD hR hC ht

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) : output G ids L Δ a k t T B hB s = ∅ ∧
      ∀ v, ((program ids L Δ a k t T B hB).runEncoded G s v).1 = false := by
  exact ⟨Finset.eq_empty_iff_forall_notMem.mpr (fun v => isEmptyElim v), fun v => isEmptyElim v⟩

theorem rounds_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t T B hB).rounds = (GeneralCoveringTaskPhysicalMarks.program ids L Δ k t T B).rounds +
      (GeneralCoveringTaskAggregate.program ids L a B k hB).rounds := by
  simp only [program, attach, Program.rounds, ProgramMemory.rounds, Nat.zero_add]

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t T B hB).rounds =
      (10 + 4 * (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B).rounds) +
        (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4) := by
  rw [rounds_eq, GeneralCoveringTaskPhysicalMarks.rounds, GeneralCoveringTaskAggregate.rounds]

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t T B hB).maxBits = max (GeneralCoveringTaskPhysicalMarks.program ids L Δ k t T B).maxBits
      (GeneralCoveringTaskAggregate.program ids L a B k hB).maxBits := by
  simp only [program, attach, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t T B hB).maxBits ≤
      max ((L + Δ + 3) * (bits + (GeneralCoveringTaskPartitionMarks.program ids Δ k t T B).maxBits + 2))
        (max (bits + 2) (max 1 L * (bits + (GeneralCoveringTaskIntegral.program ids a B k hB).maxBits + 1))) := by
  rw [maxBits_eq]
  apply max_le_max (GeneralCoveringTaskPhysicalMarks.maxBits ids L Δ k t T B)
  rw [GeneralCoveringTaskAggregate.maxBits_eq]
  exact GeneralCoveringTaskParallel.maxBits ids L a B k hB

def roundCoefficient (L Δ a k T B c p d : ℕ) : ℕ :=
  GeneralCoveringTaskPhysicalMarks.roundCoefficient L Δ k T c p d + RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4

def aggregateBitCoefficient (L a k B c p d : ℕ) : ℕ :=
  let f := DeterministicColorReductionIdentifiers.bitFactor c p d
  max (f + 2) (max 1 L * (f + (3 * f + RecursiveSearch.extraBits (4 * k) a B 1 (2 * B * k) + 1) + 1))

def bitCoefficient (L Δ a k B c p d : ℕ) : ℕ :=
  max (GeneralCoveringTaskPhysicalMarks.bitCoefficient L Δ k c p d) (aggregateBitCoefficient L a k B c p d)

theorem costs {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B c p d M : ℕ) (hB : 1 ≤ B)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program ids L Δ a k t T B hB).rounds ≤ roundCoefficient L Δ a k T B c p d *
      (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
    (program ids L Δ a k t T B hB).maxBits ≤ bitCoefficient L Δ a k B c p d * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := GeneralCoveringTaskPhysicalMarks.costs ids L Δ k t T B c p d M hbits hM
  have hi := DeterministicColorReductionIdentifiers.public_length_bound (Fintype.card V) bits c p d M hbits hM
  have ha := (GeneralCoveringTaskAggregate.logarithmic_bits ids L a B k hB (Fintype.card V)
    (DeterministicColorReductionIdentifiers.bitFactor c p d) hi).1
  constructor
  · rw [rounds_eq, GeneralCoveringTaskAggregate.rounds]
    unfold roundCoefficient
    nlinarith [hp.1]
  · rw [maxBits_eq]
    have hm := max_le_max hp.2 ha
    simpa only [bitCoefficient, aggregateBitCoefficient, Nat.mul_max_mul_right] using hm

end Paper.GeneralCoveringTaskPhysicalAggregate

#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.run_program
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.state_retained
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.env_retained
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.private_input_retained
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.output_eq
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.geometry
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.spec
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.fields_retained
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.empty_low
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.empty_centers
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.empty_physical
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.rounds_eq
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.rounds
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.maxBits_eq
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.maxBits
#print axioms Paper.GeneralCoveringTaskPhysicalAggregate.costs
