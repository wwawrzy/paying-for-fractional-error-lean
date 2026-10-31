import Paper.Solver.LocalSearch.GeneralCoveringRandomFractionalPhysical
import Paper.Solver.LocalSearch.GeneralCoveringInitializerSupported

/-! Actual initializer ONCE, then actual pointwise random fractional program
ONCE. Original incidence/residual/cost/own coins are private saved memory.
Selected initializer bits become centers locally. No supplied center/cover,
partition, mask or optimum is a runtime input. Expectation and averaging are
separate gates. Public numeric parameters precede the physical graph. -/
namespace Paper.GeneralCoveringInitializedRandomFractional
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B Δ k b n : ℕ) := GeneralCoveringInitializerRun.Input V × GeneralCoveringTaskRandomPhysicalMarks.Saved B Δ k b n
abbrev Output (V : Type) (B Δ k b n : ℕ) := GeneralCoveringRandomFractionalPhysical.Output V B Δ k b n × Input V B Δ k b n

def seed {B Δ k b n : ℕ} (out : GeneralCoveringRequests.Output) (s : Input V B Δ k b n) :
    GeneralCoveringRandomFractionalPhysical.Input V B Δ k b n :=
  (GeneralCoveringOwners.initializerInput out s.1, s.2)

def start (B Δ k b n : ℕ) : Program V (Input V B Δ k b n)
    (GeneralCoveringInitializerRun.Input V × Input V B Δ k b n) :=
  .local (fun _ _ s => (s.1, s))

def prepare (B Δ k b n : ℕ) : Program V (GeneralCoveringRequests.Output × Input V B Δ k b n)
    (GeneralCoveringRandomFractionalPhysical.Input V B Δ k b n × Input V B Δ k b n) :=
  .local (fun _ _ s => (seed s.1 s.2, s.2))

/-- Literal native execution. ib/ih/ifreq/it are the public Run parameters. -/
def program {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B Δ k b n) (Output V B Δ k b n) :=
  .seq (start B Δ k b n)
    (.seq (ProgramMemory.carry (X := Input V B Δ k b n) (GeneralCoveringInitializerRun.program ids ib ih ifreq it))
      (.seq (prepare B Δ k b n)
        (ProgramMemory.carry (X := Input V B Δ k b n)
          (GeneralCoveringRandomFractionalPhysical.program ids L Δ a B k q t b n hB))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem compose_run {In S Saved Mid Out : Type} (P : Program V In S) (Q : Program V Mid Out)
    (first : Saved → In) (next : S → Saved → Mid) (s : V → Saved) :
    (Program.seq (Program.local (fun _ _ x => (first x, x)))
      (Program.seq (ProgramMemory.carry P)
        (Program.seq (Program.local (fun _ _ x => (next x.1 x.2, x.2))) (ProgramMemory.carry Q)))).runEncoded G s =
      fun v => (Q.runEncoded G (fun u => next (P.runEncoded G (fun w => first (s w)) u) (s u)) v, s v) := by
  rw [Program.runEncoded_eq_run]
  change (ProgramMemory.carry Q).run G ((Program.local (fun _ _ x => (next x.1 x.2, x.2))).run G
    ((ProgramMemory.carry P).run G (fun v => (first (s v), s v)))) = _
  rw [ProgramMemory.run G P]
  change (ProgramMemory.carry Q).run G (fun v => (next (P.run G (fun w => first (s w)) v) (s v), s v)) = _
  rw [ProgramMemory.run G Q]
  simp only [Program.runEncoded_eq_run]

def initialResult {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) :=
  (GeneralCoveringInitializerRun.program ids ib ih ifreq it).runEncoded G (fun v => (s v).1)

def randomInput {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) :
    V → GeneralCoveringRandomFractionalPhysical.Input V B Δ k b n :=
  fun v => seed (initialResult G ids ib ih ifreq it s v) (s v)

/-- Exact encoded selected-bit set, not a supplied mathematical center set. -/
def centers {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) : Finset V :=
  GeneralCoveringInitializerSupported.output G ids ib ih ifreq it (fun v => (s v).1)

theorem run_program {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s = fun v =>
      ((GeneralCoveringRandomFractionalPhysical.program ids L Δ a B k q t b n hB).runEncoded G
        (randomInput G ids ib ih ifreq it s) v, s v) := by
  delta program start prepare randomInput initialResult
  exact compose_run G (GeneralCoveringInitializerRun.program ids ib ih ifreq it)
    (GeneralCoveringRandomFractionalPhysical.program ids L Δ a B k q t b n hB) Prod.fst seed s

theorem input_retained {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    ((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).2 = s v := by
  rw [run_program]

theorem random_private {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) (v : V) :
    (randomInput G ids ib ih ifreq it s v).1.demand = (s v).1.residual ∧
    (randomInput G ids ib ih ifreq it s v).1.candidates = (s v).1.candidates ∧
    (randomInput G ids ib ih ifreq it s v).1.targets = (s v).1.targets ∧
    (randomInput G ids ib ih ifreq it s v).2 = (s v).2 := by
  delta randomInput seed GeneralCoveringOwners.initializerInput
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem bool_filter (f : V → Bool) (v : V) :
    f v = decide (v ∈ Finset.univ.filter (fun u => f u = true)) := by
  cases he : f v <;> simp [he]

theorem center_bit {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) (v : V) :
    (randomInput G ids ib ih ifreq it s v).1.center = decide (v ∈ centers G ids ib ih ifreq it s) := by
  delta randomInput seed initialResult centers GeneralCoveringInitializerSupported.output GeneralCoveringOwners.initializerInput
  exact bool_filter (fun u => ((GeneralCoveringInitializerRun.program ids ib ih ifreq it).runEncoded G (fun w => (s w).1) u).selected) v

theorem cost_function {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) :
    (fun v => ((randomInput G ids ib ih ifreq it s v).2.1.val : ℝ)) = (fun v => ((s v).2.1.val : ℝ)) := by
  funext v
  exact congrArg (fun z : GeneralCoveringTaskRandomPhysicalMarks.Saved B Δ k b n => (z.1.val : ℝ))
    (random_private G ids ib ih ifreq it s v).2.2.2

theorem coins_function {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) :
    (fun v => (randomInput G ids ib ih ifreq it s v).2.2) = (fun v => (s v).2.2) := by
  funext v
  exact congrArg Prod.snd (random_private G ids ib ih ifreq it s v).2.2.2

/-- Retain original input AND the actual producer's own coins/cost/private
seeded input, not merely a separate copy of the initial coin vector. -/
theorem memory_retained {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    let out := (program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v
    out.2 = s v ∧ out.1.2.coins = (s v).2.2 ∧ out.1.2.fields.cost = (s v).2.1 ∧
    out.1.2.env.metadata.owned.input = (randomInput G ids ib ih ifreq it s v).1 := by
  dsimp only
  rw [run_program]
  have hm := GeneralCoveringRandomFractionalPhysical.memory_retained G ids L Δ a B k q t b n hB
    (randomInput G ids ib ih ifreq it s) v
  have hp := (random_private G ids ib ih ifreq it s v).2.2.2
  exact ⟨rfl, hm.2.2.1.trans (congrArg Prod.snd hp), hm.2.2.2.1.trans (congrArg Prod.fst hp), hm.2.2.2.2⟩

/-- Interpretation of original private data ONLY. No D or center premise. -/
structure Original {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) where
  cover : V → Finset V
  targets : V → Finset V
  R : Finset V
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  local_rows : ∀ r ∈ R, cover r ⊆ closed G r
  rows : ∀ r ∈ R, (cover r).Nonempty
  residual : ∀ r, (s r).1.residual = decide (r ∈ R)
  candidates : ∀ r, (s r).1.candidates = cover r
  inverse : ∀ v, (s v).1.targets = targets v

noncomputable def original {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} {s : V → Input V B Δ k b n} (d : Original G s) :
    GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (randomInput G ids ib ih ifreq it s v).1) where
  cover := d.cover
  targets := d.targets
  D := centers G ids ib ih ifreq it s
  R := d.R
  incidence := d.incidence
  local_rows := d.local_rows
  center := center_bit G ids ib ih ifreq it s
  demand v := ((random_private G ids ib ih ifreq it s v).1).trans (d.residual v)
  candidates v := ((random_private G ids ib ih ifreq it s v).2.1).trans (d.candidates v)
  inverse v := ((random_private G ids ib ih ifreq it s v).2.2.1).trans (d.inverse v)

theorem initializer_spec {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ) (hib : 1 ≤ ib)
    {B Δ k b n : ℕ} {s : V → Input V B Δ k b n} (d : Original G s) :
    GeneralCoveringInitializerPass.Covers d.cover d.R (centers G ids ib ih ifreq it s) ∧
    centers G ids ib ih ifreq it s ⊆ CoveringSupport.admissible d.cover d.R := by
  have hs := GeneralCoveringInitializerRun.spec G ids d.cover d.targets ib ih ifreq it hib d.R
    d.incidence d.local_rows d.rows (fun v => (s v).1) d.residual d.candidates d.inverse
  delta centers
  simp only [GeneralCoveringInitializerSupported.output_eq]
  exact ⟨hs.1, hs.2.1⟩

/-- Optional quantitative specialization to the accepted public initializer
choices. The runtime remains the literal Run program above. -/
theorem uniform_bounds {bits : ℕ} (ids : BitCode V bits) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hden : MinorDensity.Bound G ρ) {B Δ k b n : ℕ} {s : V → Input V B Δ k b n} (d : Original G s)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    let D := centers G ids (GeneralCoveringInitializerFractional.listBound ρ)
      (GeneralCoveringInitializerFractional.candidateThreshold ρ) (GeneralCoveringInitializerFractional.listThreshold ρ)
      (GeneralCoveringInitializerFractional.scale ρ) s
    (D.card : ℝ) ≤ GeneralCoveringInitializerFractional.uniformCoefficient ρ *
      GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.1.val : ℝ)) ∧
    (∑ v ∈ D, ((s v).2.1.val : ℝ)) ≤ (B : ℝ) * GeneralCoveringInitializerFractional.uniformCoefficient ρ *
      GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.1.val : ℝ)) := by
  have hs := GeneralCoveringInitializerSupported.uniform_fin_spec G ids d.cover d.targets hρ hden B d.R
    d.local_rows d.rows d.incidence (fun v => (s v).2.1) hc (fun v => (s v).1) d.residual d.candidates d.inverse
  delta centers
  exact ⟨hs.2.2.1, hs.2.2.2⟩

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def boundary {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) {B b n : ℕ} {s : V → Input V B Δ k b n} (d : Original G s) :=
  GeneralCoveringRandomFractionalPhysical.boundary G d.cover (centers G ids ib ih ifreq it s) d.R L hk t (fun v => (s v).2.2)

private theorem native_positive {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it : ℕ)
    {B Δ k b n : ℕ} {s : V → Input V B Δ k b n} (d : Original G s)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (randomInput G ids ib ih ifreq it s v).2.1.val := by
  intro v hv
  have h := congrArg (fun z : GeneralCoveringTaskRandomPhysicalMarks.Saved B Δ k b n => z.1.val)
    (random_private G ids ib ih ifreq it s v).2.2.2
  change (randomInput G ids ib ih ifreq it s v).2.1.val = (s v).2.1.val at h
  exact h.symm ▸ hc v hv

theorem output_bound {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    ((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).1.1.1 ≤
      max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + q := by
  rw [run_program]
  exact GeneralCoveringRandomFractionalPhysical.output_bound G ids L Δ a B k q t b n hB
    (randomInput G ids ib ih ifreq it s) v

theorem common_denominator {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (s : V → Input V B Δ k b n) (v : V) :
    (q : ℝ) * ((((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).1.1.1 : ℝ) / q) =
      ((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).1.1.1 := by
  rw [run_program]
  exact GeneralCoveringRandomFractionalPhysical.common_denominator G ids L Δ a B k q t b n hB hq
    (randomInput G ids ib ih ifreq it s) v

theorem support {bits ib ih ifreq it L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hib : 1 ≤ ib) (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n) (d : Original G s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    ∀ v, v ∉ CoveringSupport.admissible d.cover d.R →
      ((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).1.1.1 = 0 := by
  have hi := initializer_spec G ids ib ih ifreq it hib d
  rw [run_program]
  exact GeneralCoveringRandomFractionalPhysical.support G ids (L := L) hB hk ht hq
    (randomInput G ids ib ih ifreq it s) (original G ids ib ih ifreq it d)
    hi.1 hi.2 ha hden ξ haccuracy (native_positive G ids ib ih ifreq it d hc)

theorem feasible {bits ib ih ifreq it L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hib : 1 ≤ ib) (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n) (d : Original G s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    CoveringOptimum.Feasible d.cover d.R
      (fun v => (((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).1.1.1 : ℝ) / q) := by
  have hi := initializer_spec G ids ib ih ifreq it hib d
  rw [run_program]
  exact GeneralCoveringRandomFractionalPhysical.feasible G ids (L := L) hB hk ht hq
    (randomInput G ids ib ih ifreq it s) (original G ids ib ih ifreq it d)
    hi.1 hi.2 ha hden ξ haccuracy (native_positive G ids ib ih ifreq it d hc)

theorem cost {bits ib ih ifreq it L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hib : 1 ≤ ib) (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n) (d : Original G s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    CoveringOptimum.objective (fun v => ((s v).2.1.val : ℝ))
      (fun v => (((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).1.1.1 : ℝ) / q) ≤
      (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.1.val : ℝ)) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover (centers G ids ib ih ifreq it s) d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover (centers G ids ib ih ifreq it s) d.R L Δ).card +
        (boundary G ids ib ih ifreq it L Δ k hk t d).card) := by
  have hi := initializer_spec G ids ib ih ifreq it hib d
  have hs := GeneralCoveringRandomFractionalPhysical.cost G ids (L := L) hB hk ht hq
    (randomInput G ids ib ih ifreq it s) (original G ids ib ih ifreq it d)
    hi.1 hi.2 ha hden ξ haccuracy (native_positive G ids ib ih ifreq it d hc)
  rw [cost_function G ids ib ih ifreq it s, coins_function G ids ib ih ifreq it s] at hs
  rw [run_program]
  exact hs

/-- Full initialized pointwise guarantee, with NO supplied D/cover/center
hypothesis. Only the interpretation of original private fields remains. -/
theorem spec {bits ib ih ifreq it L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hib : 1 ≤ ib) (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n) (d : Original G s)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    let out := (program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s
    let x := fun v => ((out v).1.1.1 : ℝ) / q
    SevenFoundation.feasible (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2.1)) x ∧
    CoveringOptimum.objective (fun v => ((s v).2.1.val : ℝ)) x ≤
      (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.1.val : ℝ)) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover (centers G ids ib ih ifreq it s) d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover (centers G ids ib ih ifreq it s) d.R L Δ).card +
        (boundary G ids ib ih ifreq it L Δ k hk t d).card) ∧
    (∀ v, (out v).1.1.1 ≤ max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + q) ∧
    (∀ v, (q : ℝ) * x v = (out v).1.1.1) ∧ (∀ v, (out v).2 = s v) := by
  dsimp only
  have hs := support G ids (ib := ib) (ih := ih) (ifreq := ifreq) (it := it) (L := L)
    hB hib hk ht hq s d ha hden ξ haccuracy hc
  refine ⟨GeneralCoveringFractionalCorrect.instance_feasible d.R d.cover (fun v => (s v).2.1) _
    (feasible G ids hB hib hk ht hq s d ha hden ξ haccuracy hc) ?_,
    cost G ids hB hib hk ht hq s d ha hden ξ haccuracy hc,
    output_bound G ids ib ih ifreq it L Δ a B k q t b n hB s,
    common_denominator G ids ib ih ifreq it L Δ a B k q t b n hB hq s,
    input_retained G ids ib ih ifreq it L Δ a B k q t b n hB s⟩
  intro v hv
  rw [hs v hv]
  simp only [Nat.cast_zero, zero_div]

theorem empty_demands {bits ib ih ifreq it L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hib : 1 ≤ ib) (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n) (d : Original G s)
    (he : d.R = ∅) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    ∀ v, ((program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s v).1.1.1 = 0 := by
  intro v
  exact support G ids hB hib hk ht hq s d ha hden ξ haccuracy hc v (by simp [he, CoveringSupport.admissible])

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (program ids ib ih ifreq it L Δ a B k q t b n hB).runEncoded G s = fun v => isEmptyElim v := by
  funext v
  exact isEmptyElim v

theorem rounds_eq {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B) :
    (program ids ib ih ifreq it L Δ a B k q t b n hB).rounds =
      (GeneralCoveringInitializerRun.program ids ib ih ifreq it).rounds +
        (GeneralCoveringRandomFractionalPhysical.program ids L Δ a B k q t b n hB).rounds := by
  simp only [program, start, prepare, Program.rounds, ProgramMemory.rounds, Nat.zero_add]

theorem rounds {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B) :
    (program ids ib ih ifreq it L Δ a B k q t b n hB).rounds =
      RecursiveSearch.roundBound (4 * k) a (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) +
        4 * (n * (3 * k + 1) + 1) + it * (5 + 2 * ifreq) + 18 := by
  rw [rounds_eq, GeneralCoveringInitializerRun.rounds, GeneralCoveringRandomFractionalPhysical.rounds]
  omega

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B) :
    (program ids ib ih ifreq it L Δ a B k q t b n hB).maxBits =
      max (GeneralCoveringInitializerRun.program ids ib ih ifreq it).maxBits
        (GeneralCoveringRandomFractionalPhysical.program ids L Δ a B k q t b n hB).maxBits := by
  simp only [program, start, prepare, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max]

def bitCoefficient (ifreq L Δ a B k q b n c : ℕ) : ℕ :=
  max (max 1 ifreq * (c + 1)) (GeneralCoveringRandomFractionalPhysical.bitCoefficient L Δ a B k q b n c)

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (ib ih ifreq it L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (c : ℕ) (hids : bits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids ib ih ifreq it L Δ a B k q t b n hB).maxBits ≤
      bitCoefficient ifreq L Δ a B k q b n c * Nat.clog 2 (Fintype.card V + 2) := by
  let H := Nat.clog 2 (Fintype.card V + 2)
  let K := bitCoefficient ifreq L Δ a B k q b n c
  have hlog : 1 ≤ H := Nat.clog_pos (by omega) (by omega)
  have hidsH : bits ≤ c * H := hids
  have hb : bits + 1 ≤ (c + 1) * H := by nlinarith [hidsH]
  have hm : max (bits + 1) (ifreq * (bits + 1)) ≤ max 1 ifreq * (bits + 1) :=
    max_le (by simpa only [one_mul] using Nat.mul_le_mul_right (bits + 1) (le_max_left 1 ifreq))
      (Nat.mul_le_mul_right (bits + 1) (le_max_right 1 ifreq))
  have hi := (GeneralCoveringInitializerRun.maxBits ids ib ih ifreq it).trans hm
  have hi' : (GeneralCoveringInitializerRun.program ids ib ih ifreq it).maxBits ≤ (max 1 ifreq * (c + 1)) * H := by
    exact hi.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (max 1 ifreq) hb)
  have hr := GeneralCoveringRandomFractionalPhysical.logarithmic_bits ids L Δ a B k q t b n hB c hids
  have hI : max 1 ifreq * (c + 1) ≤ K := le_max_left _ _
  have hR : GeneralCoveringRandomFractionalPhysical.bitCoefficient L Δ a B k q b n c ≤ K := le_max_right _ _
  rw [maxBits_eq]
  exact max_le (hi'.trans (Nat.mul_le_mul_right H hI)) (hr.trans (Nat.mul_le_mul_right H hR))

end Paper.GeneralCoveringInitializedRandomFractional

#print axioms Paper.GeneralCoveringInitializedRandomFractional.run_program
#print axioms Paper.GeneralCoveringInitializedRandomFractional.input_retained
#print axioms Paper.GeneralCoveringInitializedRandomFractional.random_private
#print axioms Paper.GeneralCoveringInitializedRandomFractional.center_bit
#print axioms Paper.GeneralCoveringInitializedRandomFractional.cost_function
#print axioms Paper.GeneralCoveringInitializedRandomFractional.coins_function
#print axioms Paper.GeneralCoveringInitializedRandomFractional.memory_retained
#print axioms Paper.GeneralCoveringInitializedRandomFractional.original
#print axioms Paper.GeneralCoveringInitializedRandomFractional.initializer_spec
#print axioms Paper.GeneralCoveringInitializedRandomFractional.uniform_bounds
#print axioms Paper.GeneralCoveringInitializedRandomFractional.output_bound
#print axioms Paper.GeneralCoveringInitializedRandomFractional.common_denominator
#print axioms Paper.GeneralCoveringInitializedRandomFractional.support
#print axioms Paper.GeneralCoveringInitializedRandomFractional.feasible
#print axioms Paper.GeneralCoveringInitializedRandomFractional.cost
#print axioms Paper.GeneralCoveringInitializedRandomFractional.spec
#print axioms Paper.GeneralCoveringInitializedRandomFractional.empty_demands
#print axioms Paper.GeneralCoveringInitializedRandomFractional.empty_physical
#print axioms Paper.GeneralCoveringInitializedRandomFractional.rounds_eq
#print axioms Paper.GeneralCoveringInitializedRandomFractional.rounds
#print axioms Paper.GeneralCoveringInitializedRandomFractional.maxBits_eq
#print axioms Paper.GeneralCoveringInitializedRandomFractional.logarithmic_bits
