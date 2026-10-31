import Paper.Solver.LocalSearch.GeneralCoveringTaskRandomPhysicalMarks
import Paper.Solver.LocalSearch.GeneralCoveringTaskFractionalRepair

/-! One actual random physical producer, then ONLY the fractional repair core.
The whole producer output (including own coins/private Env) is retained.
The equality with the native Repair program is a proof-reuse statement only:
no second preparation occurs in this program. Every outcome is covered;
expectation, initializer discharge and averaging remain separate. -/
namespace Paper.GeneralCoveringRandomFractionalPhysical
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B Δ k b n : ℕ) := GeneralCoveringTaskRandomPhysicalMarks.Input V B Δ k b n
abbrev Produced (V : Type) (B Δ k b n : ℕ) := GeneralCoveringTaskRandomPhysicalMarks.Output V B Δ k b n
abbrev Output (V : Type) (B Δ k b n : ℕ) := GeneralCoveringTaskFractionalRepair.Output V B × Produced V B Δ k b n

/-- Local projection with the complete producer output saved privately. -/
def project (B Δ k b n : ℕ) : Program V (Produced V B Δ k b n)
    (GeneralCoveringTaskFractionalRepair.Input V B × Produced V B Δ k b n) :=
  .local (fun _ _ s => ((s.env, s.fields), s))

/-- Literal public program: producer ONCE, local projection, repair CORE. -/
def program {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B Δ k b n) (Output V B Δ k b n) :=
  .seq (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
    (.seq (project B Δ k b n)
      (ProgramMemory.carry (X := Produced V B Δ k b n) (GeneralCoveringTaskFractionalRepair.core ids L a B k q hB)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem compose_run {In S Mid Out : Type} (P : Program V In S) (Q : Program V Mid Out)
    (f : S → Mid) (s : V → In) :
    (Program.seq P (Program.seq (Program.local (fun _ _ x => (f x, x))) (ProgramMemory.carry Q))).runEncoded G s =
      fun v => (Q.runEncoded G (fun u => f (P.runEncoded G s u)) v, P.runEncoded G s v) := by
  rw [Program.runEncoded_eq_run]
  change (ProgramMemory.carry Q).run G (fun v => (f (P.run G s v), P.run G s v)) = _
  rw [ProgramMemory.run G Q]
  simp only [Program.runEncoded_eq_run]

private theorem input_eta {B Δ k b n : ℕ} (s : V → Input V B Δ k b n) :
    (fun v => ((s v).1, ((s v).2.1, (s v).2.2))) = s := by
  funext v
  rfl

private theorem run_input_eta {B Δ k b n : ℕ} {Out : Type}
    (P : Program V (Input V B Δ k b n) Out) (s : V → Input V B Δ k b n) :
    P.runEncoded G (fun v => ((s v).1, ((s v).2.1, (s v).2.2))) = P.runEncoded G s :=
  congrArg (P.runEncoded G) (input_eta s)

private theorem run_property {In Out : Type} (P : Program V In Out)
    (s t : V → In) (he : s = t) (v : V) (property : Out → Prop)
    (hs : property (P.runEncoded G s v)) : property (P.runEncoded G t v) := by
  cases he
  exact hs

def produced {bits : ℕ} (ids : BitCode V bits) (L Δ k t b n B : ℕ) (s : V → Input V B Δ k b n) :=
  (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B).runEncoded G s

/-- Counterfactual native input ONLY for proof reuse, never runtime input. -/
def nativeInput {bits : ℕ} (ids : BitCode V bits) (L Δ k t b n B : ℕ) (s : V → Input V B Δ k b n) :
    V → GeneralCoveringTaskFractionalRepair.NativeInput V B :=
  fun v => ((s v).1, (produced G ids L Δ k t b n B s v).fields)

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (program ids L Δ a B k q t b n hB).runEncoded G s = fun v =>
      ((GeneralCoveringTaskFractionalRepair.core ids L a B k q hB).runEncoded G
        (fun u => ((produced G ids L Δ k t b n B s u).env, (produced G ids L Δ k t b n B s u).fields)) v,
        produced G ids L Δ k t b n B s v) :=
  compose_run G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
    (GeneralCoveringTaskFractionalRepair.core ids L a B k q hB) (fun x => (x.env, x.fields)) s

theorem producer_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    ((program ids L Δ a B k q t b n hB).runEncoded G s v).2 = produced G ids L Δ k t b n B s v := by
  rw [run_program]

theorem native_cost {bits : ℕ} (ids : BitCode V bits) (L Δ k t b n B : ℕ)
    (s : V → Input V B Δ k b n) (v : V) :
    (nativeInput G ids L Δ k t b n B s v).2.cost = (s v).2.1 := by
  change (produced G ids L Δ k t b n B s v).fields.cost = (s v).2.1
  have h := GeneralCoveringTaskRandomPhysicalMarks.cost_retained G ids L Δ k t b n B
    (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v
  delta produced
  exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
    (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) v
    (fun z : Produced V B Δ k b n => z.fields.cost = (s v).2.1) h

/-- Metadata preparation depends only on original private fields, not on
client Fields or coins. This equality does NOT execute another preparation. -/
theorem prepared_env {bits : ℕ} (ids : BitCode V bits) (L Δ k t b n B : ℕ)
    (s : V → Input V B Δ k b n) (v : V) :
    (produced G ids L Δ k t b n B s v).env =
      GeneralCoveringTaskFractionalRepair.env G ids L Δ (nativeInput G ids L Δ k t b n B s) v :=
  GeneralCoveringTaskRandomPhysicalMarks.env_retained G ids L Δ k t b n B
    (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v

private theorem native_core {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringTaskFractionalRepair.NativeInput V B) :
    (GeneralCoveringTaskFractionalRepair.program ids L Δ a B k q hB).runEncoded G s =
      (GeneralCoveringTaskFractionalRepair.core ids L a B k q hB).runEncoded G
        (fun v => (GeneralCoveringTaskFractionalRepair.env G ids L Δ s v, (s v).2)) := by
  change (GeneralCoveringTaskFractionalRepair.core ids L a B k q hB).runEncoded G
    ((ProgramMemory.carry (GeneralCoveringOwnerVirtualPrepare.program ids L Δ)).runEncoded G
      (fun v => ((s v).1, (s v).2))) = _
  simp only [Program.runEncoded_eq_run]
  rw [ProgramMemory.run]
  simp only [GeneralCoveringTaskFractionalRepair.env, Program.runEncoded_eq_run]

/-- Full encoded equality with accepted native Repair for proof reuse only.
Its generated Fields are the actual producer's Fields on original input. -/
theorem native_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (program ids L Δ a B k q t b n hB).runEncoded G s = fun v =>
      ((GeneralCoveringTaskFractionalRepair.program ids L Δ a B k q hB).runEncoded G
        (nativeInput G ids L Δ k t b n B s) v, produced G ids L Δ k t b n B s v) := by
  have hin : (fun v => ((produced G ids L Δ k t b n B s v).env, (produced G ids L Δ k t b n B s v).fields)) =
      fun v => (GeneralCoveringTaskFractionalRepair.env G ids L Δ (nativeInput G ids L Δ k t b n B s) v,
        (nativeInput G ids L Δ k t b n B s v).2) :=
    funext (fun v => Prod.ext (prepared_env G ids L Δ k t b n B s v) rfl)
  rw [run_program, hin, ← native_core G ids L Δ a B k q hB (nativeInput G ids L Δ k t b n B s)]

theorem memory_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    let out := (program ids L Δ a B k q t b n hB).runEncoded G s v
    out.1.2.2.2.1 = out.2.fields ∧ out.1.2.2.2.2 = out.2.env ∧
    out.2.coins = (s v).2.2 ∧ out.2.fields.cost = (s v).2.1 ∧
    out.2.env.metadata.owned.input = (s v).1 := by
  dsimp only
  rw [native_eq]
  refine ⟨GeneralCoveringTaskFractionalRepair.fields_retained G ids L Δ a B k q hB _ v, ?_,
    GeneralCoveringTaskRandomPhysicalMarks.coins_retained G ids L Δ k t b n B
      (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v,
    native_cost G ids L Δ k t b n B s v,
    GeneralCoveringTaskRandomPhysicalMarks.private_input_retained G ids L Δ k t b n B
      (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v⟩
  exact (GeneralCoveringTaskFractionalRepair.env_retained G ids L Δ a B k q hB _ v).trans
    (prepared_env G ids L Δ k t b n B s v).symm

theorem output_bound {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    ((program ids L Δ a B k q t b n hB).runEncoded G s v).1.1 ≤
      max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + q := by
  rw [native_eq]
  exact GeneralCoveringTaskFractionalRepair.output_bound G ids L Δ a B k q hB _ v

theorem common_denominator {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (s : V → Input V B Δ k b n) (v : V) :
    (q : ℝ) * ((((program ids L Δ a B k q t b n hB).runEncoded G s v).1.1 : ℝ) / q) =
      ((program ids L Δ a B k q t b n hB).runEncoded G s v).1.1 := by
  have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  field_simp [hqn]

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Derive ALL repair interpretation/part/interior fields from the actual
random producer. The only supplied interpretation describes original input. -/
noncomputable def original {bits : ℕ} (ids : BitCode V bits) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (s : V → Input V B Δ k b n)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1)) :
    GeneralCoveringTaskFractionalRepair.Original G L Δ k B (nativeInput G ids L Δ k t b n B s) := by
  have hs := GeneralCoveringTaskRandomPhysicalMarks.fields_spec G ids L Δ k hk t ht b n B
    (fun v => (s v).1) d (fun v => (s v).2.1) (fun v => (s v).2.2)
  refine {
    cover := d.cover
    targets := d.targets
    D := d.D
    R := d.R
    incidence := d.incidence
    local_rows := d.local_rows
    center := d.center
    demand := d.demand
    candidates := d.candidates
    inverse := d.inverse
    P := GeneralCoveringTaskRandomPhysicalMarks.partition G d.cover d.D d.R L hk t (fun v => (s v).2.2)
    low_role := ?_
    excluded_role := ?_
    interior := ?_ }
  · intro U hU i hi
    have hrole := (hs.2.1 U hU i hi).2
    change (produced G ids L Δ k t b n B s i.val.val).fields.role = _
    delta produced
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) i.val.val
      (fun z : Produced V B Δ k b n => z.fields.role = some (GeneralCoveringTaskRoles.name d.D
        (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) U
        ((GeneralCoveringTaskRandomPhysicalMarks.partition G d.cover d.D d.R L hk t (fun v => (s v).2.2)).nonempty U hU))) hrole
  · intro i hi
    have hexcluded := hs.2.2.1 i hi
    change (produced G ids L Δ k t b n B s i.val).fields.role = none
    delta produced
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) i.val
      (fun z : Produced V B Δ k b n => z.fields.role = none) hexcluded
  · intro i
    have hinterior := hs.2.2.2.1 i
    change (produced G ids L Δ k t b n B s i.val.val).fields.interior = _
    delta produced
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) i.val.val
      (fun z : Produced V B Δ k b n => z.fields.interior = decide (i ∉ BoundaryOwners.vertices
        (graph G d.cover d.D d.R L (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
        Finset.univ (GeneralCoveringTaskRandomPhysicalMarks.partition G d.cover d.D d.R L hk t (fun v => (s v).2.2)).parts)) hinterior

/-- Exactly the SAME actual pulled random boundary used by repair. -/
noncomputable def boundary {Δ k b n : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hk : 0 < k) (t : ℕ) (β : V → GeneralCoveringTaskRandomPhysicalMarks.Coins Δ k b n) :=
  BoundaryOwners.vertices (graph G C D R L (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) Finset.univ
    (GeneralCoveringTaskRandomPhysicalMarks.partition G C D R L hk t β).parts

theorem original_boundary {bits : ℕ} (ids : BitCode V bits) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (s : V → Input V B Δ k b n)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1)) :
    GeneralCoveringTaskFractionalRepair.boundary G (original G ids L Δ k hk t ht b n B s d) =
      boundary G d.cover d.D d.R L hk t (fun v => (s v).2.2) := rfl

private theorem native_positive {bits : ℕ} (ids : BitCode V bits) (L Δ k t b n B : ℕ)
    (s : V → Input V B Δ k b n) (C : V → Finset V) (R : Finset V)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ (s v).2.1.val) :
    ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ (nativeInput G ids L Δ k t b n B s v).2.cost.val := by
  intro v hv
  rw [native_cost]
  exact hc v hv

theorem support {bits L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1))
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    ∀ v, v ∉ CoveringSupport.admissible d.cover d.R →
      ((program ids L Δ a B k q t b n hB).runEncoded G s v).1.1 = 0 := by
  rw [native_eq]
  exact GeneralCoveringTaskFractionalRepair.support G ids hB hq (original G ids L Δ k hk t ht b n B s d)
    hcover hadm ha hden ξ haccuracy (native_positive G ids L Δ k t b n B s d.cover d.R hc)

theorem feasible {bits L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1))
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    CoveringOptimum.Feasible d.cover d.R
      (fun v => (((program ids L Δ a B k q t b n hB).runEncoded G s v).1.1 : ℝ) / q) := by
  rw [native_eq]
  exact GeneralCoveringTaskFractionalRepair.feasible G ids hB hq (original G ids L Δ k hk t ht b n B s d)
    hcover hadm ha hden ξ haccuracy (native_positive G ids L Δ k t b n B s d.cover d.R hc)

theorem cost {bits L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1))
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    CoveringOptimum.objective (fun v => ((s v).2.1.val : ℝ))
      (fun v => (((program ids L Δ a B k q t b n hB).runEncoded G s v).1.1 : ℝ) / q) ≤
      (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.1.val : ℝ)) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card +
        (boundary G d.cover d.D d.R L hk t (fun v => (s v).2.2)).card) := by
  have hs := GeneralCoveringTaskFractionalRepair.cost G ids hB hq (original G ids L Δ k hk t ht b n B s d)
    hcover hadm ha hden ξ haccuracy (native_positive G ids L Δ k t b n B s d.cover d.R hc)
  have he : (fun v => ((nativeInput G ids L Δ k t b n B s v).2.cost.val : ℝ)) =
      (fun v => ((s v).2.1.val : ℝ)) := by
    funext v
    exact congrArg (fun z : Fin (B + 1) => (z.val : ℝ)) (native_cost G ids L Δ k t b n B s v)
  rw [he] at hs
  rw [native_eq]
  exact hs

/-- Every public coin assignment satisfies full original-R supported
fractional feasibility and the actual additive random-boundary cost bound.
D-cover/admissibility are explicit intermediate premises. Expected boundary
and initializer discharge remain separate. -/
theorem spec {bits L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1))
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    let out := (program ids L Δ a B k q t b n hB).runEncoded G s
    let x := fun v => ((out v).1.1 : ℝ) / q
    SevenFoundation.feasible (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2.1)) x ∧
    CoveringOptimum.objective (fun v => ((s v).2.1.val : ℝ)) x ≤
      (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.1.val : ℝ)) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card +
        (boundary G d.cover d.D d.R L hk t (fun v => (s v).2.2)).card) ∧
    (∀ v, (out v).1.1 ≤ max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + q) ∧
    (∀ v, (q : ℝ) * x v = (out v).1.1) ∧
    (∀ v, (out v).2 = produced G ids L Δ k t b n B s v) := by
  dsimp only
  have hs := support G ids (L := L) hB hk ht hq s d hcover hadm ha hden ξ haccuracy hc
  refine ⟨GeneralCoveringFractionalCorrect.instance_feasible d.R d.cover (fun v => (s v).2.1) _
    (feasible G ids hB hk ht hq s d hcover hadm ha hden ξ haccuracy hc) ?_,
    cost G ids hB hk ht hq s d hcover hadm ha hden ξ haccuracy hc,
    output_bound G ids L Δ a B k q t b n hB s,
    common_denominator G ids L Δ a B k q t b n hB hq s,
    producer_retained G ids L Δ a B k q t b n hB s⟩
  intro v hv
  rw [hs v hv]
  simp only [Nat.cast_zero, zero_div]

theorem empty_demands {bits L Δ a B k q t b n : ℕ} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hk : 0 < k) (ht : 0 < t) (hq : 1 ≤ q) (s : V → Input V B Δ k b n)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1)) (he : d.R = ∅)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    ∀ v, ((program ids L Δ a B k q t b n hB).runEncoded G s v).1.1 = 0 := by
  intro v
  exact support G ids hB hk ht hq s d hcover hadm ha hden ξ haccuracy hc v (by simp [he, CoveringSupport.admissible])

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (program ids L Δ a B k q t b n hB).runEncoded G s = fun v => isEmptyElim v := by
  funext v
  exact isEmptyElim v

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a B k q t b n hB).rounds =
      RecursiveSearch.roundBound (4 * k) a (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) +
        4 * (n * (3 * k + 1) + 1) + 16 := by
  simp only [program, project, Program.rounds, ProgramMemory.rounds, GeneralCoveringTaskRandomPhysicalMarks.rounds,
    GeneralCoveringTaskFractionalRepair.core_rounds]
  omega

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a B k q t b n hB).maxBits =
      max (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B).maxBits
        (max (GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB).maxBits (bits + 1)) := by
  simp only [program, project, Program.maxBits, ProgramMemory.maxBits, GeneralCoveringTaskFractionalRepair.core_maxBits,
    Nat.zero_max]

/-- Graph-independent coefficient for logarithmic physical messages. -/
def bitCoefficient (L Δ a B k q b n c : ℕ) : ℕ :=
  max (GeneralCoveringTaskRandomPhysicalMarks.bitCoefficient L Δ k b n c)
    (max (max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B q
      (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 1) + 1))) (c + 1))

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q t b n : ℕ) (hB : 1 ≤ B)
    (c : ℕ) (hids : bits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids L Δ a B k q t b n hB).maxBits ≤
      bitCoefficient L Δ a B k q b n c * Nat.clog 2 (Fintype.card V + 2) := by
  let K0 := max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B q
    (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 1) + 1))
  let K := bitCoefficient L Δ a B k q b n c
  have hp := GeneralCoveringTaskRandomPhysicalMarks.logarithmic_bits ids L Δ k t b n B c hids
  have hg := (GeneralCoveringTaskFractionalAggregate.logarithmic_bits ids L a B k q hB (Fintype.card V) c hids).1
  have hl : 1 ≤ Nat.clog 2 (Fintype.card V + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : bits + 1 ≤ (c + 1) * Nat.clog 2 (Fintype.card V + 2) := by nlinarith
  have hP : GeneralCoveringTaskRandomPhysicalMarks.bitCoefficient L Δ k b n c ≤ K := le_max_left _ _
  have hG : K0 ≤ K := (le_max_left K0 (c + 1)).trans (le_max_right _ _)
  have hD : c + 1 ≤ K := (le_max_right K0 (c + 1)).trans (le_max_right _ _)
  rw [maxBits_eq]
  exact max_le (hp.trans (Nat.mul_le_mul_right _ hP))
    (max_le (hg.trans (Nat.mul_le_mul_right _ hG)) (hb.trans (Nat.mul_le_mul_right _ hD)))

end Paper.GeneralCoveringRandomFractionalPhysical

#print axioms Paper.GeneralCoveringRandomFractionalPhysical.run_program
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.producer_retained
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.native_cost
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.prepared_env
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.native_eq
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.memory_retained
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.output_bound
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.common_denominator
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.original
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.original_boundary
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.support
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.feasible
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.cost
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.spec
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.empty_demands
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.empty_physical
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.rounds
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.maxBits_eq
#print axioms Paper.GeneralCoveringRandomFractionalPhysical.logarithmic_bits
