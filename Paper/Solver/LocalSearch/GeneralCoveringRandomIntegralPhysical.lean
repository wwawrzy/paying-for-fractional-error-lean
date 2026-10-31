import Paper.Solver.LocalSearch.GeneralCoveringRandomBoundaryBound
import Paper.Solver.LocalSearch.GeneralCoveringTaskPhysicalRepair

/-! Native random marks once, the physical task aggregate CORE, then the
two-round optional-partner repair CORE. The whole producer state and its
original public-vertex coins survive privately. Correctness and additive
cost hold for each outcome; initialization and expected approximation are
separate gates. No partition, metadata or task mask is executable input. -/
namespace Paper.GeneralCoveringRandomIntegralPhysical
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B Δ k b n : ℕ) := GeneralCoveringTaskRandomPhysicalMarks.Input V B Δ k b n
abbrev Saved (V : Type) (B Δ k b n : ℕ) := GeneralCoveringTaskRandomPhysicalMarks.Output V B Δ k b n
abbrev Before (V : Type) (B Δ k b n : ℕ) := Bool × Saved V B Δ k b n
abbrev Output (V : Type) (B Δ k b n : ℕ) := Bool × (GeneralCoveringOwnerRepair.Output V × Before V B Δ k b n)

def inputOf {B Δ k b n : ℕ} (s : Saved V B Δ k b n) : GeneralCoveringTaskAggregate.Input V B :=
  (s.env.metadata, s.fields)

def attach (B Δ k b n : ℕ) :
    Program V (Saved V B Δ k b n) (GeneralCoveringTaskAggregate.Input V B × Saved V B Δ k b n) :=
  .local (fun _ _ s => (inputOf s, s))

def aggregate {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B Δ k b n) (Before V B Δ k b n) :=
  .seq (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
    (.seq (attach B Δ k b n)
      (ProgramMemory.carry (X := Saved V B Δ k b n) (GeneralCoveringTaskAggregate.program ids L a B k hB)))

def mark {B Δ k b n : ℕ} (s : Before V B Δ k b n) : Bool :=
  s.2.env.metadata.owned.input.center && (s.2.env.high || (s.2.env.low && !s.2.fields.interior))

def repairInput {B Δ k b n : ℕ} (s : Before V B Δ k b n) : GeneralCoveringOwnerRepair.Input V :=
  ⟨s.2.env, mark s⟩

def prepare (B Δ k b n : ℕ) :
    Program V (Before V B Δ k b n) (GeneralCoveringOwnerRepair.Input V × Before V B Δ k b n) :=
  .local (fun _ _ s => (repairInput s, s))

def finish (B Δ k b n : ℕ) :
    Program V (GeneralCoveringOwnerRepair.Output V × Before V B Δ k b n) (Output V B Δ k b n) :=
  .local (fun _ _ s => (s.2.1 || s.1.selected, (s.1, s.2)))

/-- Both downstream clients use their cores. The native producer occurs once. -/
def program {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B Δ k b n) (Output V B Δ k b n) :=
  .seq (aggregate ids L Δ a k t b n B hB)
    (.seq (prepare B Δ k b n)
      (.seq (ProgramMemory.carry (X := Before V B Δ k b n) (GeneralCoveringOwnerRepair.core ids))
        (finish B Δ k b n)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Only original private semantics and positive public k,t. -/
structure Original (B Δ k t b n : ℕ) (s : V → Input V B Δ k b n)
    extends GeneralCoveringTaskRandomPhysicalMarks.Original G (fun v => (s v).1) where
  hk : 0 < k
  ht : 0 < t

private theorem compose_run {In S Mid Out Final : Type} (P : Program V In S) (Q : Program V Mid Out)
    (f : S → Mid) (h : Out → S → Final) (s : V → In) :
    (Program.seq P (Program.seq (Program.local (fun _ _ x => (f x, x)))
      (Program.seq (ProgramMemory.carry Q) (Program.local (fun _ _ x => h x.1 x.2))))).runEncoded G s =
      fun v => h (Q.runEncoded G (fun u => f (P.runEncoded G s u)) v) (P.runEncoded G s v) := by
  rw [Program.runEncoded_eq_run]
  change (Program.local (fun _ _ x => h x.1 x.2)).run G
    ((ProgramMemory.carry Q).run G (fun v => (f (P.run G s v), P.run G s v))) = _
  rw [ProgramMemory.run G Q]
  change (fun v => h (Q.run G (fun u => f (P.run G s u)) v) (P.run G s v)) = _
  simp only [Program.runEncoded_eq_run]

private theorem carry_run {In S Mid Out : Type} (P : Program V In S) (Q : Program V Mid Out)
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

/-- Transport a property with P opaque; never compare two expanded runs. -/
private theorem run_property {In Out : Type} (P : Program V In Out)
    (s t : V → In) (he : s = t) (v : V) (property : Out → Prop)
    (hs : property (P.runEncoded G s v)) : property (P.runEncoded G t v) := by
  cases he
  exact hs

def state {bits : ℕ} (ids : BitCode V bits) (L Δ k t b n B : ℕ) (s : V → Input V B Δ k b n) :=
  (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B).runEncoded G s

def clientState {bits : ℕ} (ids : BitCode V bits) (L Δ k t b n B : ℕ) (s : V → Input V B Δ k b n) :=
  fun v => inputOf (state G ids L Δ k t b n B s v)

theorem aggregate_run {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (aggregate ids L Δ a k t b n B hB).runEncoded G s = fun v =>
      ((GeneralCoveringTaskAggregate.program ids L a B k hB).runEncoded G (clientState G ids L Δ k t b n B s) v,
        state G ids L Δ k t b n B s v) :=
  carry_run G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
    (GeneralCoveringTaskAggregate.program ids L a B k hB) inputOf s

def before {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) := (aggregate ids L Δ a k t b n B hB).runEncoded G s

def repairState {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :=
  (GeneralCoveringOwnerRepair.core ids).runEncoded G (fun v => repairInput (before G ids L Δ a k t b n B hB s v))

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    (program ids L Δ a k t b n B hB).runEncoded G s = fun v =>
      ((before G ids L Δ a k t b n B hB s v).1 || (repairState G ids L Δ a k t b n B hB s v).selected,
        (repairState G ids L Δ a k t b n B hB s v, before G ids L Δ a k t b n B hB s v)) :=
  compose_run G (aggregate ids L Δ a k t b n B hB) (GeneralCoveringOwnerRepair.core ids)
    repairInput (fun r s => (s.1 || r.selected, (r, s))) s

theorem aggregate_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    (before G ids L Δ a k t b n B hB s v).2 = state G ids L Δ k t b n B s v := by
  exact congrArg (fun z : Before V B Δ k b n => z.2)
    (congrFun (aggregate_run G ids L Δ a k t b n B hB s) v)

theorem retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    ((program ids L Δ a k t b n B hB).runEncoded G s v).2.2.2 = state G ids L Δ k t b n B s v := by
  rw [run_program]
  exact aggregate_retained G ids L Δ a k t b n B hB s v

theorem env_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    (before G ids L Δ a k t b n B hB s v).2.env =
      GeneralCoveringOwnerSimulation.learned G ids L Δ (fun u => (s u).1) v :=
  (congrArg (fun x : Saved V B Δ k b n => x.env) (aggregate_retained G ids L Δ a k t b n B hB s v)).trans
    (GeneralCoveringTaskRandomPhysicalMarks.env_retained G ids L Δ k t b n B
      (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v)

theorem private_input_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) (v : V) :
    ((program ids L Δ a k t b n B hB).runEncoded G s v).2.2.2.env.metadata.owned.input = (s v).1 ∧
      ((program ids L Δ a k t b n B hB).runEncoded G s v).2.2.2.fields.cost = (s v).2.1 ∧
      ((program ids L Δ a k t b n B hB).runEncoded G s v).2.2.2.coins = (s v).2.2 := by
  simp only [retained G ids L Δ a k t b n B hB s v]
  refine ⟨?_, ?_, ?_⟩
  · delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) v
      (fun z : Saved V B Δ k b n => z.env.metadata.owned.input = (s v).1)
      (GeneralCoveringTaskRandomPhysicalMarks.private_input_retained G ids L Δ k t b n B
        (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v)
  · delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) v
      (fun z : Saved V B Δ k b n => z.fields.cost = (s v).2.1)
      (GeneralCoveringTaskRandomPhysicalMarks.cost_retained G ids L Δ k t b n B
        (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v)
  · delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) v
      (fun z : Saved V B Δ k b n => z.coins = (s v).2.2)
      (GeneralCoveringTaskRandomPhysicalMarks.coins_retained G ids L Δ k t b n B
        (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v)

def aggregateOutput {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) : Finset V :=
  Finset.univ.filter (fun v => (before G ids L Δ a k t b n B hB s v).1)

def output {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) : Finset V :=
  Finset.univ.filter (fun v => ((program ids L Δ a k t b n B hB).runEncoded G s v).1)

theorem aggregate_output_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    aggregateOutput G ids L Δ a k t b n B hB s =
      GeneralCoveringTaskAggregate.output G ids L a B k hB (clientState G ids L Δ k t b n B s) :=
  congrArg (fun out : V → Before V B Δ k b n => Finset.univ.filter (fun v => (out v).1))
    (aggregate_run G ids L Δ a k t b n B hB s)

theorem output_union {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B Δ k b n) :
    output G ids L Δ a k t b n B hB s = aggregateOutput G ids L Δ a k t b n B hB s ∪
      GeneralCoveringOwnerRepair.chosen (repairState G ids L Δ a k t b n B hB s) := by
  ext v
  simp only [output, aggregateOutput, GeneralCoveringOwnerRepair.chosen, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union, run_program, Bool.or_eq_true]

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def partition {B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (L : ℕ) (d : Original G B Δ k t b n s) :=
  GeneralCoveringTaskRandomPhysicalMarks.partition G d.cover d.D d.R L d.hk t (fun v => (s v).2.2)

noncomputable def boundary {B Δ k t b n : ℕ} {s : V → Input V B Δ k b n}
    (L : ℕ) (d : Original G B Δ k t b n s) :=
  GeneralCoveringRandomBoundaryBound.boundary G d.cover d.D d.R L Δ k d.hk t b n (fun v => (s v).2.2)

/-- All geometry is derived from the same actual random producer outcome. -/
noncomputable def geometry {bits L Δ k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (d : Original G B Δ k t b n s) :
    GeneralCoveringTaskRoles.Geometry G L B (clientState G ids L Δ k t b n B s) := by
  have hf := GeneralCoveringTaskRandomPhysicalMarks.fields_spec G ids L Δ k d.hk t d.ht b n B
    (fun v => (s v).1) d.toOriginal (fun v => (s v).2.1) (fun v => (s v).2.2)
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows (fun v => (s v).1) d.center d.demand d.candidates d.inverse
  have hm (v : V) : (state G ids L Δ k t b n B s v).env.metadata =
      GeneralCoveringOwnerDiscoveryCorrect.metadata G d.cover d.D d.R L (fun u => (s u).1) v := by
    delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) v
      (fun z : Saved V B Δ k b n => z.env.metadata =
        GeneralCoveringOwnerDiscoveryCorrect.metadata G d.cover d.D d.R L (fun u => (s u).1) v)
      ((congrArg GeneralCoveringOwnerVirtualPrepare.Env.metadata
        (GeneralCoveringTaskRandomPhysicalMarks.env_retained G ids L Δ k t b n B
          (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v)).trans (hs.1 v))
  refine {
    cover := d.cover
    targets := d.targets
    D := d.D
    R := d.R
    Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
    k := k
    P := partition G L d
    Bdy := boundary G L d
    local_rows := d.local_rows
    owner := fun v => congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.owner) (hm v)
    admissible := fun v => congrArg GeneralCoveringOwnerSupport.State.admissible (hm v)
    heavy := fun v => congrArg GeneralCoveringOwnerSupport.State.heavy (hm v)
    residual := fun v => congrArg GeneralCoveringOwnerSupport.State.residual (hm v)
    candidates := fun v => (congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.input.candidates) (hm v)).trans (d.candidates v)
    inverse := fun v => (congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.input.targets) (hm v)).trans (d.inverse v)
    incidence := d.incidence
    low_role := ?_
    excluded_role := ?_
    interior := ?_ }
  · intro U hU i hi
    change (state G ids L Δ k t b n B s i.val.val).fields.role = _
    delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) i.val.val
      (fun z : Saved V B Δ k b n => z.fields.role = some (GeneralCoveringTaskRoles.name d.D
        (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) U ((partition G L d).nonempty U hU)))
      (hf.2.1 U hU i hi).2
  · intro i hi
    change (state G ids L Δ k t b n B s i.val).fields.role = none
    delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) i.val
      (fun z : Saved V B Δ k b n => z.fields.role = none) (hf.2.2.1 i hi)
  · intro i
    change (state G ids L Δ k t b n B s i.val.val).fields.interior = _
    delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) i.val.val
      (fun z : Saved V B Δ k b n => z.fields.interior = decide (i ∉ boundary G L d)) (hf.2.2.2.1 i)

theorem aggregate_spec {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hB : 1 ≤ B) (d : Original G B Δ k t b n s)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
    let P := partition G L d
    let Bdy := boundary G L d
    let O := aggregateOutput G ids L Δ a k t b n B hB s
    O ⊆ P.parts.biUnion (fun I => service G d.cover d.D d.R L Q I Bdy) ∧
      O ⊆ CoveringSupport.admissible d.cover d.R ∧
      GeneralCoveringNormalizedIntegral.Covers d.cover (P.parts.biUnion (fun I => demands G d.cover d.D d.R L Q I Bdy)) O ∧
      ∀ W : Finset V, W ⊆ CoveringSupport.admissible d.cover d.R →
        GeneralCoveringNormalizedIntegral.Covers d.cover d.R W →
        (∑ v ∈ O, (s v).2.1.val) ≤ ∑ v ∈ W, (s v).2.1.val := by
  dsimp only
  rw [aggregate_output_eq]
  let cs := clientState G ids L Δ k t b n B s
  let g := geometry (L := L) G ids d
  have hcost : ∀ v, (cs v).2.cost = (s v).2.1 := by
    intro v
    change (state G ids L Δ k t b n B s v).fields.cost = (s v).2.1
    delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) v
      (fun z : Saved V B Δ k b n => z.fields.cost = (s v).2.1)
      (GeneralCoveringTaskRandomPhysicalMarks.cost_retained G ids L Δ k t b n B
        (fun u => (s u).1) (fun u => (s u).2.1) (fun u => (s u).2.2) v)
  have hpositive : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (cs v).2.cost.val := by
    intro v hv
    rw [hcost v]
    exact hc v hv
  have hs := GeneralCoveringTaskAggregate.aggregate_spec G ids g hcover hadm a ha hden hB hpositive rfl
  have hsum (U : Finset V) : (∑ v ∈ U, (cs v).2.cost.val) = ∑ v ∈ U, (s v).2.1.val := by
    apply Finset.sum_congr rfl
    intro v _
    exact congrArg Fin.val (hcost v)
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
  intro W _hWadm hW
  calc
    _ = ∑ v ∈ GeneralCoveringTaskAggregate.output G ids L a B k hB cs, (cs v).2.cost.val := (hsum _).symm
    _ ≤ ∑ v ∈ W, (cs v).2.cost.val := (hs.2.2.2 W hW).2
    _ = ∑ v ∈ W, (s v).2.1.val := hsum W

abbrev marked (D : Finset V) (Q : Finset D) (Bdy : Finset (Low D Q)) : Finset V :=
  GeneralCoveringTaskPhysicalRepair.marked D Q Bdy

private theorem bool_of_iff (b : Bool) (p : Prop) [Decidable p] (h : b = true ↔ p) : b = decide p := by
  cases b <;> simp_all

/-- A graph-free Boolean bridge; native facts below derive every premise. -/
private theorem local_mark {B Δ k b n : ℕ} (D : Finset V) (Q : Finset D) (Bdy : Finset (Low D Q)) (z : V → Before V B Δ k b n)
    (hc : ∀ v, (z v).2.env.metadata.owned.input.center = decide (v ∈ D))
    (hh : ∀ v, (z v).2.env.high = decide (v ∈ Q.image Subtype.val))
    (hl : ∀ v, (z v).2.env.low = decide (v ∈ (Finset.univ : Finset (Low D Q)).image (fun i => i.val.val)))
    (hi : ∀ i : Low D Q, (z i.val.val).2.fields.interior = decide (i ∉ Bdy)) (v : V) :
    mark (z v) = decide (v ∈ marked D Q Bdy) := by
  by_cases hhigh : v ∈ Q.image Subtype.val
  · have hvD := GeneralCoveringTaskPhysicalRepair.marked_subset D Q Bdy (Finset.mem_union_left _ hhigh)
    simp [mark, hc v, hh v, hhigh, hvD, marked, GeneralCoveringTaskPhysicalRepair.marked]
  · by_cases hlow : v ∈ (Finset.univ : Finset (Low D Q)).image (fun i => i.val.val)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hlow
      have hbi : i.val.val ∈ Bdy.image (fun i => i.val.val) ↔ i ∈ Bdy := by
        constructor
        · rintro h
          obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
          have hji : j = i := Subtype.ext (Subtype.ext he)
          exact hji ▸ hj
        · intro h
          exact Finset.mem_image.mpr ⟨i, h, rfl⟩
      have hli : i.val.val ∈ (Finset.univ : Finset (Low D Q)).image (fun i => i.val.val) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      by_cases hb : i ∈ Bdy <;>
        simp [mark, hc, hh, hl, hi i, i.val.property, hhigh, hli, hb, marked,
          GeneralCoveringTaskPhysicalRepair.marked, hbi]
    · have hb : v ∉ Bdy.image (fun i => i.val.val) := by
        intro h
        obtain ⟨i, _, he⟩ := Finset.mem_image.mp h
        exact hlow (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩)
      simp [mark, hh v, hl v, hhigh, hlow, marked, GeneralCoveringTaskPhysicalRepair.marked, hb]

private theorem interior_of_eq {B Δ k b n : ℕ} {x y : Saved V B Δ k b n} {q : Bool}
    (he : x = y) (hy : y.fields.interior = q) : x.fields.interior = q :=
  (congrArg (fun z : Saved V B Δ k b n => z.fields.interior) he).trans hy

theorem mark_exact {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hB : 1 ≤ B) (d : Original G B Δ k t b n s) (v : V) :
    mark (before G ids L Δ a k t b n B hB s v) = decide (v ∈ marked d.D
      (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G L d)) := by
  let input := fun v => (s v).1
  let E := GeneralCoveringOwnerSimulation.learned G ids L Δ input
  have he (v : V) := env_retained G ids L Δ a k t b n B hB s v
  have hp := GeneralCoveringTaskRandomPhysicalMarks.fields_spec G ids L Δ k d.hk t d.ht b n B
    (fun u => (s u).1) d.toOriginal (fun u => (s u).2.1) (fun u => (s u).2.2)
  have hInterior (i : Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) :
      (state G ids L Δ k t b n B s i.val.val).fields.interior = decide (i ∉ boundary G L d) := by
    delta state
    exact run_property G (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B)
      (fun u => ((s u).1, ((s u).2.1, (s u).2.2))) s (input_eta s) i.val.val
      (fun z : Saved V B Δ k b n => z.fields.interior = decide (i ∉ boundary G L d)) (hp.2.2.2.1 i)
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  have hf := GeneralCoveringOwnerHighCount.learned_flags G ids d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  apply local_mark d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)
    (boundary G L d) (before G ids L Δ a k t b n B hB s)
  · intro u
    exact (congrArg GeneralCoveringOwners.Input.center
      ((congrArg (fun z : GeneralCoveringOwnerVirtualPrepare.Env V => z.metadata.owned.input) (he u)).trans
        (GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input u))).trans (d.center u)
  · intro u
    apply (congrArg GeneralCoveringOwnerVirtualPrepare.Env.high (he u)).trans
    apply bool_of_iff
    have hiff := (GeneralCoveringOwnerHighCount.mem_flagged E u).symm
    rw [hf] at hiff
    exact hiff
  · intro u
    exact (congrArg GeneralCoveringOwnerVirtualPrepare.Env.low (he u)).trans (hs.2.2.1 u)
  · intro i
    exact interior_of_eq (aggregate_retained G ids L Δ a k t b n B hB s i.val.val) (hInterior i)

theorem repair_correct {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hB : 1 ≤ B) (d : Original G B Δ k t b n s) :
    repairState G ids L Δ a k t b n B hB s = GeneralCoveringOwnerRepair.expected G
      (fun v => (before G ids L Δ a k t b n B hB s v).2.env) d.cover d.D d.R L
      (marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G L d)) := by
  let input := fun v => (s v).1
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  have hm (v : V) : (before G ids L Δ a k t b n B hB s v).2.env.metadata =
      GeneralCoveringOwnerDiscoveryCorrect.metadata G d.cover d.D d.R L input v :=
    (congrArg GeneralCoveringOwnerVirtualPrepare.Env.metadata (env_retained G ids L Δ a k t b n B hB s v)).trans (hs.1 v)
  have hi (v : V) : (before G ids L Δ a k t b n B hB s v).2.env.metadata.owned.input = input v :=
    (congrArg (fun z : GeneralCoveringOwnerVirtualPrepare.Env V => z.metadata.owned.input)
      (env_retained G ids L Δ a k t b n B hB s v)).trans
        (GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v)
  apply GeneralCoveringOwnerRepair.core_correct G ids d.cover d.D d.R L _
    (GeneralCoveringTaskPhysicalRepair.marked_subset _ _ _)
    (fun v => (before G ids L Δ a k t b n B hB s v).2.env)
    (fun v => mark (before G ids L Δ a k t b n B hB s v))
  · intro v
    exact (congrArg GeneralCoveringOwners.Input.center (hi v)).trans (d.center v)
  · intro v
    exact congrArg GeneralCoveringOwnerSupport.State.residual (hm v)
  · intro v
    exact (congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.input.candidates) (hm v)).trans (d.candidates v)
  · intro v
    exact congrArg GeneralCoveringOwnerSupport.State.heavy (hm v)
  · exact mark_exact G ids hB d
  · exact d.local_rows

theorem output_exact {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hB : 1 ≤ B) (d : Original G B Δ k t b n s) :
    output G ids L Δ a k t b n B hB s = aggregateOutput G ids L Δ a k t b n B hB s ∪
      GeneralCoveringOwnerRepair.selected G d.cover d.D d.R L
        (marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G L d)) := by
  rw [output_union, repair_correct G ids hB d, GeneralCoveringOwnerRepair.chosen_expected]


theorem covers {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G B Δ k t b n s) (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) :
    output G ids L Δ a k t b n B hB s ⊆ CoveringSupport.admissible d.cover d.R ∧
      GeneralCoveringNormalizedIntegral.Covers d.cover d.R (output G ids L Δ a k t b n B hB s) := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
  let P := partition G L d
  let Bdy := boundary G L d
  let I := marked d.D Q Bdy
  have hiD : I ⊆ d.D := GeneralCoveringTaskPhysicalRepair.marked_subset _ _ _
  have hg := aggregate_spec (L := L) G ids hB d hcover hadm ha hden hc
  rw [output_exact G ids hB d]
  refine ⟨Finset.union_subset hg.2.1 (GeneralCoveringOwnerRepair.admissible G d.cover d.D d.R L I (hiD.trans hadm)), ?_⟩
  intro r hr
  by_cases hres : r ∈ GeneralCoveringOwnerSupport.residual G d.cover d.D d.R L
  · obtain ⟨i, hi, ho⟩ := GeneralCoveringOwners.exists_owner d.cover d.D d.R hcover (Finset.mem_union_left d.D hr)
    let j : d.D := ⟨i, hi⟩
    by_cases hq : j ∈ Q
    · have hm : i ∈ I := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hq, rfl⟩)
      obtain ⟨v, hv, hvc⟩ := GeneralCoveringOwnerRepair.covers_class G d.cover d.D d.R L I hiD hcover hres hm ho
      exact ⟨v, Finset.mem_union_right _ hv, hvc⟩
    · let l : Low d.D Q := ⟨j, hq⟩
      by_cases hb : l ∈ Bdy
      · have hm : i ∈ I := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, hb, rfl⟩)
        obtain ⟨v, hv, hvc⟩ := GeneralCoveringOwnerRepair.covers_class G d.cover d.D d.R L I hiD hcover hres hm ho
        exact ⟨v, Finset.mem_union_right _ hv, hvc⟩
      · obtain ⟨U, hU, hl⟩ := P.covers l (Finset.mem_univ l)
        have htask : r ∈ P.parts.biUnion (fun U => demands G d.cover d.D d.R L Q U Bdy) :=
          Finset.mem_biUnion.mpr ⟨U, hU, Finset.mem_filter.mpr ⟨hres, l, hl, hb, ho⟩⟩
        obtain ⟨v, hv, hvc⟩ := hg.2.2.1 r htask
        exact ⟨v, Finset.mem_union_left _ hv, hvc⟩
  · obtain ⟨v, hv, hvc⟩ := GeneralCoveringOwnerRepair.covers_heavy_row G d.cover d.D d.R L I hr hres
    exact ⟨v, Finset.mem_union_right _ hv, hvc⟩

theorem cost {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G B Δ k t b n s) (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val)
    (W : Finset V) (hWadm : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) :
    (∑ v ∈ output G ids L Δ a k t b n B hB s, (s v).2.1.val) ≤ (∑ v ∈ W, (s v).2.1.val) +
      B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card +
        (boundary G L d).card) := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
  let Bdy := boundary G L d
  let I := marked d.D Q Bdy
  let A := aggregateOutput G ids L Δ a k t b n B hB s
  let Z := GeneralCoveringOwnerRepair.selected G d.cover d.D d.R L I
  have hg := aggregate_spec (L := L) G ids hB d hcover hadm ha hden hc
  have hb : ∀ v ∈ CoveringSupport.admissible d.cover d.R, (0 : ℝ) ≤ (s v).2.1.val ∧ ((s v).2.1.val : ℝ) ≤ B := by
    intro v _
    constructor
    · exact Nat.cast_nonneg _
    · have hh : (s v).2.1.val ≤ B := by have h := (s v).2.1.isLt; omega
      exact_mod_cast hh
  have hr := (GeneralCoveringOwnerRepair.cost G d.cover d.D d.R L B I (fun v => ((s v).2.1.val : ℝ))
    ((GeneralCoveringTaskPhysicalRepair.marked_subset _ _ _).trans hadm) hb).2
  have hn : (∑ v ∈ Z, (s v).2.1.val) ≤ B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * I.card := by
    exact_mod_cast hr
  have hm : 2 * B * I.card ≤ 2 * B * (Q.card + Bdy.card) :=
    Nat.mul_le_mul_left (2 * B) (GeneralCoveringTaskPhysicalRepair.marked_card d.D Q Bdy)
  have hu := Finset.sum_union_inter (s₁ := A) (s₂ := Z) (f := fun v => (s v).2.1.val)
  have haCost : (∑ v ∈ A, (s v).2.1.val) ≤ ∑ v ∈ W, (s v).2.1.val := by
    exact hg.2.2.2 W hWadm hW
  have huBound : (∑ v ∈ A ∪ Z, (s v).2.1.val) ≤ (∑ v ∈ A, (s v).2.1.val) + ∑ v ∈ Z, (s v).2.1.val := by
    omega
  rw [output_exact G ids hB d]
  change (∑ v ∈ A ∪ Z, (s v).2.1.val) ≤ (∑ v ∈ W, (s v).2.1.val) +
    B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * (Q.card + Bdy.card)
  calc
    _ ≤ (∑ v ∈ A, (s v).2.1.val) + ∑ v ∈ Z, (s v).2.1.val := huBound
    _ ≤ (∑ v ∈ W, (s v).2.1.val) +
        (B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * I.card) := Nat.add_le_add haCost hn
    _ = (∑ v ∈ W, (s v).2.1.val) + B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * I.card :=
      (Nat.add_assoc _ _ _).symm
    _ ≤ _ := Nat.add_le_add_left hm _

theorem empty_demands {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G B Δ k t b n s) (hR : d.R = ∅) (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.1.val) : output G ids L Δ a k t b n B hB s = ∅ := by
  have hs := (covers (L := L) (Δ := Δ) (a := a) (b := b) (n := n) G ids hB d hcover hadm ha hden hc).1
  have he : output G ids L Δ a k t b n B hB s ⊆ ∅ := by
    simpa only [hR, CoveringSupport.admissible, Finset.biUnion_empty] using hs
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (he hv))

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B) (s : V → Input V B Δ k b n) :
    output G ids L Δ a k t b n B hB s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun v => isEmptyElim v)

/-- With no low vertices there are no client keys; only actual repair remains. -/
theorem empty_low {bits L Δ a k t b n B : ℕ} {s : V → Input V B Δ k b n}
    (ids : BitCode V bits) (hB : 1 ≤ B) (d : Original G B Δ k t b n s)
    [IsEmpty (Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))] :
    aggregateOutput G ids L Δ a k t b n B hB s = ∅ ∧
      output G ids L Δ a k t b n B hB s = GeneralCoveringOwnerRepair.selected G d.cover d.D d.R L
        (marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G L d)) := by
  let g := geometry (L := L) G ids d
  have he : g.P.parts = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro U hU
    obtain ⟨i, _⟩ := g.P.nonempty U hU
    exact isEmptyElim (show Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) from i)
  have hs := GeneralCoveringTaskAggregate.empty_parts G ids g he a hB
  have hout : aggregateOutput G ids L Δ a k t b n B hB s = ∅ := by
    rw [aggregate_output_eq]
    exact hs.1
  exact ⟨hout, by rw [output_exact G ids hB d, hout, Finset.empty_union]⟩

theorem aggregate_rounds {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (aggregate ids L Δ a k t b n B hB).rounds =
      10 + 4 * (n * (3 * k + 1) + 1) + (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4) := by
  simp only [aggregate, attach, Program.rounds, ProgramMemory.rounds, Nat.zero_add,
    GeneralCoveringTaskRandomPhysicalMarks.rounds, GeneralCoveringTaskAggregate.rounds]

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t b n B hB).rounds =
      (10 + 4 * (n * (3 * k + 1) + 1) + (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4)) + 2 := by
  simp only [program, prepare, finish, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringOwnerRepair.core_rounds, Nat.zero_add, Nat.add_zero, aggregate_rounds]

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t b n B hB).maxBits =
      max (max (GeneralCoveringTaskRandomPhysicalMarks.program ids L Δ k t b n B).maxBits
        (GeneralCoveringTaskAggregate.program ids L a B k hB).maxBits) (bits + 1) := by
  simp only [program, aggregate, attach, prepare, finish, Program.maxBits, ProgramMemory.maxBits,
    GeneralCoveringOwnerRepair.core_maxBits, Nat.zero_max, Nat.max_zero]

theorem packet_bound {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t b n B hB).maxBits ≤
      max (max ((L + Δ + 3) *
        (bits + max (ActiveFiniteBitPartition.packetBound bits Δ k b n) (k * (bits + 1)) + 2))
        (max (bits + 2) (max 1 L * (bits + (GeneralCoveringTaskIntegral.program ids a B k hB).maxBits + 1)))) (bits + 1) := by
  rw [maxBits_eq]
  apply max_le_max_right
  apply max_le_max (GeneralCoveringTaskRandomPhysicalMarks.packet_bound ids L Δ k t b n B)
  rw [GeneralCoveringTaskAggregate.maxBits_eq]
  exact GeneralCoveringTaskParallel.maxBits ids L a B k hB

def bitCoefficient (L Δ a k b n B c : ℕ) : ℕ :=
  max (max (GeneralCoveringTaskRandomPhysicalMarks.bitCoefficient L Δ k b n c)
    (max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B 1 (2 * B * k) + 1) + 1)))) (c + 1)

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B c : ℕ) (hB : 1 ≤ B)
    (hids : bits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (program ids L Δ a k t b n B hB).maxBits ≤
      bitCoefficient L Δ a k b n B c * Nat.clog 2 (Fintype.card V + 2) := by
  have hm := GeneralCoveringTaskRandomPhysicalMarks.logarithmic_bits ids L Δ k t b n B c hids
  have ha := (GeneralCoveringTaskAggregate.logarithmic_bits ids L a B k hB (Fintype.card V) c hids).1
  have hr := (BroadcastModel.logarithmic_message_budget (Fintype.card V) bits c hids).1
  rw [maxBits_eq]
  simpa only [bitCoefficient, Nat.mul_max_mul_right] using max_le_max (max_le_max hm ha) hr

/-- Common polynomial identifier capacity is measured by PUBLIC physical order. -/
theorem public_costs {bits : ℕ} (ids : BitCode V bits) (L Δ a k t b n B c p d M : ℕ) (hB : 1 ≤ B)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program ids L Δ a k t b n B hB).rounds =
      (10 + 4 * (n * (3 * k + 1) + 1) + (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4)) + 2 ∧
    (program ids L Δ a k t b n B hB).maxBits ≤
      bitCoefficient L Δ a k b n B (DeterministicColorReductionIdentifiers.bitFactor c p d) *
        Nat.clog 2 (Fintype.card V + 2) := by
  exact ⟨rounds ids L Δ a k t b n B hB, logarithmic_bits ids L Δ a k t b n B _ hB
    (DeterministicColorReductionIdentifiers.public_length_bound (Fintype.card V) bits c p d M hbits hM)⟩

end Paper.GeneralCoveringRandomIntegralPhysical

#print axioms Paper.GeneralCoveringRandomIntegralPhysical.aggregate_run
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.run_program
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.aggregate_retained
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.retained
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.env_retained
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.private_input_retained
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.aggregate_output_eq
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.output_union
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.geometry
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.aggregate_spec
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.mark_exact
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.repair_correct
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.output_exact
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.covers
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.cost
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.empty_demands
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.empty_physical
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.empty_low
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.aggregate_rounds
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.rounds
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.maxBits_eq
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.packet_bound
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.logarithmic_bits
#print axioms Paper.GeneralCoveringRandomIntegralPhysical.public_costs

