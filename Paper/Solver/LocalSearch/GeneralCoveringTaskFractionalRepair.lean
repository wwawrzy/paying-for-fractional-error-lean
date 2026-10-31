import Paper.Solver.LocalSearch.GeneralCoveringTaskFractionalAggregate
import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepair

/-! One physical VirtualPrepare, actual fractional Aggregate retaining the
whole Env and Fields, then the two-round optional-partner repair CORE.
Own output is p+q*selectedIndicator, without clipping. Full original-R
fractional feasibility and additive repair cost are proved for truthful
original private input and local correct full-part/interior fields. Actual
high/metadata/masks/repair sets are derived, never runtime oracles. -/
namespace Paper.GeneralCoveringTaskFractionalRepair
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringOwnerVirtualPrepare.Env V × GeneralCoveringTaskRoles.Fields V B
abbrev NativeInput (V : Type) (B : ℕ) := GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B
abbrev Before (V : Type) (B : ℕ) := ℕ × (GeneralCoveringTaskRoles.Fields V B × GeneralCoveringOwnerVirtualPrepare.Env V)
abbrev Output (V : Type) (B : ℕ) := ℕ × (GeneralCoveringOwnerRepair.Output V × Before V B)

def aggregatePrepare (B : ℕ) : Program V (Input V B) (GeneralCoveringTaskFractionalAggregate.Input V B × Input V B) :=
  .local (fun _ _ s => ((s.1.metadata, s.2), s))

def aggregateFinish (B : ℕ) : Program V (ℕ × Input V B) (Before V B) :=
  .local (fun _ _ s => (s.1, (s.2.2, s.2.1)))

def beforeProgram {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) : Program V (Input V B) (Before V B) :=
  .seq (aggregatePrepare B) (.seq (ProgramMemory.carry (GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB))
    (aggregateFinish B))

def mark {B : ℕ} (s : Before V B) : Bool := s.2.2.metadata.owned.input.center &&
  (s.2.2.high || (s.2.2.low && !s.2.1.interior))

def repairInput {B : ℕ} (s : Before V B) : GeneralCoveringOwnerRepair.Input V := ⟨s.2.2, mark s⟩

def repairPrepare (B : ℕ) : Program V (Before V B) (GeneralCoveringOwnerRepair.Input V × Before V B) :=
  .local (fun _ _ s => (repairInput s, s))

def finish (B q : ℕ) : Program V (GeneralCoveringOwnerRepair.Output V × Before V B) (Output V B) :=
  .local (fun _ _ s => (s.2.1 + (if s.1.selected then q else 0), (s.1, s.2)))

def core {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) : Program V (Input V B) (Output V B) :=
  .seq (beforeProgram ids L a B k q hB) (.seq (repairPrepare B)
    (.seq (ProgramMemory.carry (X := Before V B) (GeneralCoveringOwnerRepair.core ids)) (finish B q)))

/-- Single native ten-round preparation; no repeated Support/owner prefix. -/
def program {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) : Program V (NativeInput V B) (Output V B) :=
  .seq (ProgramMemory.carry (GeneralCoveringOwnerVirtualPrepare.program ids L Δ)) (core ids L a B k q hB)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem carry_encoded {In Out X : Type} (P : Program V In Out) (s : V → In) (x : V → X) :
    (ProgramMemory.carry P).runEncoded G (fun v => (s v, x v)) = fun v => (P.runEncoded G s v, x v) := by
  simp only [Program.runEncoded_eq_run]
  exact ProgramMemory.run G P s x

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

theorem beforeProgram_run {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    (beforeProgram ids L a B k q hB).runEncoded G s = fun v =>
      ((GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB).runEncoded G
        (fun u => ((s u).1.metadata, (s u).2)) v, ((s v).2, (s v).1)) := by
  rw [Program.runEncoded_eq_run]
  change (aggregateFinish B).run G
    ((ProgramMemory.carry (GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB)).run G
      (fun v => (((s v).1.metadata, (s v).2), s v))) = _
  rw [ProgramMemory.run]
  change (fun v => ((GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB).run G
    (fun u => ((s u).1.metadata, (s u).2)) v, ((s v).2, (s v).1))) = _
  simp only [Program.runEncoded_eq_run]

theorem run_core {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    (core ids L a B k q hB).runEncoded G s =
      let z := (beforeProgram ids L a B k q hB).runEncoded G s
      let r := (GeneralCoveringOwnerRepair.core ids).runEncoded G (fun v => repairInput (z v))
      fun v => ((z v).1 + (if (r v).selected then q else 0), (r v, z v)) :=
  compose_run G (beforeProgram ids L a B k q hB) (GeneralCoveringOwnerRepair.core ids)
    repairInput (fun r z => (z.1 + (if r.selected then q else 0), (r, z))) s

def env {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) {B : ℕ} (s : V → NativeInput V B) :=
  (GeneralCoveringOwnerVirtualPrepare.program ids L Δ).runEncoded G (fun v => (s v).1)

def roleInput {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) {B : ℕ} (s : V → NativeInput V B) :
    V → GeneralCoveringTaskFractionalAggregate.Input V B := fun v => ((env G ids L Δ s v).metadata, (s v).2)

def before {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) :=
  (beforeProgram ids L a B k q hB).runEncoded G (fun v => (env G ids L Δ s v, (s v).2))

def repairState {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) :=
  (GeneralCoveringOwnerRepair.core ids).runEncoded G (fun v => repairInput (before G ids L Δ a B k q hB s v))

theorem before_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) :
    before G ids L Δ a B k q hB s = fun v =>
      ((GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB).runEncoded G (roleInput G ids L Δ s) v,
        ((s v).2, env G ids L Δ s v)) :=
  beforeProgram_run G ids L a B k q hB _

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) :
    (program ids L Δ a B k q hB).runEncoded G s = fun v =>
      ((before G ids L Δ a B k q hB s v).1 + (if (repairState G ids L Δ a B k q hB s v).selected then q else 0),
        (repairState G ids L Δ a B k q hB s v, before G ids L Δ a B k q hB s v)) := by
  change (core ids L a B k q hB).runEncoded G
    ((ProgramMemory.carry (GeneralCoveringOwnerVirtualPrepare.program ids L Δ)).runEncoded G
      (fun v => ((s v).1, (s v).2))) = _
  rw [carry_encoded G (GeneralCoveringOwnerVirtualPrepare.program ids L Δ), run_core]
  rfl

theorem env_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) (v : V) :
    ((program ids L Δ a B k q hB).runEncoded G s v).2.2.2.2 = env G ids L Δ s v := by rw [run_program, before_eq]

theorem fields_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) (v : V) :
    ((program ids L Δ a B k q hB).runEncoded G s v).2.2.2.1 = (s v).2 := by rw [run_program, before_eq]

theorem private_input_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) (v : V) :
    ((program ids L Δ a B k q hB).runEncoded G s v).2.2.2.2.metadata.owned.input = (s v).1 :=
  (congrArg (fun e : GeneralCoveringOwnerVirtualPrepare.Env V => e.metadata.owned.input)
    (env_retained G ids L Δ a B k q hB s v)).trans
      (GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ (fun u => (s u).1) v)

/-- Public bound holds even for malformed private data and arbitrary marks. -/
theorem output_bound {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) (v : V) :
    ((program ids L Δ a B k q hB).runEncoded G s v).1 ≤
      max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + q := by
  rw [run_program, before_eq]
  have hp := GeneralCoveringTaskFractionalAggregate.output_bound G ids L a B k q hB (roleInput G ids L Δ s) v
  by_cases h : (repairState G ids L Δ a B k q hB s v).selected = true
  · simpa only [if_pos h] using Nat.add_le_add_right hp q
  · simpa only [if_neg h, Nat.add_zero] using hp.trans (Nat.le_add_right _ _)

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Original private interpretation and truthful local part/interior fields.
Q and boundary are fixed below to actual high and the boundary of THIS P. -/
structure Original (L Δ k B : ℕ) (s : V → NativeInput V B) where
  cover : V → Finset V
  targets : V → Finset V
  D : Finset V
  R : Finset V
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  local_rows : ∀ r ∈ R, cover r ⊆ closed G r
  center : ∀ v, (s v).1.center = decide (v ∈ D)
  demand : ∀ v, (s v).1.demand = decide (v ∈ R)
  candidates : ∀ v, (s v).1.candidates = cover v
  inverse : ∀ v, (s v).1.targets = targets v
  P : SmallParts.Data (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)) Finset.univ k
  low_role : ∀ (I : Finset (Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ))) (hI : I ∈ P.parts)
    (i : Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)), i ∈ I →
    (s i.val.val).2.role = some (GeneralCoveringTaskRoles.name D _ I (P.nonempty I hI))
  excluded_role : ∀ d : D, d ∈ GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ → (s d.val).2.role = none
  interior : ∀ i : Low D (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ),
    (s i.val.val).2.interior = decide (i ∉ BoundaryOwners.vertices
      (graph G cover D R L (GeneralCoveringOwnerVirtualPrepare.high G cover D R L Δ)) Finset.univ P.parts)

noncomputable def boundary {L Δ k B : ℕ} {s : V → NativeInput V B} (d : Original G L Δ k B s) :=
  BoundaryOwners.vertices (graph G d.cover d.D d.R L (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
    Finset.univ d.P.parts

def marked (D : Finset V) (Q : Finset D) (Bdy : Finset (Low D Q)) : Finset V :=
  Q.image Subtype.val ∪ Bdy.image (fun i => i.val.val)

theorem marked_subset (D : Finset V) (Q : Finset D) (Bdy : Finset (Low D Q)) : marked D Q Bdy ⊆ D := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact i.property
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact i.val.property

theorem marked_card (D : Finset V) (Q : Finset D) (Bdy : Finset (Low D Q)) :
    (marked D Q Bdy).card ≤ Q.card + Bdy.card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

private theorem bool_of_iff (b : Bool) (p : Prop) [Decidable p] (h : b = true ↔ p) : b = decide p := by
  cases b <;> simp_all

/-- A graph-free Boolean bridge; native facts below derive every premise. -/
private theorem local_mark {B : ℕ} (D : Finset V) (Q : Finset D) (Bdy : Finset (Low D Q)) (z : V → Before V B)
    (hc : ∀ v, (z v).2.2.metadata.owned.input.center = decide (v ∈ D))
    (hh : ∀ v, (z v).2.2.high = decide (v ∈ Q.image Subtype.val))
    (hl : ∀ v, (z v).2.2.low = decide (v ∈ (Finset.univ : Finset (Low D Q)).image (fun i => i.val.val)))
    (hi : ∀ i : Low D Q, (z i.val.val).2.1.interior = decide (i ∉ Bdy)) (v : V) :
    mark (z v) = decide (v ∈ marked D Q Bdy) := by
  by_cases hhigh : v ∈ Q.image Subtype.val
  · have hvD := marked_subset D Q Bdy (Finset.mem_union_left _ hhigh)
    simp [mark, hc v, hh v, hhigh, hvD, marked]
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
        simp [mark, hc, hh, hl, hi i, i.val.property, hhigh, hli, hb, marked, hbi]
    · have hb : v ∉ Bdy.image (fun i => i.val.val) := by
        intro h
        obtain ⟨i, _, he⟩ := Finset.mem_image.mp h
        exact hlow (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩)
      simp [mark, hh v, hl v, hhigh, hlow, marked, hb]

noncomputable def repairSet {L Δ k B : ℕ} {s : V → NativeInput V B} (d : Original G L Δ k B s) : Finset V :=
  GeneralCoveringOwnerRepair.selected G d.cover d.D d.R L
    (marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G d))

def base {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) (s : V → NativeInput V B) :=
  (GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB).runEncoded G (roleInput G ids L Δ s)

/-- Metadata/high/low truths are consequences of the SINGLE actual producer. -/
theorem env_spec {bits L Δ k B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (d : Original G L Δ k B s) :
    (∀ v, (env G ids L Δ s v).metadata = GeneralCoveringOwnerDiscoveryCorrect.metadata G d.cover d.D d.R L (fun u => (s u).1) v) ∧
    (∀ v, (env G ids L Δ s v).metadata.owned.input = (s v).1) ∧
    (∀ v, (env G ids L Δ s v).low = decide (v ∈ GeneralCoveringOwnerVirtualPrepare.image d.D
      (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))) ∧
    GeneralCoveringOwnerHighCount.flagged (env G ids L Δ s) = GeneralCoveringOwnerHighCount.physicalHigh G d.cover d.D d.R L Δ := by
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids d.cover d.targets d.D d.R L Δ d.incidence d.local_rows
    (fun v => (s v).1) d.center d.demand d.candidates d.inverse
  have hh := GeneralCoveringOwnerHighCount.learned_flags G ids d.cover d.targets d.D d.R L Δ d.incidence d.local_rows
    (fun v => (s v).1) d.center d.demand d.candidates d.inverse
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hh⟩

noncomputable def geometry {bits L Δ k B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits)
    (d : Original G L Δ k B s) : GeneralCoveringTaskRoles.Geometry G L B (roleInput G ids L Δ s) := by
  have hs := env_spec G ids d
  exact
    { cover := d.cover
      targets := d.targets
      D := d.D
      R := d.R
      Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
      k := k
      P := d.P
      Bdy := boundary G d
      local_rows := d.local_rows
      owner := fun v => congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.owner) (hs.1 v)
      admissible := fun v => congrArg GeneralCoveringOwnerSupport.State.admissible (hs.1 v)
      heavy := fun v => congrArg GeneralCoveringOwnerSupport.State.heavy (hs.1 v)
      residual := fun v => congrArg GeneralCoveringOwnerSupport.State.residual (hs.1 v)
      candidates := fun v => (congrArg GeneralCoveringOwners.Input.candidates (hs.2.1 v)).trans (d.candidates v)
      inverse := fun v => (congrArg GeneralCoveringOwners.Input.targets (hs.2.1 v)).trans (d.inverse v)
      incidence := d.incidence
      low_role := d.low_role
      excluded_role := d.excluded_role
      interior := d.interior }

theorem mark_exact {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G L Δ k B s) (v : V) :
    mark (before G ids L Δ a B k q hB s v) = decide (v ∈ marked d.D
      (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G d)) := by
  have hs := env_spec G ids d
  apply local_mark d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)
    (boundary G d) (before G ids L Δ a B k q hB s)
  · intro u
    rw [before_eq]
    exact (congrArg GeneralCoveringOwners.Input.center (hs.2.1 u)).trans (d.center u)
  · intro u
    rw [before_eq]
    apply bool_of_iff
    have hi := (GeneralCoveringOwnerHighCount.mem_flagged (env G ids L Δ s) u).symm
    rw [hs.2.2.2] at hi
    exact hi
  · intro u
    rw [before_eq]
    exact hs.2.2.1 u
  · intro i
    rw [before_eq]
    exact d.interior i

theorem repair_correct {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G L Δ k B s) :
    repairState G ids L Δ a B k q hB s = GeneralCoveringOwnerRepair.expected G (env G ids L Δ s)
      d.cover d.D d.R L (marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G d)) := by
  have hs := env_spec G ids d
  have he : (fun v => repairInput (before G ids L Δ a B k q hB s v)) =
      fun v => (⟨env G ids L Δ s v, mark (before G ids L Δ a B k q hB s v)⟩ : GeneralCoveringOwnerRepair.Input V) := by
    funext v
    unfold repairInput
    rw [before_eq]
  unfold repairState
  rw [he]
  apply GeneralCoveringOwnerRepair.core_correct G ids d.cover d.D d.R L _ (marked_subset _ _ _)
    (env G ids L Δ s) (fun v => mark (before G ids L Δ a B k q hB s v))
  · intro v
    exact (congrArg GeneralCoveringOwners.Input.center (hs.2.1 v)).trans (d.center v)
  · intro v
    exact congrArg GeneralCoveringOwnerSupport.State.residual (hs.1 v)
  · intro v
    exact (congrArg GeneralCoveringOwners.Input.candidates (hs.2.1 v)).trans (d.candidates v)
  · intro v
    exact congrArg GeneralCoveringOwnerSupport.State.heavy (hs.1 v)
  · exact mark_exact G ids hB d
  · exact d.local_rows

/-- Exact native integer numerator, including actual optional partners. -/
theorem output_eq {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G L Δ k B s) (v : V) :
    ((program ids L Δ a B k q hB).runEncoded G s v).1 = base G ids L Δ a B k q hB s v +
      q * (if v ∈ repairSet G d then 1 else 0) := by
  rw [run_program, before_eq, repair_correct G ids hB d]
  change base G ids L Δ a B k q hB s v + (if decide (v ∈ repairSet G d) then q else 0) = _
  by_cases hv : v ∈ repairSet G d <;> simp [hv]

theorem solution_eq {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s) (v : V) :
    (((program ids L Δ a B k q hB).runEncoded G s v).1 : ℝ) / q =
      (base G ids L Δ a B k q hB s v : ℝ) / q + GeneralCoveringTaskFractional.indicator (repairSet G d) v := by
  have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [output_eq G ids hB d v]
  by_cases hv : v ∈ repairSet G d <;>
    simp [hv, GeneralCoveringTaskFractional.indicator, Nat.cast_add, add_div, hqn]

theorem aggregate_spec {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.cost.val) :
    GeneralCoveringTaskFractionalAggregate.Spec d.cover d.R
      (GeneralCoveringTaskFractionalAggregate.taskDemands G (geometry G ids d))
      (GeneralCoveringTaskFractionalAggregate.taskService G (geometry G ids d)) (fun v => (s v).2.cost) q ξ
      (GeneralCoveringTaskFractionalAggregate.taskLP G (geometry G ids d) (fun v => ((s v).2.cost.val : ℝ)))
      (base G ids L Δ a B k q hB s) :=
  GeneralCoveringTaskFractionalAggregate.aggregate_spec G ids (geometry G ids d) hcover hadm a ha hden q hB hq ξ haccuracy hc rfl

/-- Every original row is heavy-hit, owned by a repaired high/boundary center,
or belongs to an interior task. A genuine D-cover excludes owner=none. -/
theorem row_cases {bits L Δ k B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (d : Original G L Δ k B s)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) {r : V} (hr : r ∈ d.R) :
    r ∈ GeneralCoveringTaskFractionalAggregate.taskDemands G (geometry G ids d) ∨ ∃ v ∈ repairSet G d, v ∈ d.cover r := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
  let Bd := boundary G d
  let I := marked d.D Q Bd
  by_cases hres : r ∈ GeneralCoveringOwnerSupport.residual G d.cover d.D d.R L
  · obtain ⟨i, hi, ho⟩ := GeneralCoveringOwners.exists_owner d.cover d.D d.R hcover (Finset.mem_union_left d.D hr)
    let j : d.D := ⟨i, hi⟩
    by_cases hq : j ∈ Q
    · have hm : i ∈ I := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hq, rfl⟩)
      exact Or.inr (GeneralCoveringOwnerRepair.covers_class G d.cover d.D d.R L I (marked_subset _ _ _) hcover hres hm ho)
    · let l : Low d.D Q := ⟨j, hq⟩
      by_cases hb : l ∈ Bd
      · have hm : i ∈ I := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, hb, rfl⟩)
        exact Or.inr (GeneralCoveringOwnerRepair.covers_class G d.cover d.D d.R L I (marked_subset _ _ _) hcover hres hm ho)
      · obtain ⟨U, hU, hl⟩ := d.P.covers l (Finset.mem_univ l)
        exact Or.inl (Finset.mem_biUnion.mpr ⟨U, hU, Finset.mem_filter.mpr ⟨hres, l, hl, hb, ho⟩⟩)
  · exact Or.inr (GeneralCoveringOwnerRepair.covers_heavy_row G d.cover d.D d.R L I hr hres)

theorem repair_admissible {L Δ k B : ℕ} {s : V → NativeInput V B} (d : Original G L Δ k B s)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) : repairSet G d ⊆ CoveringSupport.admissible d.cover d.R :=
  GeneralCoveringOwnerRepair.admissible G d.cover d.D d.R L _ ((marked_subset _ _ _).trans hadm)

theorem support {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.cost.val) :
    ∀ v, v ∉ CoveringSupport.admissible d.cover d.R → ((program ids L Δ a B k q hB).runEncoded G s v).1 = 0 := by
  have hg := aggregate_spec G ids hB hq d hcover hadm ha hden ξ haccuracy hc
  intro v hv
  have hn : v ∉ repairSet G d := fun h => hv (repair_admissible G d hadm h)
  rw [output_eq G ids hB d v, hg.2.1 v hv, if_neg hn, Nat.mul_zero, Nat.add_zero]

theorem feasible {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.cost.val) :
    CoveringOptimum.Feasible d.cover d.R (fun v => (((program ids L Δ a B k q hB).runEncoded G s v).1 : ℝ) / q) := by
  have hg := aggregate_spec G ids hB hq d hcover hadm ha hden ξ haccuracy hc
  have hn (v : V) : (0 : ℝ) ≤ (((program ids L Δ a B k q hB).runEncoded G s v).1 : ℝ) / q :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg q)
  refine ⟨hn, ?_⟩
  intro r hr
  rcases row_cases G ids d hcover hr with ht | ⟨v, hv, hvc⟩
  · apply (hg.2.2.1.2 r ht).trans
    apply Finset.sum_le_sum
    intro v _
    rw [solution_eq G ids hB hq d v]
    have hi : (0 : ℝ) ≤ GeneralCoveringTaskFractional.indicator (repairSet G d) v := by
      unfold GeneralCoveringTaskFractional.indicator
      split_ifs <;> norm_num
    linarith
  · have hv1 : (1 : ℝ) ≤ (((program ids L Δ a B k q hB).runEncoded G s v).1 : ℝ) / q := by
      rw [solution_eq G ids hB hq d v]
      have hb : (0 : ℝ) ≤ (base G ids L Δ a B k q hB s v : ℝ) / q :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg q)
      simp only [GeneralCoveringTaskFractional.indicator, if_pos hv]
      linarith
    exact hv1.trans (Finset.single_le_sum (s := d.cover r)
      (f := fun w => (((program ids L Δ a B k q hB).runEncoded G s w).1 : ℝ) / q) (fun w _ => hn w) hvc)

theorem objective_eq {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s) (c : V → ℝ) :
    CoveringOptimum.objective c (fun v => (((program ids L Δ a B k q hB).runEncoded G s v).1 : ℝ) / q) =
      CoveringOptimum.objective c (fun v => (base G ids L Δ a B k q hB s v : ℝ) / q) + ∑ v ∈ repairSet G d, c v := by
  calc
    _ = CoveringOptimum.objective c (fun v => (base G ids L Δ a B k q hB s v : ℝ) / q +
        GeneralCoveringTaskFractional.indicator (repairSet G d) v) :=
      congrArg (CoveringOptimum.objective c) (funext (fun v => solution_eq G ids hB hq d v))
    _ = CoveringOptimum.objective c (fun v => (base G ids L Δ a B k q hB s v : ℝ) / q) +
        CoveringOptimum.objective c (GeneralCoveringTaskFractional.indicator (repairSet G d)) := by
      unfold CoveringOptimum.objective
      simp_rw [mul_add]
      exact Finset.sum_add_distrib
    _ = _ := congrArg (fun t => CoveringOptimum.objective c
      (fun v => (base G ids L Δ a B k q hB s v : ℝ) / q) + t)
      (GeneralCoveringTaskFractional.indicator_objective c (repairSet G d))

/-- Additive cost uses actual marked centers and shared-partner-safe repair.
There is no assumption that a selected center C-covers itself. -/
theorem cost {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.cost.val) :
    CoveringOptimum.objective (fun v => ((s v).2.cost.val : ℝ))
      (fun v => (((program ids L Δ a B k q hB).runEncoded G s v).1 : ℝ) / q) ≤
      (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.cost.val : ℝ)) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card + (boundary G d).card) := by
  let I := marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G d)
  have hg := aggregate_spec G ids hB hq d hcover hadm ha hden ξ haccuracy hc
  have hb := hg.2.2.2.1.trans hg.2.2.2.2.1
  have hbounds : ∀ v ∈ CoveringSupport.admissible d.cover d.R, (0 : ℝ) ≤ (s v).2.cost.val ∧ ((s v).2.cost.val : ℝ) ≤ B := by
    intro v _
    constructor
    · exact Nat.cast_nonneg _
    · have hh : (s v).2.cost.val ≤ B := by have ht := (s v).2.cost.isLt; omega
      exact_mod_cast hh
  have hr := (GeneralCoveringOwnerRepair.cost G d.cover d.D d.R L B I (fun v => ((s v).2.cost.val : ℝ))
    ((marked_subset _ _ _).trans hadm) hbounds).2
  have hm : (I.card : ℝ) ≤ (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card + (boundary G d).card := by
    exact_mod_cast marked_card d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary G d)
  have hm' := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 2 * (B : ℝ) by positivity)
  rw [objective_eq G ids hB hq d]
  change _ + (∑ v ∈ GeneralCoveringOwnerRepair.selected G d.cover d.D d.R L I, ((s v).2.cost.val : ℝ)) ≤ _
  push_cast at hb hr hm' ⊢
  linarith

theorem spec {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.cost.val) :
    let out := (program ids L Δ a B k q hB).runEncoded G s
    let x := fun v => ((out v).1 : ℝ) / q
    SevenFoundation.feasible (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2.cost)) x ∧
    CoveringOptimum.objective (fun v => ((s v).2.cost.val : ℝ)) x ≤
      (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.cost.val : ℝ)) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card + (boundary G d).card) ∧
    (∀ v, (out v).2.2.2.2 = env G ids L Δ s v ∧ (out v).2.2.2.1 = (s v).2 ∧ (out v).2.2.2.2.metadata.owned.input = (s v).1) ∧
    (∀ v, (out v).1 ≤ max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + q) ∧
    (∀ v, (q : ℝ) * x v = (out v).1) := by
  dsimp only
  have hs := support G ids hB hq d hcover hadm ha hden ξ haccuracy hc
  refine ⟨GeneralCoveringFractionalCorrect.instance_feasible d.R d.cover (fun v => (s v).2.cost) _
    (feasible G ids hB hq d hcover hadm ha hden ξ haccuracy hc) ?_,
    cost G ids hB hq d hcover hadm ha hden ξ haccuracy hc, ?_, output_bound G ids L Δ a B k q hB s, ?_⟩
  · intro v hv
    rw [hs v hv]
    simp only [Nat.cast_zero, zero_div]
  · intro v
    exact ⟨env_retained G ids L Δ a B k q hB s v, fields_retained G ids L Δ a B k q hB s v,
      private_input_retained G ids L Δ a B k q hB s v⟩
  · intro v
    have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    field_simp [hqn]

theorem empty_demands {bits L Δ a k q B : ℕ} {s : V → NativeInput V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (hq : 1 ≤ q) (d : Original G L Δ k B s) (he : d.R = ∅)
    (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D) (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.cost.val) :
    ∀ v, ((program ids L Δ a B k q hB).runEncoded G s v).1 = 0 := by
  intro v
  exact support G ids hB hq d hcover hadm ha hden ξ haccuracy hc v (by simp [he, CoveringSupport.admissible])

theorem core_rounds {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) :
    (core ids L a B k q hB).rounds = RecursiveSearch.roundBound (4 * k) a (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 6 := by
  simp only [core, beforeProgram, aggregatePrepare, aggregateFinish, repairPrepare, finish, Program.rounds,
    ProgramMemory.rounds, GeneralCoveringTaskFractionalAggregate.rounds, GeneralCoveringOwnerRepair.core_rounds]
  omega

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a B k q hB).rounds = RecursiveSearch.roundBound (4 * k) a (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 16 := by
  simp only [program, Program.rounds, ProgramMemory.rounds, GeneralCoveringOwnerVirtualPrepare.rounds, core_rounds]
  omega

theorem core_maxBits {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) :
    (core ids L a B k q hB).maxBits = max (GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB).maxBits (bits + 1) := by
  simp only [core, beforeProgram, aggregatePrepare, aggregateFinish, repairPrepare, finish, Program.maxBits,
    ProgramMemory.maxBits, GeneralCoveringOwnerRepair.core_maxBits, Nat.zero_max, Nat.max_zero]

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a B k q hB).maxBits = max (GeneralCoveringOwnerVirtualPrepare.program ids L Δ).maxBits
      (max (GeneralCoveringTaskFractionalAggregate.program ids L a B k q hB).maxBits (bits + 1)) := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, core_maxBits]

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (L Δ a B k q : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    let K0 := max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B q
      (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 1) + 1))
    (program ids L Δ a B k q hB).maxBits ≤ max ((L + Δ + 3) * (c + 2)) (max K0 (c + 1)) * Nat.clog 2 (n + 2) := by
  dsimp only
  let K0 := max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B q
    (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 1) + 1))
  let K := max ((L + Δ + 3) * (c + 2)) (max K0 (c + 1))
  have hp := GeneralCoveringOwnerVirtualPrepare.logarithmic_bits ids L Δ n c hids
  have hg := (GeneralCoveringTaskFractionalAggregate.logarithmic_bits ids L a B k q hB n c hids).1
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : bits + 1 ≤ (c + 1) * Nat.clog 2 (n + 2) := by nlinarith
  have hA : (L + Δ + 3) * (c + 2) ≤ K := le_max_left _ _
  have hC : K0 ≤ K := (le_max_left K0 (c + 1)).trans (le_max_right _ _)
  have hD : c + 1 ≤ K := (le_max_right K0 (c + 1)).trans (le_max_right _ _)
  rw [maxBits_eq]
  exact max_le (hp.trans (Nat.mul_le_mul_right _ hA))
    (max_le (hg.trans (Nat.mul_le_mul_right _ hC)) (hb.trans (Nat.mul_le_mul_right _ hD)))
end Paper.GeneralCoveringTaskFractionalRepair

#print axioms Paper.GeneralCoveringTaskFractionalRepair.beforeProgram_run
#print axioms Paper.GeneralCoveringTaskFractionalRepair.run_core
#print axioms Paper.GeneralCoveringTaskFractionalRepair.before_eq
#print axioms Paper.GeneralCoveringTaskFractionalRepair.run_program
#print axioms Paper.GeneralCoveringTaskFractionalRepair.env_retained
#print axioms Paper.GeneralCoveringTaskFractionalRepair.fields_retained
#print axioms Paper.GeneralCoveringTaskFractionalRepair.private_input_retained
#print axioms Paper.GeneralCoveringTaskFractionalRepair.output_bound
#print axioms Paper.GeneralCoveringTaskFractionalRepair.marked_subset
#print axioms Paper.GeneralCoveringTaskFractionalRepair.marked_card
#print axioms Paper.GeneralCoveringTaskFractionalRepair.env_spec
#print axioms Paper.GeneralCoveringTaskFractionalRepair.geometry
#print axioms Paper.GeneralCoveringTaskFractionalRepair.mark_exact
#print axioms Paper.GeneralCoveringTaskFractionalRepair.repair_correct
#print axioms Paper.GeneralCoveringTaskFractionalRepair.output_eq
#print axioms Paper.GeneralCoveringTaskFractionalRepair.solution_eq
#print axioms Paper.GeneralCoveringTaskFractionalRepair.aggregate_spec
#print axioms Paper.GeneralCoveringTaskFractionalRepair.row_cases
#print axioms Paper.GeneralCoveringTaskFractionalRepair.repair_admissible
#print axioms Paper.GeneralCoveringTaskFractionalRepair.support
#print axioms Paper.GeneralCoveringTaskFractionalRepair.feasible
#print axioms Paper.GeneralCoveringTaskFractionalRepair.objective_eq
#print axioms Paper.GeneralCoveringTaskFractionalRepair.cost
#print axioms Paper.GeneralCoveringTaskFractionalRepair.spec
#print axioms Paper.GeneralCoveringTaskFractionalRepair.empty_demands
#print axioms Paper.GeneralCoveringTaskFractionalRepair.core_rounds
#print axioms Paper.GeneralCoveringTaskFractionalRepair.rounds
#print axioms Paper.GeneralCoveringTaskFractionalRepair.core_maxBits
#print axioms Paper.GeneralCoveringTaskFractionalRepair.maxBits_eq
#print axioms Paper.GeneralCoveringTaskFractionalRepair.logarithmic_bits
