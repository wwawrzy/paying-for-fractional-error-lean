import Paper.Solver.LocalSearch.GeneralCoveringTaskPhysicalAggregate
import Paper.Solver.LocalSearch.GeneralCoveringOwnerRepair

/-! Actual physical aggregate once, then the two-round optional-partner repair
CORE. Its mark is computed from retained center/high/low/interior fields.
All sets and original-data records below are proof-side only. Initializer
discharge, uniform epsilon parameters and the random branch remain separate. -/
namespace Paper.GeneralCoveringTaskPhysicalRepair
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringTaskPhysicalAggregate.Input V B
abbrev Before (V : Type) (B : ℕ) := GeneralCoveringTaskPhysicalAggregate.Output V B
abbrev Output (V : Type) (B : ℕ) := Bool × (GeneralCoveringOwnerRepair.Output V × Before V B)

def mark {B : ℕ} (s : Before V B) : Bool := s.2.2.metadata.owned.input.center &&
  (s.2.2.high || (s.2.2.low && !s.2.1.interior))

def repairInput {B : ℕ} (s : Before V B) : GeneralCoveringOwnerRepair.Input V := ⟨s.2.2, mark s⟩
def prepare (B : ℕ) : Program V (Before V B) (GeneralCoveringOwnerRepair.Input V × Before V B) :=
  .local (fun _ _ s => (repairInput s, s))
def finish (B : ℕ) : Program V (GeneralCoveringOwnerRepair.Output V × Before V B) (Output V B) :=
  .local (fun _ _ s => (s.2.1 || s.1.selected, (s.1, s.2)))

def program {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Output V B) :=
  .seq (GeneralCoveringTaskPhysicalAggregate.program ids L Δ a k t T B hB)
    (.seq (prepare B) (.seq (ProgramMemory.carry (X := Before V B) (GeneralCoveringOwnerRepair.core ids)) (finish B)))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

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

def before {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :=
  (GeneralCoveringTaskPhysicalAggregate.program ids L Δ a k t T B hB).runEncoded G s
def repairState {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :=
  (GeneralCoveringOwnerRepair.core ids).runEncoded G (fun v => repairInput (before G ids L Δ a k t T B hB s v))

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    (program ids L Δ a k t T B hB).runEncoded G s = fun v =>
      ((before G ids L Δ a k t T B hB s v).1 || (repairState G ids L Δ a k t T B hB s v).selected,
        (repairState G ids L Δ a k t T B hB s v, before G ids L Δ a k t T B hB s v)) :=
  compose_run G (GeneralCoveringTaskPhysicalAggregate.program ids L Δ a k t T B hB)
    (GeneralCoveringOwnerRepair.core ids) repairInput (fun r s => (s.1 || r.selected, (r, s))) s

theorem retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) (v : V) :
    ((program ids L Δ a k t T B hB).runEncoded G s v).2.2 = before G ids L Δ a k t T B hB s v := by rw [run_program]

theorem private_input_retained {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (v : V) :
    ((program ids L Δ a k t T B hB).runEncoded G (fun u => (input u, c u)) v).2.2.2.2.metadata.owned.input = input v :=
  (congrArg (fun x : Before V B => x.2.2.metadata.owned.input) (retained G ids L Δ a k t T B hB _ v)).trans
    (GeneralCoveringTaskPhysicalAggregate.private_input_retained G ids L Δ a k t T B hB input c v)

def output {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => ((program ids L Δ a k t T B hB).runEncoded G s v).1)

theorem output_union {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    output G ids L Δ a k t T B hB s = GeneralCoveringTaskPhysicalAggregate.output G ids L Δ a k t T B hB s ∪
      GeneralCoveringOwnerRepair.chosen (repairState G ids L Δ a k t T B hB s) := by
  ext v
  simp only [output, GeneralCoveringTaskPhysicalAggregate.output, GeneralCoveringOwnerRepair.chosen,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, run_program, Bool.or_eq_true, before]

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _
private noncomputable local instance cutAdj {W : Type} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (S : Finset W) (P : Finset (Finset W)) :
    DecidableRel (PartCut.graph J S P).Adj := fun _ _ => Classical.propDecidable _

/-- Only original private input interpretation and k,t positivity. No masks,
partition, output inequality or computed geometric fields are supplied. -/
structure Original (k t B : ℕ) (s : V → Input V B) where
  cover : V → Finset V
  targets : V → Finset V
  D : Finset V
  R : Finset V
  hk : 0 < k
  ht : 0 < t
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  local_rows : ∀ r ∈ R, cover r ⊆ closed G r
  center : ∀ v, (s v).1.center = decide (v ∈ D)
  demand : ∀ v, (s v).1.demand = decide (v ∈ R)
  candidates : ∀ v, (s v).1.candidates = cover v
  inverse : ∀ v, (s v).1.targets = targets v

noncomputable def boundary {bits L Δ k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (d : Original G k t B s) :=
  BoundaryOwners.vertices (graph G d.cover d.D d.R L (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
    Finset.univ (GeneralCoveringTaskPhysicalMarks.partition G ids d.cover d.D d.R L Δ k t T d.hk d.ht).parts

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

private theorem interior_of_eq {B : ℕ} {x y : GeneralCoveringTaskRoles.Fields V B} {b : Bool}
    (he : x = y) (hy : y.interior = b) : x.interior = b :=
  (congrArg (fun f : GeneralCoveringTaskRoles.Fields V B => f.interior) he).trans hy

theorem mark_exact {bits L Δ a k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G k t B s) (v : V) :
    mark (before G ids L Δ a k t T B hB s v) = decide (v ∈ marked d.D
      (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ) (boundary (L := L) (Δ := Δ) (T := T) G ids d)) := by
  let input := fun v => (s v).1
  let c := fun v => (s v).2
  let E := GeneralCoveringOwnerSimulation.learned G ids L Δ input
  have he (v : V) := GeneralCoveringTaskPhysicalAggregate.env_retained G ids L Δ a k t T B hB input c v
  have hp := GeneralCoveringTaskPhysicalMarks.fields_spec G ids L Δ k t T B d.hk d.ht d.cover d.targets d.D d.R
    d.incidence d.local_rows input c d.center d.demand d.candidates d.inverse
  have hInterior := hp.2.2.2.1
  have hinput : (fun u => (input u, c u)) = s := by funext u; rfl
  rw [hinput] at hInterior
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  have hf := GeneralCoveringOwnerHighCount.learned_flags G ids d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  apply local_mark d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)
    (boundary (L := L) (Δ := Δ) (T := T) G ids d) (before G ids L Δ a k t T B hB s)
  · intro u
    exact (congrArg GeneralCoveringOwners.Input.center
      (GeneralCoveringTaskPhysicalAggregate.private_input_retained G ids L Δ a k t T B hB input c u)).trans (d.center u)
  · intro u
    apply (congrArg GeneralCoveringOwnerVirtualPrepare.Env.high (he u)).trans
    apply bool_of_iff
    have hiff := (GeneralCoveringOwnerHighCount.mem_flagged E u).symm
    rw [hf] at hiff
    exact hiff
  · intro u
    exact (congrArg GeneralCoveringOwnerVirtualPrepare.Env.low (he u)).trans (hs.2.2.1 u)
  · intro i
    exact interior_of_eq
      (GeneralCoveringTaskPhysicalAggregate.fields_retained G ids L Δ a k t T B hB s i.val.val) (hInterior i)

theorem repair_correct {bits L Δ a k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G k t B s) :
    repairState G ids L Δ a k t T B hB s = GeneralCoveringOwnerRepair.expected G
      (fun v => (before G ids L Δ a k t T B hB s v).2.2) d.cover d.D d.R L
      (marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)
        (boundary (L := L) (Δ := Δ) (T := T) G ids d)) := by
  let input := fun v => (s v).1
  let c := fun v => (s v).2
  have hs := GeneralCoveringOwnerSimulation.learned_spec G ids d.cover d.targets d.D d.R L Δ
    d.incidence d.local_rows input d.center d.demand d.candidates d.inverse
  have hm (v : V) : (before G ids L Δ a k t T B hB s v).2.2.metadata =
      GeneralCoveringOwnerDiscoveryCorrect.metadata G d.cover d.D d.R L input v :=
    (congrArg GeneralCoveringOwnerVirtualPrepare.Env.metadata
      (GeneralCoveringTaskPhysicalAggregate.env_retained G ids L Δ a k t T B hB input c v)).trans (hs.1 v)
  apply GeneralCoveringOwnerRepair.core_correct G ids d.cover d.D d.R L _ (marked_subset _ _ _)
    (fun v => (before G ids L Δ a k t T B hB s v).2.2) (fun v => mark (before G ids L Δ a k t T B hB s v))
  · intro v
    exact (congrArg GeneralCoveringOwners.Input.center
      (GeneralCoveringTaskPhysicalAggregate.private_input_retained G ids L Δ a k t T B hB input c v)).trans (d.center v)
  · intro v
    exact congrArg GeneralCoveringOwnerSupport.State.residual (hm v)
  · intro v
    exact (congrArg (fun m : GeneralCoveringOwnerSupport.State V => m.owned.input.candidates) (hm v)).trans (d.candidates v)
  · intro v
    exact congrArg GeneralCoveringOwnerSupport.State.heavy (hm v)
  · exact mark_exact G ids hB d
  · exact d.local_rows

theorem output_exact {bits L Δ a k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G k t B s) :
    output G ids L Δ a k t T B hB s = GeneralCoveringTaskPhysicalAggregate.output G ids L Δ a k t T B hB s ∪
      GeneralCoveringOwnerRepair.selected G d.cover d.D d.R L
        (marked d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)
          (boundary (L := L) (Δ := Δ) (T := T) G ids d)) := by
  rw [output_union, repair_correct G ids hB d, GeneralCoveringOwnerRepair.chosen_expected]

theorem boundary_count {bits L Δ k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (d : Original G k t B s) :
    (boundary (L := L) (Δ := Δ) (T := T) G ids d).card ≤
      2 * (PartCut.graph (graph G d.cover d.D d.R L (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
        Finset.univ (GeneralCoveringTaskPhysicalMarks.partition G ids d.cover d.D d.R L Δ k t T d.hk d.ht).parts).edgeFinset.card :=
  BoundaryOwners.count _ _ _

theorem covers {bits L Δ a k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G k t B s) (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val) :
    output G ids L Δ a k t T B hB s ⊆ CoveringSupport.admissible d.cover d.R ∧
      GeneralCoveringNormalizedIntegral.Covers d.cover d.R (output G ids L Δ a k t T B hB s) := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
  let P := GeneralCoveringTaskPhysicalMarks.partition G ids d.cover d.D d.R L Δ k t T d.hk d.ht
  let Bdy := boundary (L := L) (Δ := Δ) (T := T) G ids d
  let I := marked d.D Q Bdy
  have hiD : I ⊆ d.D := marked_subset _ _ _
  have hg := GeneralCoveringTaskPhysicalAggregate.spec G ids L Δ a k t T B hB d.hk d.ht d.cover d.targets d.D d.R
    d.incidence d.local_rows hcover hadm ha hden (fun v => (s v).1) (fun v => (s v).2)
    d.center d.demand d.candidates d.inverse hc
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

theorem cost {bits L Δ a k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G k t B s) (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val)
    (W : Finset V) (hWadm : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) :
    (∑ v ∈ output G ids L Δ a k t T B hB s, (s v).2.val) ≤ (∑ v ∈ W, (s v).2.val) +
      B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card +
        (boundary (L := L) (Δ := Δ) (T := T) G ids d).card) := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ
  let Bdy := boundary (L := L) (Δ := Δ) (T := T) G ids d
  let I := marked d.D Q Bdy
  let A := GeneralCoveringTaskPhysicalAggregate.output G ids L Δ a k t T B hB s
  let Z := GeneralCoveringOwnerRepair.selected G d.cover d.D d.R L I
  have hg := GeneralCoveringTaskPhysicalAggregate.spec G ids L Δ a k t T B hB d.hk d.ht d.cover d.targets d.D d.R
    d.incidence d.local_rows hcover hadm ha hden (fun v => (s v).1) (fun v => (s v).2)
    d.center d.demand d.candidates d.inverse hc
  have hb : ∀ v ∈ CoveringSupport.admissible d.cover d.R, (0 : ℝ) ≤ (s v).2.val ∧ ((s v).2.val : ℝ) ≤ B := by
    intro v _
    constructor
    · exact Nat.cast_nonneg _
    · have hh : (s v).2.val ≤ B := by have h := (s v).2.isLt; omega
      exact_mod_cast hh
  have hr := (GeneralCoveringOwnerRepair.cost G d.cover d.D d.R L B I (fun v => ((s v).2.val : ℝ))
    ((marked_subset _ _ _).trans hadm) hb).2
  have hn : (∑ v ∈ Z, (s v).2.val) ≤ B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * I.card := by
    exact_mod_cast hr
  have hm : 2 * B * I.card ≤ 2 * B * (Q.card + Bdy.card) :=
    Nat.mul_le_mul_left (2 * B) (marked_card d.D Q Bdy)
  have hu := Finset.sum_union_inter (s₁ := A) (s₂ := Z) (f := fun v => (s v).2.val)
  have hinput : (fun v => ((s v).1, (s v).2)) = s := by funext v; rfl
  have haCost : (∑ v ∈ A, (s v).2.val) ≤ ∑ v ∈ W, (s v).2.val := by
    simpa only [hinput] using hg.2.2.2 W hWadm hW
  have huBound : (∑ v ∈ A ∪ Z, (s v).2.val) ≤ (∑ v ∈ A, (s v).2.val) + ∑ v ∈ Z, (s v).2.val := by
    omega
  rw [output_exact G ids hB d]
  change (∑ v ∈ A ∪ Z, (s v).2.val) ≤ (∑ v ∈ W, (s v).2.val) +
    B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * (Q.card + Bdy.card)
  calc
    _ ≤ (∑ v ∈ A, (s v).2.val) + ∑ v ∈ Z, (s v).2.val := huBound
    _ ≤ (∑ v ∈ W, (s v).2.val) +
        (B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * I.card) := Nat.add_le_add haCost hn
    _ = (∑ v ∈ W, (s v).2.val) + B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card + 2 * B * I.card :=
      (Nat.add_assoc _ _ _).symm
    _ ≤ _ := Nat.add_le_add_left hm _

theorem cost_crossing {bits L Δ a k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G k t B s) (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val)
    (W : Finset V) (hWadm : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) :
    (∑ v ∈ output G ids L Δ a k t T B hB s, (s v).2.val) ≤ (∑ v ∈ W, (s v).2.val) +
      B * (GeneralCoveringOwnerSupport.heavy G d.cover d.D d.R L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card +
        2 * (PartCut.graph (graph G d.cover d.D d.R L (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))
          Finset.univ (GeneralCoveringTaskPhysicalMarks.partition G ids d.cover d.D d.R L Δ k t T d.hk d.ht).parts).edgeFinset.card) := by
  have hh := cost (L := L) (Δ := Δ) (a := a) (T := T) G ids hB d hcover hadm ha hden hc W hWadm hW
  have hb := boundary_count (L := L) (Δ := Δ) (T := T) G ids d
  have hm := Nat.mul_le_mul_left (2 * B)
    (Nat.add_le_add_left hb (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ).card)
  exact hh.trans (Nat.add_le_add_left hm _)

theorem empty_demands {bits L Δ a k t T B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (hB : 1 ≤ B)
    (d : Original G k t B s) (hR : d.R = ∅) (hcover : GeneralCoveringInitializerPass.Covers d.cover d.R d.D)
    (hadm : d.D ⊆ CoveringSupport.admissible d.cover d.R) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val) : output G ids L Δ a k t T B hB s = ∅ := by
  have hs := (covers (L := L) (Δ := Δ) (a := a) (T := T) G ids hB d hcover hadm ha hden hc).1
  have he : output G ids L Δ a k t T B hB s ⊆ ∅ := by
    simpa only [hR, CoveringSupport.admissible, Finset.biUnion_empty] using hs
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (he hv))

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    output G ids L Δ a k t T B hB s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun v => isEmptyElim v)

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t T B hB).rounds = (GeneralCoveringTaskPhysicalAggregate.program ids L Δ a k t T B hB).rounds + 2 := by
  simp only [program, prepare, finish, Program.rounds, ProgramMemory.rounds, GeneralCoveringOwnerRepair.core_rounds,
    Nat.zero_add, Nat.add_zero]

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B : ℕ) (hB : 1 ≤ B) :
    (program ids L Δ a k t T B hB).maxBits = max (GeneralCoveringTaskPhysicalAggregate.program ids L Δ a k t T B hB).maxBits (bits + 1) := by
  simp only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits, GeneralCoveringOwnerRepair.core_maxBits,
    Nat.zero_max, Nat.max_zero]

def roundCoefficient (L Δ a k T B c p d : ℕ) := GeneralCoveringTaskPhysicalAggregate.roundCoefficient L Δ a k T B c p d + 2
def bitCoefficient (L Δ a k B c p d : ℕ) := max (GeneralCoveringTaskPhysicalAggregate.bitCoefficient L Δ a k B c p d)
  (DeterministicColorReductionIdentifiers.bitFactor c p d + 1)

theorem costs {bits : ℕ} (ids : BitCode V bits) (L Δ a k t T B c p d M : ℕ) (hB : 1 ≤ B)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program ids L Δ a k t T B hB).rounds ≤ roundCoefficient L Δ a k T B c p d *
      (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
    (program ids L Δ a k t T B hB).maxBits ≤ bitCoefficient L Δ a k B c p d * Nat.clog 2 (Fintype.card V + 2) := by
  have hp := GeneralCoveringTaskPhysicalAggregate.costs ids L Δ a k t T B c p d M hB hbits hM
  have hi := DeterministicColorReductionIdentifiers.public_length_bound (Fintype.card V) bits c p d M hbits hM
  have hb := (BroadcastModel.logarithmic_message_budget (Fintype.card V) bits
    (DeterministicColorReductionIdentifiers.bitFactor c p d) hi).1
  constructor
  · rw [rounds]
    unfold roundCoefficient
    nlinarith [hp.1]
  · rw [maxBits]
    simpa only [bitCoefficient, Nat.mul_max_mul_right] using max_le_max hp.2 hb

end Paper.GeneralCoveringTaskPhysicalRepair

#print axioms Paper.GeneralCoveringTaskPhysicalRepair.run_program
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.retained
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.private_input_retained
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.output_union
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.marked_subset
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.marked_card
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.mark_exact
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.repair_correct
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.output_exact
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.boundary_count
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.covers
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.cost
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.cost_crossing
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.empty_demands
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.empty_physical
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.rounds
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.maxBits
#print axioms Paper.GeneralCoveringTaskPhysicalRepair.costs
