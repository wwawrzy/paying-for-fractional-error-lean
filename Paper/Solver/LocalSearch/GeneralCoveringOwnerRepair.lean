import Paper.Solver.LocalSearch.GeneralCoveringOwnerHighCount
import Paper.Solver.LocalSearch.GeneralCoveringHeavyCount

/-! Physical repair of heavy rows and marked owner classes, including
optional C-partners. The reusable core takes only private Env/local mark bits,
uses Partners.attach ONCE and one Option-addressed request broadcast. The
native high entry computes Env once and takes marks from its actual high bit.
All finite global sets below are proof-side descriptions of these local bits. -/
namespace Paper.GeneralCoveringOwnerRepair
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

structure Input (V : Type) where
  env : GeneralCoveringOwnerVirtualPrepare.Env V
  mark : Bool

structure State (V : Type) where
  env : GeneralCoveringOwnerVirtualPrepare.Env V
  marked : Bool
  partner : Option V

structure Output (V : Type) where
  env : GeneralCoveringOwnerVirtualPrepare.Env V
  heavy : Bool
  marked : Bool
  partner : Option V
  requested : Bool
  selected : Bool

def message (s : State V) : Option V := if s.marked then s.partner else none

def assemble (s : State V) (req : Bool) : Output V :=
  ⟨s.env, s.env.metadata.heavy, s.marked, s.partner, req, (s.env.metadata.heavy || s.marked || req)⟩

def requestRound : Round V (State V) (Output V) (Option V) where
  send _ _ s := message s
  update v N s msg := assemble s (decide (v ∈ MaskedMinimum.pool N (message s) msg))

def requestProgram {b : ℕ} (ids : BitCode V b) : Program V (State V) (Output V) :=
  .broadcast (b + 1) ids.option requestRound

def prepare : Program V (Input V) (GeneralCoveringOwnerSupport.State V × Input V) :=
  .local fun _ _ s => (s.env.metadata, s)

def toState : Program V (GeneralCoveringPartners.Output V × Input V) (State V) :=
  .local fun _ _ s => ⟨s.2.env, s.2.mark && s.2.env.metadata.owned.input.center, s.1.partner⟩

/-- INTERMEDIATE local-mark core. No global marked set is supplied to code. -/
def core {b : ℕ} (ids : BitCode V b) : Program V (Input V) (Output V) :=
  .seq prepare (.seq (ProgramMemory.carry GeneralCoveringPartners.attach) (.seq toState (requestProgram ids)))

/-- Native high-only entry: original private incidence input, one actual
preparation, computed high marks, then two physical repair rounds. -/
def program {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) : Program V (GeneralCoveringOwners.Input V) (Output V) :=
  .seq (GeneralCoveringOwnerVirtualPrepare.program ids L Δ)
    (.seq (.local fun _ _ e => (⟨e, e.high⟩ : Input V)) (core ids))

theorem core_rounds {b : ℕ} (ids : BitCode V b) : (core ids).rounds = 2 := rfl

theorem rounds {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) : (program ids L Δ).rounds = 12 := rfl

theorem core_maxBits {b : ℕ} (ids : BitCode V b) : (core ids).maxBits = b + 1 := by
  change max 0 (max 1 (max 0 (b + 1))) = b + 1
  omega

theorem maxBits {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) :
    (program ids L Δ).maxBits ≤ (L + Δ + 3) * (b + 2) := by
  simp only [program, Program.maxBits, core_maxBits, Nat.zero_max]
  apply max_le
  · exact GeneralCoveringOwnerVirtualPrepare.maxBits ids L Δ
  · nlinarith

theorem logarithmic_bits {b : ℕ} (ids : BitCode V b) (L Δ n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program ids L Δ).maxBits ≤ ((L + Δ + 3) * (c + 2)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + 2 ≤ (c + 2) * Nat.clog 2 (n + 2) := by nlinarith
  exact (maxBits ids L Δ).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def requested (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V) : Finset V :=
  I.biUnion (fun i => (GeneralCoveringPartners.partner G C D R L i).toFinset)

noncomputable def selected (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V) : Finset V :=
  (GeneralCoveringOwnerSupport.heavy G C D R L ∪ I) ∪ requested G C D R L I

noncomputable def expected (E : V → GeneralCoveringOwnerVirtualPrepare.Env V)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V) (v : V) : Output V :=
  ⟨E v, decide (v ∈ GeneralCoveringOwnerSupport.heavy G C D R L), decide (v ∈ I),
    GeneralCoveringPartners.partner G C D R L v, decide (v ∈ requested G C D R L I),
    decide (v ∈ selected G C D R L I)⟩

theorem mem_requested (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V) (v : V) :
    v ∈ requested G C D R L I ↔ ∃ i ∈ I, GeneralCoveringPartners.partner G C D R L i = some v := by
  constructor
  · intro hv
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hv
    exact ⟨i, hi, by simpa using hp⟩
  · rintro ⟨i, hi, hp⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [hp]⟩

theorem requested_card (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V) :
    (requested G C D R L I).card ≤ I.card := by
  calc
    _ ≤ ∑ i ∈ I, (GeneralCoveringPartners.partner G C D R L i).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, 1 := Finset.sum_le_sum (fun i _ => by
      cases hp : GeneralCoveringPartners.partner G C D R L i <;> simp [hp])
    _ = _ := by simp

theorem selected_card (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V) :
    (selected G C D R L I).card ≤ (GeneralCoveringOwnerSupport.heavy G C D R L).card + 2 * I.card := by
  have h1 := Finset.card_union_le (GeneralCoveringOwnerSupport.heavy G C D R L) I
  have h2 := Finset.card_union_le (GeneralCoveringOwnerSupport.heavy G C D R L ∪ I) (requested G C D R L I)
  have h3 := requested_card G C D R L I
  change ((GeneralCoveringOwnerSupport.heavy G C D R L ∪ I) ∪ requested G C D R L I).card ≤ _
  omega

theorem admissible (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V)
    (hI : I ⊆ CoveringSupport.admissible C R) : selected G C D R L I ⊆ CoveringSupport.admissible C R := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp hv with hv | hv
    · exact GeneralCoveringOwnerSupport.heavy_admissible G C D R L hv
    · exact hI hv
  · obtain ⟨i, _, hp⟩ := (mem_requested G C D R L I v).mp hv
    exact (GeneralCoveringPartners.light_admissible G C D R L hp).1

theorem bundle_subset (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V)
    {i : V} (hi : i ∈ I) : GeneralCoveringPartners.bundle G C D R L i ⊆ selected G C D R L I := by
  intro v hv
  rcases Finset.mem_union.mp hv with he | hp
  · have heq : v = i := Finset.mem_singleton.mp he
    subst v
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hp⟩)

theorem covers_class (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V)
    (hI : I ⊆ D) (hcover : GeneralCoveringInitializerPass.Covers C R D)
    {r i : V} (hr : r ∈ GeneralCoveringOwnerSupport.residual G C D R L)
    (hi : i ∈ I) (ho : GeneralCoveringOwners.owner C D R r = some i) :
    ∃ v ∈ selected G C D R L I, v ∈ C r := by
  obtain ⟨v, hv, hvC⟩ := GeneralCoveringPartners.bundle_covers G C D R L hcover (hI hi) hr ho
  exact ⟨v, bundle_subset G C D R L I hi hv, hvC⟩

theorem covers_heavy_row (C : V → Finset V) (D R : Finset V) (L : ℕ) (I : Finset V)
    {r : V} (hr : r ∈ R) (hn : r ∉ GeneralCoveringOwnerSupport.residual G C D R L) :
    ∃ v ∈ selected G C D R L I, v ∈ C r := by
  have he : C r ∩ GeneralCoveringOwnerSupport.heavy G C D R L ≠ ∅ := by
    intro he
    exact hn (Finset.mem_filter.mpr ⟨hr, he⟩)
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  exact ⟨v, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mp hv).2), (Finset.mem_inter.mp hv).1⟩

/-- Partner occurrences are charged once per marked owner BEFORE duplicate
physical selections are merged; hence shared partners never undercharge. -/
theorem cost (C : V → Finset V) (D R : Finset V) (L B : ℕ) (I : Finset V) (c : V → ℝ)
    (hI : I ⊆ CoveringSupport.admissible C R)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v ∧ c v ≤ B) :
    0 ≤ (∑ v ∈ selected G C D R L I, c v) ∧
    (∑ v ∈ selected G C D R L I, c v) ≤
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G C D R L).card + 2 * B * I.card := by
  refine ⟨Finset.sum_nonneg (fun v hv => (hc v (admissible G C D R L I hI hv)).1), ?_⟩
  calc
    _ ≤ ∑ _v ∈ selected G C D R L I, (B : ℝ) :=
      Finset.sum_le_sum (fun v hv => (hc v (admissible G C D R L I hI hv)).2)
    _ = (B : ℝ) * (selected G C D R L I).card := by simp [mul_comm]
    _ ≤ (B : ℝ) * ((GeneralCoveringOwnerSupport.heavy G C D R L).card + 2 * I.card) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast selected_card G C D R L I) (Nat.cast_nonneg B)
    _ = _ := by ring

theorem run_core {b : ℕ} (ids : BitCode V b) (s : V → Input V) :
    (core ids).run G s = (requestProgram ids).run G (fun v =>
      ⟨(s v).env, (s v).mark && (s v).env.metadata.owned.input.center,
        (GeneralCoveringPartners.attach.run G (fun u => (s u).env.metadata) v).partner⟩) := by
  change (requestProgram ids).run G (toState.run G
    ((ProgramMemory.carry GeneralCoveringPartners.attach).run G (fun v => ((s v).env.metadata, s v)))) = _
  rw [ProgramMemory.run G GeneralCoveringPartners.attach]
  rfl

theorem request_correct {b : ℕ} (ids : BitCode V b) (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (I : Finset V) (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) (s : V → State V)
    (he : ∀ v, (s v).env = E v) (hm : ∀ v, (s v).marked = decide (v ∈ I))
    (hp : ∀ v, (s v).partner = GeneralCoveringPartners.partner G C D R L v)
    (hh : ∀ v, (E v).metadata.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G C D R L))
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    (requestProgram ids).run G s = expected G E C D R L I := by
  have hmsg (r v : V) : message (s r) = some v ↔ r ∈ I ∧ GeneralCoveringPartners.partner G C D R L r = some v := by
    unfold message
    rw [hm r, hp r]
    by_cases hr : r ∈ I <;> simp [hr]
  have horigin (r v : V) (h : message (s r) = some v) : v ∈ requested G C D R L I := by
    obtain ⟨hr, hp⟩ := (hmsg r v).mp h
    exact (mem_requested G C D R L I v).mpr ⟨r, hr, hp⟩
  funext v
  have hpool : v ∈ MaskedMinimum.pool (G.neighborFinset v) (message (s v))
      (fun u => message (s u.val)) ↔ v ∈ requested G C D R L I := by
    constructor
    · exact MaskedMinimum.pool_origin _ _ _ (fun z => z ∈ requested G C D R L I)
        (horigin v) (fun u => horigin u.val)
    · intro hv
      obtain ⟨r, hr, hp⟩ := (mem_requested G C D R L I v).mp hv
      have hsend := (hmsg r v).mpr ⟨hr, hp⟩
      have hadj := GeneralCoveringPartners.adjacent G C D R L hlocal hp
      exact MaskedMinimum.mem_pool_incoming _ _ _
        ⟨r, (G.mem_neighborFinset v r).mpr hadj.symm⟩ hsend
  change assemble (s v) (decide (v ∈ MaskedMinimum.pool (G.neighborFinset v)
    (message (s v)) (fun u => message (s u.val)))) = _
  have hb : decide (v ∈ MaskedMinimum.pool (G.neighborFinset v) (message (s v))
      (fun u => message (s u.val))) = decide (v ∈ requested G C D R L I) := Bool.decide_congr hpool
  rw [hb]
  unfold assemble expected
  rw [he v, hm v, hp v, hh v]
  apply congrArg (fun sel => Output.mk (E v) (decide (v ∈ GeneralCoveringOwnerSupport.heavy G C D R L))
    (decide (v ∈ I)) (GeneralCoveringPartners.partner G C D R L v)
    (decide (v ∈ requested G C D R L I)) sel)
  simp only [← Bool.decide_or]
  apply Bool.decide_congr
  simp only [selected, Finset.mem_union]

/-- Intermediate exact contract for already-computed metadata and private
mark bits. The high-only native entry below DERIVES all these field facts. -/
theorem core_correct {b : ℕ} (ids : BitCode V b) (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (I : Finset V) (hI : I ⊆ D) (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) (m : V → Bool)
    (hD : ∀ v, (E v).metadata.owned.input.center = decide (v ∈ D))
    (hr : ∀ v, (E v).metadata.residual = decide (v ∈ GeneralCoveringOwnerSupport.residual G C D R L))
    (hC : ∀ v, (E v).metadata.owned.input.candidates = C v)
    (hh : ∀ v, (E v).metadata.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G C D R L))
    (hm : ∀ v, m v = decide (v ∈ I)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    (core ids).runEncoded G (fun v => ⟨E v, m v⟩) = expected G E C D R L I := by
  have hp := GeneralCoveringPartners.attach_correct G C D R L (fun v => (E v).metadata) hD hr hC hlocal
  rw [Program.runEncoded_eq_run, run_core]
  dsimp only
  rw [hp]
  apply request_correct G ids C D R L I E _ (fun _ => rfl) _ (fun _ => rfl) hh hlocal
  intro v
  change (m v && (E v).metadata.owned.input.center) = decide (v ∈ I)
  rw [hm v, hD v]
  by_cases hv : v ∈ I
  · simp [hv, hI hv]
  · simp [hv]

theorem high_run {b : ℕ} (ids : BitCode V b) (L Δ : ℕ) (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ).runEncoded G input = (core ids).runEncoded G (fun v =>
      ⟨GeneralCoveringOwnerSimulation.learned G ids L Δ input v,
        (GeneralCoveringOwnerSimulation.learned G ids L Δ input v).high⟩) := by
  have he := (GeneralCoveringOwnerSimulation.learned_eq_run G ids L Δ input).symm
  calc
    _ = (core ids).run G (fun v =>
        ⟨(GeneralCoveringOwnerVirtualPrepare.program ids L Δ).run G input v,
          ((GeneralCoveringOwnerVirtualPrepare.program ids L Δ).run G input v).high⟩) :=
      Program.runEncoded_eq_run G (program ids L Δ) input
    _ = (core ids).run G (fun v =>
        ⟨GeneralCoveringOwnerSimulation.learned G ids L Δ input v,
          (GeneralCoveringOwnerSimulation.learned G ids L Δ input v).high⟩) := by simp only [he]
    _ = _ := (Program.runEncoded_eq_run G (core ids) _).symm

/-- Native high-only encoded program, with NO supplied marks/metadata/partner
oracle. No C-cover is needed to compute or identify this exact output. -/
theorem high_correct {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) :
    (program ids L Δ).runEncoded G input = expected G (GeneralCoveringOwnerSimulation.learned G ids L Δ input)
      C D R L (GeneralCoveringOwnerHighCount.physicalHigh G C D R L Δ) := by
  let E := GeneralCoveringOwnerSimulation.learned G ids L Δ input
  let I := GeneralCoveringOwnerHighCount.physicalHigh G C D R L Δ
  have hs := GeneralCoveringOwnerVirtualPrepare.private_correct G ids C targets D R L Δ
    hinc hlocal input hD hR hC hTargets
  have hm (v : V) : (E v).metadata = GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L input v := (hs.1 v).1
  have hi (v : V) : (E v).metadata.owned.input = input v := (hs.1 v).2.1
  have hd (v : V) : (E v).metadata.owned.input.center = decide (v ∈ D) :=
    (congrArg GeneralCoveringOwners.Input.center (hi v)).trans (hD v)
  have hc (v : V) : (E v).metadata.owned.input.candidates = C v :=
    (congrArg GeneralCoveringOwners.Input.candidates (hi v)).trans (hC v)
  have hr (v : V) : (E v).metadata.residual = decide (v ∈ GeneralCoveringOwnerSupport.residual G C D R L) := by
    simpa only [GeneralCoveringOwnerDiscoveryCorrect.metadata, GeneralCoveringOwnerSupport.expected] using
      congrArg GeneralCoveringOwnerSupport.State.residual (hm v)
  have hh (v : V) : (E v).metadata.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G C D R L) := by
    simpa only [GeneralCoveringOwnerDiscoveryCorrect.metadata, GeneralCoveringOwnerSupport.expected] using
      congrArg GeneralCoveringOwnerSupport.State.heavy (hm v)
  have hf : GeneralCoveringOwnerHighCount.flagged E = I :=
    GeneralCoveringOwnerHighCount.learned_flags G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets
  have hmark (v : V) : (E v).high = decide (v ∈ I) := by
    rw [← hf]
    cases hv : (E v).high <;> simp [GeneralCoveringOwnerHighCount.flagged, hv]
  rw [high_run]
  exact core_correct G ids C D R L I (GeneralCoveringOwnerHighCount.physicalHigh_subset G C D R L Δ)
    E (fun v => (E v).high) hd hr hc hh hmark hlocal

/-- Proof-side set of actual output selection bits. -/
def chosen (out : V → Output V) : Finset V := Finset.univ.filter (fun v => (out v).selected = true)

theorem chosen_expected (E : V → GeneralCoveringOwnerVirtualPrepare.Env V) (C : V → Finset V)
    (D R : Finset V) (L : ℕ) (I : Finset V) :
    chosen (expected G E C D R L I) = selected G C D R L I := by
  ext v
  simp [chosen, expected]

theorem chosen_correct {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) :
    chosen ((program ids L Δ).runEncoded G input) =
      selected G C D R L (GeneralCoveringOwnerHighCount.physicalHigh G C D R L Δ) := by
  rw [high_correct G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets]
  exact chosen_expected G _ C D R L _

/-- Physical selections cover heavy-hit rows and every residual demand
whose actual owner is high, INCLUDING a center without C-self-incidence.
The genuine initializer C-cover is used only for this coverage assertion. -/
theorem high_spec {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ B : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) (hDad : D ⊆ CoveringSupport.admissible C R)
    (c : V → ℝ) (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v ∧ c v ≤ B) :
    let out := (program ids L Δ).runEncoded G input
    (∀ v, (out v).env = GeneralCoveringOwnerSimulation.learned G ids L Δ input v ∧
      (out v).env.metadata.owned.input = input v) ∧
    chosen out = selected G C D R L (GeneralCoveringOwnerHighCount.physicalHigh G C D R L Δ) ∧
    chosen out ⊆ CoveringSupport.admissible C R ∧
    (∀ r ∈ R, r ∉ GeneralCoveringOwnerSupport.residual G C D R L ∨
        (∃ i ∈ GeneralCoveringOwnerHighCount.physicalHigh G C D R L Δ, GeneralCoveringOwners.owner C D R r = some i) →
      ∃ v ∈ chosen out, v ∈ C r) ∧
    (∑ v ∈ chosen out, c v) ≤ (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G C D R L).card +
      2 * B * (GeneralCoveringOwnerHighCount.physicalHigh G C D R L Δ).card := by
  have hout := high_correct G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets
  have hchosen := chosen_correct G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets
  have hI := GeneralCoveringOwnerHighCount.physicalHigh_subset G C D R L Δ
  have had := GeneralCoveringOwnerHighCount.admissible G C D R L Δ hDad
  dsimp only
  refine ⟨?_, hchosen, ?_, ?_, ?_⟩
  · intro v
    rw [hout]
    exact ⟨rfl, GeneralCoveringOwnerVirtualPrepare.private_input_retained G ids L Δ input v⟩
  · rw [hchosen]
    exact admissible G C D R L _ had
  · rw [hchosen]
    intro r hr hcase
    by_cases hres : r ∈ GeneralCoveringOwnerSupport.residual G C D R L
    · rcases hcase with hn | ⟨i, hi, ho⟩
      · exact False.elim (hn hres)
      · exact covers_class G C D R L _ hI hcover hres hi ho
    · exact covers_heavy_row G C D R L _ hr hres
  · rw [hchosen]
    exact (cost G C D R L B _ c had hc).2

/-- Native weighted repair bound from BOTH accepted physical density counts.
Shared partners are still charged per high owner; no C-cover is needed here. -/
theorem high_cost_density {b : ℕ} (ids : BitCode V b) (C targets : V → Finset V) (D R : Finset V) (L Δ B : ℕ)
    {a : ℝ} (ha : 1 ≤ a) (hL : 4 * a ≤ (L : ℝ)) (hΔ : 0 < Δ) (hden : MinorDensity.Bound G a)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (input : V → GeneralCoveringOwners.Input V) (hD : ∀ v, (input v).center = decide (v ∈ D))
    (hR : ∀ v, (input v).demand = decide (v ∈ R)) (hC : ∀ v, (input v).candidates = C v)
    (hTargets : ∀ v, (input v).targets = targets v) (hDad : D ⊆ CoveringSupport.admissible C R)
    (c : V → ℝ) (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v ∧ c v ≤ B) :
    (∑ v ∈ chosen ((program ids L Δ).runEncoded G input), c v) ≤
      (B : ℝ) * (2 * a * D.card / L) +
        2 * B * (2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card / Δ) := by
  rw [chosen_correct G ids C targets D R L Δ hinc hlocal input hD hR hC hTargets]
  have hL1 : 1 ≤ L := by
    have hh : (1 : ℝ) ≤ L := by linarith
    exact_mod_cast hh
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hp := GeneralCoveringHeavyCount.count_div G C D R L hlocal ha hL hden
  have hq : ((GeneralCoveringOwnerHighCount.physicalHigh G C D R L Δ).card : ℝ) ≤
      2 * a * ((L + 1 : ℕ) : ℝ) ^ 4 * D.card / Δ := by
    rw [GeneralCoveringOwnerHighCount.physicalHigh_card]
    exact GeneralCoveringOwnerHighCount.count_div G C D R L Δ hL1 hΔ hlocal ha0 hden
  exact (cost G C D R L B _ c (GeneralCoveringOwnerHighCount.admissible G C D R L Δ hDad) hc).2.trans
    (add_le_add (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg B))
      (mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * (B : ℝ) by positivity)))

end Paper.GeneralCoveringOwnerRepair

#print axioms Paper.GeneralCoveringOwnerRepair.core_rounds
#print axioms Paper.GeneralCoveringOwnerRepair.rounds
#print axioms Paper.GeneralCoveringOwnerRepair.core_maxBits
#print axioms Paper.GeneralCoveringOwnerRepair.maxBits
#print axioms Paper.GeneralCoveringOwnerRepair.logarithmic_bits
#print axioms Paper.GeneralCoveringOwnerRepair.mem_requested
#print axioms Paper.GeneralCoveringOwnerRepair.requested_card
#print axioms Paper.GeneralCoveringOwnerRepair.selected_card
#print axioms Paper.GeneralCoveringOwnerRepair.admissible
#print axioms Paper.GeneralCoveringOwnerRepair.bundle_subset
#print axioms Paper.GeneralCoveringOwnerRepair.covers_class
#print axioms Paper.GeneralCoveringOwnerRepair.covers_heavy_row
#print axioms Paper.GeneralCoveringOwnerRepair.cost
#print axioms Paper.GeneralCoveringOwnerRepair.run_core
#print axioms Paper.GeneralCoveringOwnerRepair.request_correct
#print axioms Paper.GeneralCoveringOwnerRepair.core_correct
#print axioms Paper.GeneralCoveringOwnerRepair.high_run
#print axioms Paper.GeneralCoveringOwnerRepair.high_correct
#print axioms Paper.GeneralCoveringOwnerRepair.chosen_expected
#print axioms Paper.GeneralCoveringOwnerRepair.chosen_correct
#print axioms Paper.GeneralCoveringOwnerRepair.high_spec
#print axioms Paper.GeneralCoveringOwnerRepair.high_cost_density
