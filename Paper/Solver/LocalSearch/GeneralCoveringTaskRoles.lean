import Paper.Solver.LocalSearch.GeneralCoveringTaskInput
import Paper.Preliminaries.RoleDictionary

/-! Shared physical role acquisition precedes any masked per-task solver.
Local center roles are canonical minimum-ID part names, with a proved
injectivity law. No part enumeration, graph or active-role oracle enters
the program. Capacity max(1,L) is derived from actual original S0 support.
Partition-label computation and masked TaskIntegral equivalence are separate. -/
namespace Paper.GeneralCoveringTaskRoles
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

structure Fields (V : Type) (B : ℕ) where
  cost : Fin (B + 1)
  role : Option V
  interior : Bool

/-- Compute the canonical optional role from an already local full part label. -/
def fromLabel {B : ℕ} (cost : Fin (B + 1)) (label : Finset V) (interior : Bool) : Fields V B :=
  ⟨cost, MaskedMinimum.minimum label, interior⟩

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringOwnerSupport.State V × Fields V B

structure Routed (V : Type) (B : ℕ) where
  input : Input V B
  ownRole : Option V
  ownInterior : Bool

def readValue (v : V) (N : Finset V) (own : Option V) (msg : N → Option V) : Option V → Option V
  | none => none
  | some u => if u = v then own else if h : u ∈ N then msg ⟨u, h⟩ else none

def routeRound (B : ℕ) : Round V (Input V B) (Routed V B) (Option V × Bool) where
  send _ _ s := (s.2.role, s.2.interior)
  update v N s msg :=
    ⟨s, readValue v N s.2.role (fun u => (msg u).1) s.1.owned.owner,
      GeneralCoveringTaskInput.readOwner v N s.2.interior (fun u => (msg u).2) s.1.owned.owner⟩

def route {bits : ℕ} (ids : BitCode V bits) (B : ℕ) : Program V (Input V B) (Routed V B) :=
  .broadcast (bits + 2) ids.option.pairBool (routeRound B)

def light {B : ℕ} (s : Routed V B) : Bool := s.input.1.admissible && !s.input.1.heavy

def rawKeys {B : ℕ} (s : Routed V B) (near : Finset V) : Finset V :=
  if light s then near else s.ownRole.toFinset

def payload {B : ℕ} (s : Routed V B) (keys : Finset V) (r : V) : GeneralCoveringFractional.Input V B :=
  ⟨decide (r ∈ keys), s.input.2.cost,
    (s.input.1.residual && decide (s.ownRole = some r)) && s.ownInterior,
    s.input.1.owned.input.candidates, s.input.1.owned.input.targets⟩

def entries {B : ℕ} (s : Routed V B) (keys : Finset V) : List (V × GeneralCoveringFractional.Input V B) :=
  keys.sort.map (fun r => (r, payload s keys r))

def dictionary {B : ℕ} (L : ℕ) (s : Routed V B) (near : Finset V) :
    List (V × GeneralCoveringFractional.Input V B) :=
  (TaggedDictionary.bounded (max 1 L) (entries s (rawKeys s near))).val

def collectRound (L B : ℕ) : Round V (Routed V B) (List (V × GeneralCoveringFractional.Input V B)) (Option V) where
  send _ _ s := s.ownRole
  update _ N s msg := dictionary L s (MaskedMinimum.pool N s.ownRole msg)

def collect {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) :
    Program V (Routed V B) (List (V × GeneralCoveringFractional.Input V B)) :=
  .broadcast (bits + 1) ids.option (collectRound L B)

def program {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) :
    Program V (Input V B) (List (V × GeneralCoveringFractional.Input V B)) :=
  .seq (route ids B) (collect ids L B)

def fromOwners {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) :
    Program V (GeneralCoveringOwners.Input V × Fields V B) (List (V × GeneralCoveringFractional.Input V B)) :=
  .seq (ProgramMemory.carry (GeneralCoveringOwnerSupport.program ids L)) (program ids L B)

theorem entries_keys {B : ℕ} (s : Routed V B) (keys : Finset V) : TaggedDictionary.keys (entries s keys) = keys := by
  simp only [entries, TaggedDictionary.keys, List.map_map, Function.comp_def, List.map_id', Finset.sort_toFinset]

theorem entries_consistent {B : ℕ} (s : Routed V B) (keys : Finset V) :
    TaggedDictionary.Consistent (payload s keys) (entries s keys) := by
  intro p hp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem dictionary_consistent {B : ℕ} (L : ℕ) (s : Routed V B) (near : Finset V) :
    TaggedDictionary.Consistent (payload s (rawKeys s near)) (dictionary L s near) :=
  TaggedDictionary.bounded_consistent _ _ _ (entries_consistent s _)

theorem dictionary_keys {B : ℕ} (L : ℕ) (s : Routed V B) (near : Finset V)
    (h : (rawKeys s near).card ≤ max 1 L) :
    TaggedDictionary.keys (dictionary L s near) = rawKeys s near := by
  rw [dictionary, TaggedDictionary.keys_bounded_eq _ _ (by rw [entries_keys]; exact h), entries_keys]

theorem dictionary_lookup {B : ℕ} (L : ℕ) (s : Routed V B) (near : Finset V)
    (h : (rawKeys s near).card ≤ max 1 L) (r : V) (hr : r ∈ rawKeys s near) :
    TaggedDictionary.lookup (dictionary L s near) r = some (payload s (rawKeys s near) r) := by
  apply TaggedDictionary.lookup_correct _ _ (dictionary_consistent L s near)
  rw [dictionary_keys L s near h]
  exact hr

theorem option_card (o : Option V) : o.toFinset.card ≤ 1 := by cases o <;> simp

theorem image_card (S : Finset V) (m : V → Option V) : (S.biUnion (fun u => (m u).toFinset)).card ≤ S.card := by
  calc
    _ ≤ ∑ u ∈ S, (m u).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, 1 := Finset.sum_le_sum (fun u _ => option_card (m u))
    _ = S.card := by simp

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def ownedRole (cover : V → Finset V) (D R : Finset V) {B : ℕ} (s : V → Input V B) (v : V) : Option V :=
  (GeneralCoveringOwners.owner cover D R v).bind (fun u => (s u).2.role)

def ownedInterior (cover : V → Finset V) (D R : Finset V) {B : ℕ} (s : V → Input V B) (v : V) : Bool :=
  ((GeneralCoveringOwners.owner cover D R v).map (fun u => (s u).2.interior)).getD false

def routed (cover : V → Finset V) (D R : Finset V) {B : ℕ} (s : V → Input V B) (v : V) : Routed V B :=
  ⟨s v, ownedRole cover D R s v, ownedInterior cover D R s v⟩

def pooled (cover : V → Finset V) (D R : Finset V) {B : ℕ} (s : V → Input V B) (v : V) : Finset V :=
  MaskedMinimum.pool (G.neighborFinset v) (ownedRole cover D R s v) (fun u => ownedRole cover D R s u.val)

def keysAt (cover : V → Finset V) (D R : Finset V) {B : ℕ} (s : V → Input V B) (v : V) : Finset V :=
  rawKeys (routed cover D R s v) (pooled G cover D R s v)

theorem bind_some (o : Option V) (m : V → Option V) (r : V) :
    o.bind m = some r ↔ ∃ u, o = some u ∧ m u = some r := by cases o <;> simp

theorem read_some (m : V → Option V) (v u : V) (hu : u ∈ closed G v) :
    readValue v (G.neighborFinset v) (m v) (fun w => m w.val) (some u) = m u := by
  by_cases he : u = v
  · subst u
    simp [readValue]
  · have hn := (G.mem_neighborFinset v u).mpr (((mem_closed G u v).mp hu).resolve_left he)
    simp only [readValue, if_neg he, dif_pos hn]

theorem route_correct {bits B : ℕ} (ids : BitCode V bits) (cover : V → Finset V) (D R : Finset V)
    (s : V → Input V B) (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) : (route ids B).run G s = routed cover D R s := by
  funext v
  change (⟨s v,
    readValue v (G.neighborFinset v) (s v).2.role (fun u => (s u.val).2.role) (s v).1.owned.owner,
    GeneralCoveringTaskInput.readOwner v (G.neighborFinset v) (s v).2.interior
      (fun u => (s u.val).2.interior) (s v).1.owned.owner⟩ : Routed V B) = _
  unfold routed ownedRole ownedInterior
  rw [ho v]
  cases hown : GeneralCoveringOwners.owner cover D R v with
  | none => rfl
  | some u =>
    have hn : u ∈ closed G v := (mem_closed G u v).mpr
      ((GeneralCoveringOwners.owner_star G cover D R hlocal hown).elim Or.inl (fun h => Or.inr h.symm))
    change (⟨s v, readValue v (G.neighborFinset v) (s v).2.role (fun w => (s w.val).2.role) (some u),
      CohostKnown.read v (G.neighborFinset v) (s v).2.interior (fun w => (s w.val).2.interior) u⟩ : Routed V B) =
      ⟨s v, (s u).2.role, (s u).2.interior⟩
    rw [read_some G (fun w => (s w).2.role) v u hn,
      GeneralCoveringTaskInput.read_local G (fun w => (s w).2.interior) v u hn]

theorem run_program {bits B : ℕ} (ids : BitCode V bits) (L : ℕ) (cover : V → Finset V) (D R : Finset V)
    (s : V → Input V B) (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) :
    (program ids L B).runEncoded G s = fun v => dictionary L (routed cover D R s v) (pooled G cover D R s v) := by
  rw [Program.runEncoded_eq_run]
  change (collect ids L B).run G ((route ids B).run G s) = _
  exact congrArg ((collect ids L B).run G) (route_correct G ids cover D R s ho hlocal)

theorem pooled_eq {B : ℕ} (cover : V → Finset V) (D R : Finset V) (s : V → Input V B) (v : V) :
    pooled G cover D R s v = (GeneralCoveringOwnerSupport.support G cover D R v).biUnion (fun u => (s u).2.role.toFinset) := by
  ext r
  constructor
  · intro hr
    apply MaskedMinimum.pool_origin (G.neighborFinset v) (ownedRole cover D R s v)
      (fun u => ownedRole cover D R s u.val)
      (fun r => r ∈ (GeneralCoveringOwnerSupport.support G cover D R v).biUnion (fun u => (s u).2.role.toFinset)) ?_ ?_ hr
    · intro r hr
      obtain ⟨u, hu, hm⟩ := (bind_some _ _ r).mp hr
      exact Finset.mem_biUnion.mpr ⟨u,
        (GeneralCoveringOwnerSupport.mem_support G cover D R v u).mpr ⟨v, self_mem_closed G v, hu⟩, by simp [hm]⟩
    · intro w r hr
      obtain ⟨u, hu, hm⟩ := (bind_some _ _ r).mp hr
      exact Finset.mem_biUnion.mpr ⟨u,
        (GeneralCoveringOwnerSupport.mem_support G cover D R v u).mpr
          ⟨w.val, (mem_closed G w.val v).mpr (Or.inr ((G.mem_neighborFinset v w.val).mp w.property)), hu⟩,
        by simp [hm]⟩
  · intro hr
    obtain ⟨u, hu, hm⟩ := Finset.mem_biUnion.mp hr
    have hrole : (s u).2.role = some r := by simpa using hm
    obtain ⟨w, hw, hown⟩ := (GeneralCoveringOwnerSupport.mem_support G cover D R v u).mp hu
    have hwr : ownedRole cover D R s w = some r := by simp only [ownedRole, hown, Option.bind_some]; exact hrole
    rcases (mem_closed G w v).mp hw with he | ha
    · subst w
      exact MaskedMinimum.mem_pool_self _ _ hwr
    · exact MaskedMinimum.mem_pool_incoming (G.neighborFinset v) (ownedRole cover D R s v)
        (fun x => ownedRole cover D R s x.val) ⟨w, (G.mem_neighborFinset v w).mpr ha⟩ hwr

theorem own_subset {B : ℕ} (cover : V → Finset V) (D R : Finset V) (s : V → Input V B) (v : V) :
    (ownedRole cover D R s v).toFinset ⊆ pooled G cover D R s v := by
  intro r hr
  exact MaskedMinimum.mem_pool_self _ _ (by simpa using hr)

theorem raw_mem {B : ℕ} (t : Routed V B) (near : Finset V) (hs : t.ownRole.toFinset ⊆ near) (r : V) :
    r ∈ rawKeys t near ↔ t.ownRole = some r ∨ (light t = true ∧ r ∈ near) := by
  by_cases hl : light t = true
  · rw [rawKeys, if_pos hl]
    constructor
    · intro hr; exact Or.inr ⟨hl, hr⟩
    · rintro (ho | ⟨_, hr⟩)
      · exact hs (by simp [ho])
      · exact hr
  · rw [rawKeys, if_neg hl]
    constructor
    · intro hr; exact Or.inl (by simpa using hr)
    · rintro (ho | ⟨hh, _⟩)
      · simp [ho]
      · exact False.elim (hl hh)

theorem keys_card {B : ℕ} (L : ℕ) (cover : V → Finset V) (D R : Finset V) (s : V → Input V B)
    (had : ∀ v, (s v).1.admissible = decide (v ∈ CoveringSupport.admissible cover R))
    (hh : ∀ v, (s v).1.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G cover D R L)) (v : V) :
    (keysAt G cover D R s v).card ≤ max 1 L := by
  by_cases hl : light (routed cover D R s v) = true
  · have hp : v ∈ CoveringSupport.admissible cover R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G cover D R L := by
      simpa only [light, routed, had v, hh v, ← _root_.decide_not,
        ← Bool.decide_and, decide_eq_true_eq] using hl
    have hsize : (GeneralCoveringOwnerSupport.support G cover D R v).card ≤ L := by
      by_contra hlarge
      exact hp.2 (Finset.mem_filter.mpr ⟨hp.1, by omega⟩)
    change (rawKeys (routed cover D R s v) (pooled G cover D R s v)).card ≤ _
    rw [rawKeys, if_pos hl, pooled_eq]
    exact ((image_card _ (fun u => (s u).2.role)).trans hsize).trans (le_max_right 1 L)
  · change (rawKeys (routed cover D R s v) (pooled G cover D R s v)).card ≤ _
    rw [rawKeys, if_neg hl]
    exact (option_card _).trans (le_max_left 1 L)

/-- Canonical names of actual disjoint nonempty owner parts. -/
def partIDs (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) : Finset V := I.image (fun i => i.val.val)

theorem partIDs_nonempty (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) (h : I.Nonempty) :
    (partIDs D Q I).Nonempty := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i.val.val, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

def name (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) (h : I.Nonempty) : V :=
  (partIDs D Q I).min' (partIDs_nonempty D Q I h)

theorem name_mem (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) (h : I.Nonempty) :
    name D Q I h ∈ partIDs D Q I := Finset.min'_mem _ _

theorem name_option (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) (h : I.Nonempty) :
    MaskedMinimum.minimum (partIDs D Q I) = some (name D Q I h) := dif_pos (partIDs_nonempty D Q I h)

theorem fromLabel_name {B : ℕ} (cost : Fin (B + 1)) (interior : Bool)
    (D : Finset V) (Q : Finset D) (I : Finset (Low D Q)) (h : I.Nonempty) :
    (fromLabel cost (partIDs D Q I) interior).role = some (name D Q I h) := name_option D Q I h

theorem name_injective (D : Finset V) (Q : Finset D) (F : Finset (Finset (Low D Q)))
    (hd : (F : Set (Finset (Low D Q))).Pairwise Disjoint) (I J : Finset (Low D Q))
    (hI : I ∈ F) (hJ : J ∈ F) (hnI : I.Nonempty) (hnJ : J.Nonempty)
    (he : name D Q I hnI = name D Q J hnJ) : I = J := by
  obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp (name_mem D Q I hnI)
  obtain ⟨j, hj, hej⟩ := Finset.mem_image.mp (name_mem D Q J hnJ)
  have hij : i = j := Subtype.ext (Subtype.ext (hei.trans (he.trans hej.symm)))
  by_contra hne
  exact Finset.disjoint_left.mp (hd hI hJ hne) hi (hij.symm ▸ hj)

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G cover D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Proof-side original geometry and truthful local intermediate fields.
There is deliberately no cardinality/capacity hypothesis. -/
structure Geometry (L B : ℕ) (s : V → Input V B) where
  cover : V → Finset V
  targets : V → Finset V
  D : Finset V
  R : Finset V
  Q : Finset D
  k : ℕ
  P : SmallParts.Data (graph G cover D R L Q) Finset.univ k
  Bdy : Finset (Low D Q)
  local_rows : ∀ r ∈ R, cover r ⊆ closed G r
  owner : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v
  admissible : ∀ v, (s v).1.admissible = decide (v ∈ CoveringSupport.admissible cover R)
  heavy : ∀ v, (s v).1.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G cover D R L)
  residual : ∀ v, (s v).1.residual = decide (v ∈ GeneralCoveringOwnerSupport.residual G cover D R L)
  candidates : ∀ v, (s v).1.owned.input.candidates = cover v
  inverse : ∀ v, (s v).1.owned.input.targets = targets v
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  low_role : ∀ (I : Finset (Low D Q)) (hI : I ∈ P.parts) (i : Low D Q), i ∈ I →
    (s i.val.val).2.role = some (name D Q I (P.nonempty I hI))
  excluded_role : ∀ d : D, d ∈ Q → (s d.val).2.role = none
  interior : ∀ i : Low D Q, (s i.val.val).2.interior = decide (i ∉ Bdy)

def roleID {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) : V := name g.D g.Q I (g.P.nonempty I hI)

theorem center_role_valid {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (u r : V) (hu : u ∈ g.D) (hr : (s u).2.role = some r) :
    ∃ I : Finset (Low g.D g.Q), ∃ hI : I ∈ g.P.parts, roleID G g I hI = r := by
  let d : g.D := ⟨u, hu⟩
  by_cases hq : d ∈ g.Q
  · have hn := g.excluded_role d hq
    have hb := hr.symm.trans hn
    cases hb
  · let i : Low g.D g.Q := ⟨d, hq⟩
    obtain ⟨I, hI, hi⟩ := g.P.covers i (Finset.mem_univ i)
    exact ⟨I, hI, Option.some.inj ((g.low_role I hI i hi).symm.trans hr)⟩

theorem center_role_iff {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (u : V) (hu : u ∈ g.D) :
    (s u).2.role = some (roleID G g I hI) ↔ ∃ i : Low g.D g.Q, i ∈ I ∧ i.val.val = u := by
  constructor
  · intro hr
    let d : g.D := ⟨u, hu⟩
    by_cases hq : d ∈ g.Q
    · have hb := hr.symm.trans (g.excluded_role d hq)
      cases hb
    · let i : Low g.D g.Q := ⟨d, hq⟩
      obtain ⟨J, hJ, hi⟩ := g.P.covers i (Finset.mem_univ i)
      have he : name g.D g.Q I (g.P.nonempty I hI) = name g.D g.Q J (g.P.nonempty J hJ) :=
        Option.some.inj (hr.symm.trans (g.low_role J hJ i hi))
      have hIJ := name_injective g.D g.Q g.P.parts g.P.disjoint I J hI hJ (g.P.nonempty I hI) (g.P.nonempty J hJ) he
      exact ⟨i, hIJ.symm ▸ hi, rfl⟩
  · rintro ⟨i, hi, he⟩
    rw [← he]
    exact g.low_role I hI i hi

theorem owned_named_iff {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) :
    ownedRole g.cover g.D g.R s v = some (roleID G g I hI) ↔
      v ∈ GeneralCoveringTaskInput.stars g.cover g.D g.R g.Q I := by
  constructor
  · intro hr
    obtain ⟨u, hu, hm⟩ := (bind_some _ _ _).mp hr
    obtain ⟨i, hi, he⟩ := (center_role_iff G g I hI u (GeneralCoveringOwners.owner_mem _ _ _ hu)).mp hm
    exact (GeneralCoveringTaskInput.mem_stars g.cover g.D g.R g.Q I v).mpr ⟨i, hi, by rw [he]; exact hu⟩
  · intro hv
    obtain ⟨i, hi, ho⟩ := (GeneralCoveringTaskInput.mem_stars g.cover g.D g.R g.Q I v).mp hv
    change (GeneralCoveringOwners.owner g.cover g.D g.R v).bind (fun u => (s u).2.role) = _
    rw [ho]
    exact g.low_role I hI i hi

theorem pooled_named_iff {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) :
    roleID G g I hI ∈ pooled G g.cover g.D g.R s v ↔
      ∃ i ∈ I, i.val.val ∈ GeneralCoveringOwnerSupport.support G g.cover g.D g.R v := by
  rw [pooled_eq]
  constructor
  · intro hr
    obtain ⟨u, hu, hm⟩ := Finset.mem_biUnion.mp hr
    have hm' : (s u).2.role = some (roleID G g I hI) := by simpa using hm
    obtain ⟨i, hi, he⟩ := (center_role_iff G g I hI u
      (GeneralCoveringOwnerSupport.support_labels G g.cover g.D g.R v hu)).mp hm'
    exact ⟨i, hi, by rw [he]; exact hu⟩
  · rintro ⟨i, hi, hs⟩
    exact Finset.mem_biUnion.mpr ⟨i.val.val, hs, by simp [roleID, g.low_role I hI i hi]⟩

theorem light_iff {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s) (v : V) :
    light (routed g.cover g.D g.R s v) = true ↔
      v ∈ CoveringSupport.admissible g.cover g.R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G g.cover g.D g.R L := by
  simp only [light, routed, g.admissible v, g.heavy v, ← _root_.decide_not, ← Bool.decide_and, decide_eq_true_eq]

theorem keys_named_iff {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) :
    roleID G g I hI ∈ keysAt G g.cover g.D g.R s v ↔ v ∈ vertices G g.cover g.D g.R L g.Q I := by
  unfold keysAt
  rw [raw_mem _ _ (own_subset G g.cover g.D g.R s v)]
  change (ownedRole g.cover g.D g.R s v = some (roleID G g I hI) ∨
    (light (routed g.cover g.D g.R s v) = true ∧ roleID G g I hI ∈ pooled G g.cover g.D g.R s v)) ↔ _
  rw [owned_named_iff G g I hI v, light_iff G g v, pooled_named_iff G g I hI v,
    ← GeneralCoveringTaskInput.touch_support G g.cover g.D g.R g.Q I v]
  exact (GeneralCoveringTaskInput.vertices_iff G g.cover g.D g.R L g.Q I v).symm

theorem interior_named_iff {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) :
    (ownedRole g.cover g.D g.R s v = some (roleID G g I hI) ∧ ownedInterior g.cover g.D g.R s v = true) ↔
      ∃ i ∈ I, i ∉ g.Bdy ∧ GeneralCoveringOwners.owner g.cover g.D g.R v = some i.val.val := by
  constructor
  · rintro ⟨hr, hb⟩
    obtain ⟨i, hi, ho⟩ := (GeneralCoveringTaskInput.mem_stars g.cover g.D g.R g.Q I v).mp
      ((owned_named_iff G g I hI v).mp hr)
    have hflag : (s i.val.val).2.interior = true := by
      simpa only [ownedInterior, ho, Option.map_some, Option.getD_some] using hb
    rw [g.interior i] at hflag
    exact ⟨i, hi, of_decide_eq_true hflag, ho⟩
  · rintro ⟨i, hi, hb, ho⟩
    refine ⟨?_, ?_⟩
    · change (GeneralCoveringOwners.owner g.cover g.D g.R v).bind (fun u => (s u).2.role) = _
      rw [ho]
      exact g.low_role I hI i hi
    · simp [ownedInterior, ho, g.interior i, hb]

theorem payload_part {L B : ℕ} {s : V → Input V B} (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) :
    payload (routed g.cover g.D g.R s v) (keysAt G g.cover g.D g.R s v) (roleID G g I hI) =
      (⟨decide (v ∈ vertices G g.cover g.D g.R L g.Q I), (s v).2.cost,
        decide (v ∈ demands G g.cover g.D g.R L g.Q I g.Bdy), g.cover v, g.targets v⟩ : GeneralCoveringFractional.Input V B) := by
  have ha := Bool.decide_congr (keys_named_iff G g I hI v)
  have hb : ownedInterior g.cover g.D g.R s v = decide (ownedInterior g.cover g.D g.R s v = true) := by
    cases ownedInterior g.cover g.D g.R s v <;> rfl
  have hd : (((s v).1.residual && decide (ownedRole g.cover g.D g.R s v = some (roleID G g I hI))) &&
      ownedInterior g.cover g.D g.R s v) = decide (v ∈ demands G g.cover g.D g.R L g.Q I g.Bdy) := by
    rw [g.residual v, hb]
    simp only [← Bool.decide_and]
    apply Bool.decide_congr
    constructor
    · rintro ⟨⟨hr, ho⟩, hi⟩
      obtain ⟨i, hiI, hiB, hoi⟩ := (interior_named_iff G g I hI v).mp ⟨ho, hi⟩
      exact Finset.mem_filter.mpr ⟨hr, i, hiI, hiB, hoi⟩
    · intro hv
      obtain ⟨hr, i, hiI, hiB, hoi⟩ := Finset.mem_filter.mp hv
      have hh := (interior_named_iff G g I hI v).mpr ⟨i, hiI, hiB, hoi⟩
      exact ⟨⟨hr, hh.1⟩, hh.2⟩
  change (⟨decide (roleID G g I hI ∈ keysAt G g.cover g.D g.R s v), (s v).2.cost,
    ((s v).1.residual && decide (ownedRole g.cover g.D g.R s v = some (roleID G g I hI))) &&
      ownedInterior g.cover g.D g.R s v, (s v).1.owned.input.candidates, (s v).1.owned.input.targets⟩ :
      GeneralCoveringFractional.Input V B) = _
  rw [ha, hd, g.candidates v, g.inverse v]

theorem output_keys {bits B : ℕ} (ids : BitCode V bits) (L : ℕ) (cover : V → Finset V) (D R : Finset V)
    (s : V → Input V B) (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (had : ∀ v, (s v).1.admissible = decide (v ∈ CoveringSupport.admissible cover R))
    (hh : ∀ v, (s v).1.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G cover D R L)) (v : V) :
    TaggedDictionary.keys ((program ids L B).runEncoded G s v) = keysAt G cover D R s v := by
  rw [run_program G ids L cover D R s ho hlocal]
  exact dictionary_keys L _ _ (keys_card G L cover D R s had hh v)

theorem capacity {bits B : ℕ} (ids : BitCode V bits) (L : ℕ) (cover : V → Finset V) (D R : Finset V)
    (s : V → Input V B) (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (had : ∀ v, (s v).1.admissible = decide (v ∈ CoveringSupport.admissible cover R))
    (hh : ∀ v, (s v).1.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G cover D R L)) (v : V) :
    (TaggedDictionary.keys ((program ids L B).runEncoded G s v)).card ≤ max 1 L := by
  rw [output_keys G ids L cover D R s ho hlocal had hh v]
  exact keys_card G L cover D R s had hh v

theorem consistent {bits B : ℕ} (ids : BitCode V bits) (L : ℕ) (cover : V → Finset V) (D R : Finset V)
    (s : V → Input V B) (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) (v : V) :
    TaggedDictionary.Consistent (payload (routed cover D R s v) (keysAt G cover D R s v))
      ((program ids L B).runEncoded G s v) := by
  rw [run_program G ids L cover D R s ho hlocal]
  exact dictionary_consistent L _ _

theorem keys_part {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) :
    roleID G g I hI ∈ TaggedDictionary.keys ((program ids L B).runEncoded G s v) ↔
      v ∈ vertices G g.cover g.D g.R L g.Q I := by
  rw [output_keys G ids L g.cover g.D g.R s g.owner g.local_rows g.admissible g.heavy v]
  exact keys_named_iff G g I hI v

theorem lookup_part {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (g : Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) (hv : v ∈ vertices G g.cover g.D g.R L g.Q I) :
    TaggedDictionary.lookup ((program ids L B).runEncoded G s v) (roleID G g I hI) =
      some (⟨decide (v ∈ vertices G g.cover g.D g.R L g.Q I), (s v).2.cost,
        decide (v ∈ demands G g.cover g.D g.R L g.Q I g.Bdy), g.cover v, g.targets v⟩ : GeneralCoveringFractional.Input V B) := by
  rw [run_program G ids L g.cover g.D g.R s g.owner g.local_rows]
  rw [dictionary_lookup L _ _ (keys_card G L g.cover g.D g.R s g.admissible g.heavy v)
    (roleID G g I hI) ((keys_named_iff G g I hI v).mpr hv)]
  simpa only [keysAt] using congrArg some (payload_part G g I hI v)

theorem keys_valid {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (g : Geometry G L B s)
    (v r : V) (hr : r ∈ TaggedDictionary.keys ((program ids L B).runEncoded G s v)) :
    ∃ I : Finset (Low g.D g.Q), ∃ hI : I ∈ g.P.parts, roleID G g I hI = r := by
  rw [output_keys G ids L g.cover g.D g.R s g.owner g.local_rows g.admissible g.heavy v] at hr
  have hraw := (raw_mem (routed g.cover g.D g.R s v) (pooled G g.cover g.D g.R s v)
    (own_subset G g.cover g.D g.R s v) r).mp hr
  rcases hraw with ho | ⟨_, hp⟩
  · obtain ⟨u, hu, hm⟩ := (bind_some _ _ _).mp ho
    exact center_role_valid G g u r (GeneralCoveringOwners.owner_mem _ _ _ hu) hm
  · rw [pooled_eq] at hp
    obtain ⟨u, hu, hm⟩ := Finset.mem_biUnion.mp hp
    exact center_role_valid G g u r (GeneralCoveringOwnerSupport.support_labels G g.cover g.D g.R v hu)
      (by simpa using hm)

theorem empty_parts {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits) (g : Geometry G L B s)
    (he : g.P.parts = ∅) (v : V) : (program ids L B).runEncoded G s v = [] := by
  cases hx : (program ids L B).runEncoded G s v with
  | nil => rfl
  | cons p xs =>
    have hp : p.1 ∈ TaggedDictionary.keys ((program ids L B).runEncoded G s v) :=
      (TaggedDictionary.mem_keys _ p.1).mpr ⟨p, by rw [hx]; simp, rfl⟩
    obtain ⟨I, hI, _⟩ := keys_valid G ids g v p.1 hp
    rw [he] at hI
    exact False.elim (Finset.notMem_empty I hI)

theorem route_none {bits B : ℕ} (ids : BitCode V bits) (s : V → Input V B) (v : V)
    (ho : (s v).1.owned.owner = none) :
    ((route ids B).runEncoded G s v).ownRole = none ∧ ((route ids B).runEncoded G s v).ownInterior = false := by
  rw [Program.runEncoded_eq_run]
  change readValue v (G.neighborFinset v) (s v).2.role (fun u => (s u.val).2.role) (s v).1.owned.owner = none ∧
    GeneralCoveringTaskInput.readOwner v (G.neighborFinset v) (s v).2.interior
      (fun u => (s u.val).2.interior) (s v).1.owned.owner = false
  rw [ho]
  exact ⟨rfl, rfl⟩

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) : (program ids L B).rounds = 2 := rfl

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) : (program ids L B).maxBits = bits + 2 := by
  change max (bits + 2) (bits + 1) = bits + 2
  omega

theorem length_output {bits B : ℕ} (ids : BitCode V bits) (L : ℕ) (s : V → Input V B) (v : V) :
    ((program ids L B).runEncoded G s v).length ≤ max 1 L := by
  rw [Program.runEncoded_eq_run]
  let t := (route ids B).run G s
  let near := MaskedMinimum.pool (G.neighborFinset v) (t v).ownRole (fun u => (t u.val).ownRole)
  change (dictionary L (t v) near).length ≤ max 1 L
  exact (TaggedDictionary.bounded (max 1 L) (entries (t v) (rawKeys (t v) near))).property

/-- Shared acquisition executes on G before any sparse masked simulation. -/
theorem fromOwners_run {bits B : ℕ} (ids : BitCode V bits) (L : ℕ)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → Fields V B) :
    (fromOwners ids L B).runEncoded G (fun v => (s v, fields v)) =
      (program ids L B).runEncoded G
        (fun v => ((GeneralCoveringOwnerSupport.program ids L).runEncoded G s v, fields v)) := by
  change (program ids L B).runEncoded G
    ((ProgramMemory.carry (X := Fields V B) (GeneralCoveringOwnerSupport.program ids L)).runEncoded G
      (fun v => (s v, fields v))) = _
  rw [Program.runEncoded_eq_run G (ProgramMemory.carry (X := Fields V B) (GeneralCoveringOwnerSupport.program ids L)),
    ProgramMemory.run (X := Fields V B) G (GeneralCoveringOwnerSupport.program ids L),
    Program.runEncoded_eq_run G (GeneralCoveringOwnerSupport.program ids L)]

theorem fromOwners_correct {bits B : ℕ} (ids : BitCode V bits) (cover targets : V → Finset V)
    (D R : Finset V) (L : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    (fromOwners ids L B).runEncoded G (fun v => (s v, fields v)) =
      (program ids L B).runEncoded G (fun v =>
        (GeneralCoveringOwnerSupport.expected G cover D R L (fun u =>
          ⟨s u, GeneralCoveringOwners.owner cover D R u⟩) v, fields v)) := by
  rw [fromOwners_run, Program.runEncoded_eq_run G (GeneralCoveringOwnerSupport.program ids L),
    GeneralCoveringOwnerSupport.correct G ids cover targets D R L hinc hlocal s hD hR hC ht]

theorem fromOwners_capacity {bits B : ℕ} (ids : BitCode V bits) (cover targets : V → Finset V)
    (D R : Finset V) (L : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) (v : V) :
    (TaggedDictionary.keys ((fromOwners ids L B).runEncoded G (fun u => (s u, fields u)) v)).card ≤ max 1 L := by
  rw [fromOwners_correct G ids cover targets D R L hinc hlocal s fields hD hR hC ht]
  let t : V → Input V B := fun u =>
    (GeneralCoveringOwnerSupport.expected G cover D R L
      (fun w => ⟨s w, GeneralCoveringOwners.owner cover D R w⟩) u, fields u)
  exact capacity G ids L cover D R t (fun _ => rfl) hlocal (fun _ => rfl) (fun _ => rfl) v

/-- Actual computed metadata and dictionaries, with only local center naming/interior fields left as intermediate input. -/
theorem fromOwners_part {bits B : ℕ} (ids : BitCode V bits) (cover targets : V → Finset V)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k) (Bdy : Finset (Low D Q))
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
    (hrole : ∀ (J : Finset (Low D Q)) (hJ : J ∈ P.parts) (i : Low D Q), i ∈ J →
      (fields i.val.val).role = some (name D Q J (P.nonempty J hJ)))
    (hexcluded : ∀ d : D, d ∈ Q → (fields d.val).role = none)
    (hinterior : ∀ i : Low D Q, (fields i.val.val).interior = decide (i ∉ Bdy))
    (I : Finset (Low D Q)) (hI : I ∈ P.parts) (v : V) :
    (name D Q I (P.nonempty I hI) ∈ TaggedDictionary.keys
      ((fromOwners ids L B).runEncoded G (fun u => (s u, fields u)) v) ↔ v ∈ vertices G cover D R L Q I) ∧
    (v ∈ vertices G cover D R L Q I →
      TaggedDictionary.lookup ((fromOwners ids L B).runEncoded G (fun u => (s u, fields u)) v)
        (name D Q I (P.nonempty I hI)) =
        some (⟨decide (v ∈ vertices G cover D R L Q I), (fields v).cost,
          decide (v ∈ demands G cover D R L Q I Bdy), cover v, targets v⟩ : GeneralCoveringFractional.Input V B)) := by
  rw [fromOwners_correct G ids cover targets D R L hinc hlocal s fields hD hR hC ht]
  let t : V → Input V B := fun u =>
    (GeneralCoveringOwnerSupport.expected G cover D R L
      (fun w => ⟨s w, GeneralCoveringOwners.owner cover D R w⟩) u, fields u)
  let g : Geometry G L B t :=
    { cover := cover
      targets := targets
      D := D
      R := R
      Q := Q
      k := k
      P := P
      Bdy := Bdy
      local_rows := hlocal
      owner := fun _ => rfl
      admissible := fun _ => rfl
      heavy := fun _ => rfl
      residual := fun _ => rfl
      candidates := hC
      inverse := ht
      incidence := hinc
      low_role := hrole
      excluded_role := hexcluded
      interior := hinterior }
  exact ⟨keys_part G ids g I hI v, fun hv => lookup_part G ids g I hI v hv⟩

theorem fromOwners_rounds {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) : (fromOwners ids L B).rounds = 6 := by
  simp only [fromOwners, Program.rounds, ProgramMemory.rounds, GeneralCoveringOwnerSupport.rounds, rounds]

theorem fromOwners_maxBits {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) : (fromOwners ids L B).maxBits = bits + 2 := by
  simp only [fromOwners, Program.maxBits, ProgramMemory.maxBits, GeneralCoveringOwnerSupport.maxBits, maxBits]
  omega
end Paper.GeneralCoveringTaskRoles

#print axioms Paper.GeneralCoveringTaskRoles.name_injective
#print axioms Paper.GeneralCoveringTaskRoles.fromLabel_name
#print axioms Paper.GeneralCoveringTaskRoles.run_program
#print axioms Paper.GeneralCoveringTaskRoles.pooled_eq
#print axioms Paper.GeneralCoveringTaskRoles.capacity
#print axioms Paper.GeneralCoveringTaskRoles.consistent
#print axioms Paper.GeneralCoveringTaskRoles.keys_part
#print axioms Paper.GeneralCoveringTaskRoles.lookup_part
#print axioms Paper.GeneralCoveringTaskRoles.keys_valid
#print axioms Paper.GeneralCoveringTaskRoles.empty_parts
#print axioms Paper.GeneralCoveringTaskRoles.route_none
#print axioms Paper.GeneralCoveringTaskRoles.length_output
#print axioms Paper.GeneralCoveringTaskRoles.fromOwners_correct
#print axioms Paper.GeneralCoveringTaskRoles.fromOwners_capacity
#print axioms Paper.GeneralCoveringTaskRoles.fromOwners_part
#print axioms Paper.GeneralCoveringTaskRoles.rounds
#print axioms Paper.GeneralCoveringTaskRoles.maxBits
#print axioms Paper.GeneralCoveringTaskRoles.fromOwners_rounds
#print axioms Paper.GeneralCoveringTaskRoles.fromOwners_maxBits

