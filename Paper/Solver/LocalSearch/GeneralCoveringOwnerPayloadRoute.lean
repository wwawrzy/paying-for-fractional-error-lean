import Paper.Solver.LocalSearch.GeneralCoveringOwnerDiscoveryCorrect
import Paper.Preliminaries.TaggedGather

/-! Actual optional-owner payload transport. Four physical broadcasts read
active centers, gather singleton tags, forward at light admissible candidates,
and return Option-addressed bounded reports. Private support metadata is
computed by its accepted producer and retained with the private payload.
No graph, owner, support, routing or degree oracle enters the public program. -/
namespace Paper.GeneralCoveringOwnerPayloadRoute
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V A : Type} [LinearOrder V]

structure Input (V A : Type) where
  metadata : GeneralCoveringOwnerSupport.State V
  active : Bool
  payload : A

structure PrivateInput (V A : Type) where
  localInput : GeneralCoveringOwners.Input V
  active : Bool
  payload : A

structure Report (V A : Type) where
  owner : Option V
  payloads : List (V × A)

structure Output (V A : Type) where
  input : Input V A
  payloads : List (V × A)

def sending (s : Input V A) : Bool := s.metadata.owned.input.center && s.active

def read (v : V) (N : Finset V) (s : Input V A) (msg : N → Bool × A) : Option (V × A) :=
  match s.metadata.owned.owner with
  | none => none
  | some i =>
    if i = v then if sending s then some (i, s.payload) else none
    else if h : i ∈ N then if (msg ⟨i, h⟩).1 then some (i, (msg ⟨i, h⟩).2) else none
    else none

def readRound : Round V (Input V A) (Option (V × A)) (Bool × A) where
  send _ _ s := (sending s, s.payload)
  update v N s msg := read v N s msg

def readProgram {w : ℕ} (P : BitCode A w) : Program V (Input V A) (Option (V × A)) :=
  .broadcast (1 + w) (PacketCode.product BitCode.bool P) readRound

def gate (s : Input V A) : Bool := s.metadata.admissible && !s.metadata.heavy

def candidateProgram : Program V (List (V × A) × Input V A) (List (V × A) × Input V A) :=
  .local fun _ _ s => (if gate s.2 then s.1 else [], s.2)

def makeReport (s : Input V A) (xs : List (V × A)) : Report V A :=
  match s.metadata.owned.owner with
  | none => ⟨none, []⟩
  | some i => ⟨some i, xs⟩

theorem makeReport_owner (s : Input V A) (xs : List (V × A)) :
    (makeReport s xs).owner = s.metadata.owned.owner := by
  cases ho : s.metadata.owned.owner <;> simp [makeReport, ho]

theorem makeReport_mem (s : Input V A) (xs : List (V × A)) (p : V × A)
    (hp : p ∈ (makeReport s xs).payloads) : p ∈ xs := by
  cases ho : s.metadata.owned.owner <;> simp_all [makeReport]

def accept (v : V) (r : Report V A) : List (V × A) :=
  if r.owner = some v then r.payloads else []

theorem mem_accept (v : V) (r : Report V A) (p : V × A) :
    p ∈ accept v r ↔ r.owner = some v ∧ p ∈ r.payloads := by
  by_cases h : r.owner = some v <;> simp [accept, h]

def reportRound (K : ℕ) : Round V (Report V A) (List (V × A))
    (Option V × {l : List (V × A) // l.length ≤ K}) where
  send _ _ s := (s.owner, TaggedDictionary.bounded K s.payloads)
  update v N own msg := TaggedGather.collect N
    (accept v ⟨own.owner, (TaggedDictionary.bounded K own.payloads).val⟩)
    (fun u => accept v ⟨(msg u).1, (msg u).2.val⟩)

def reportProgram {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (K : ℕ) :
    Program V (Report V A) (List (V × A)) :=
  .broadcast ((b + 1) + K * (b + w + 1))
    (PacketCode.product ids.option (ListPacket.bounded (PacketCode.product ids P) K)) (reportRound K)

def enabled (v : V) (s : Input V A) : Bool :=
  s.metadata.owned.input.center && decide (s.metadata.owned.owner = some v)

def finish (v : V) (s : Input V A) (xs : List (V × A)) : Output V A :=
  ⟨s, if enabled v s then xs else []⟩

def prepare : Program V (Input V A) (Input V A × Input V A) := .local fun _ _ s => (s, s)

def toList : Program V (Option (V × A) × Input V A) (List (V × A) × Input V A) :=
  .local fun _ _ s => (s.1.toList, s.2)

def toReport : Program V (List (V × A) × Input V A) (Report V A × Input V A) :=
  .local fun _ _ s => (makeReport s.2 s.1, s.2)

def finishProgram : Program V (List (V × A) × Input V A) (Output V A) :=
  .local fun v _ s => finish v s.2 s.1

/-- All routing parameters and codes are public, before any physical graph. -/
def route {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    Program V (Input V A) (Output V A) :=
  .seq prepare (.seq (ProgramMemory.carry (readProgram P)) (.seq toList
    (.seq (ProgramMemory.carry (TaggedGather.program ids P 1)) (.seq candidateProgram
      (.seq (ProgramMemory.carry (TaggedGather.program ids P L)) (.seq toReport
        (.seq (ProgramMemory.carry (reportProgram ids P (Δ + 1))) finishProgram)))))))

def privatePrepare : Program V (PrivateInput V A) (GeneralCoveringOwners.Input V × (Bool × A)) :=
  .local fun _ _ s => (s.localInput, (s.active, s.payload))

def attachInput : Program V (GeneralCoveringOwnerSupport.State V × (Bool × A)) (Input V A) :=
  .local fun _ _ s => ⟨s.1, s.2.1, s.2.2⟩

/-- Native composition derives metadata from private incidence lists and bits. -/
def program {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    Program V (PrivateInput V A) (Output V A) :=
  .seq privatePrepare (.seq (ProgramMemory.carry (GeneralCoveringOwnerSupport.program ids L))
    (.seq attachInput (route ids P L Δ)))

theorem route_rounds {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    (route ids P L Δ).rounds = 4 := rfl

theorem rounds {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    (program ids P L Δ).rounds = 8 := rfl

theorem route_maxBits {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    (route ids P L Δ).maxBits ≤ (L + Δ + 3) * (b + w + 1) := by
  simp only [route, prepare, toList, candidateProgram, toReport, finishProgram, Program.maxBits,
    ProgramMemory.maxBits, readProgram, reportProgram, TaggedGather.maxBits, Nat.zero_max,
    Nat.max_zero, Nat.one_mul]
  apply max_le
  · nlinarith
  · apply max_le
    · nlinarith
    · apply max_le <;> nlinarith

theorem maxBits {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) :
    (program ids P L Δ).maxBits ≤ (L + Δ + 3) * (b + w + 1) := by
  simp only [program, privatePrepare, attachInput, Program.maxBits, ProgramMemory.maxBits,
    GeneralCoveringOwnerSupport.maxBits, Nat.zero_max]
  apply max_le
  · nlinarith
  · exact route_maxBits ids P L Δ

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Literal physical bounded gather, also valid for inconsistent oversized inputs. -/
def gather (K : ℕ) (xs : V → List (V × A)) (v : V) : List (V × A) :=
  TaggedGather.collect (G.neighborFinset v) (TaggedDictionary.bounded K (xs v)).val
    (fun u => (TaggedDictionary.bounded K (xs u.val)).val)

def first {w : ℕ} (P : BitCode A w) (s : V → Input V A) : V → Option (V × A) :=
  (readProgram P).run G s

def candidate {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (s : V → Input V A) (v : V) : List (V × A) :=
  if gate (s v) then (TaggedGather.program ids P 1).run G (fun r => (first G P s r).toList) v else []

def received {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L : ℕ) (s : V → Input V A) : V → List (V × A) :=
  (TaggedGather.program ids P L).run G (candidate G ids P s)

def reports {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L : ℕ) (s : V → Input V A) (r : V) : Report V A :=
  makeReport (s r) (received G ids P L s r)

theorem run_route {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) (s : V → Input V A) :
    (route ids P L Δ).run G s = fun v =>
      finish v (s v) ((reportProgram ids P (Δ + 1)).run G (reports G ids P L s) v) := by
  change finishProgram.run G ((ProgramMemory.carry (reportProgram ids P (Δ + 1))).run G
    (toReport.run G ((ProgramMemory.carry (TaggedGather.program ids P L)).run G
      (candidateProgram.run G ((ProgramMemory.carry (TaggedGather.program ids P 1)).run G
        (toList.run G ((ProgramMemory.carry (readProgram P)).run G (fun u => (s u, s u))))))))) = _
  rw [ProgramMemory.run G (readProgram P)]
  change finishProgram.run G ((ProgramMemory.carry (reportProgram ids P (Δ + 1))).run G
    (toReport.run G ((ProgramMemory.carry (TaggedGather.program ids P L)).run G
      (candidateProgram.run G ((ProgramMemory.carry (TaggedGather.program ids P 1)).run G
        (fun u => ((first G P s u).toList, s u))))))) = _
  rw [ProgramMemory.run G (TaggedGather.program ids P 1)]
  change finishProgram.run G ((ProgramMemory.carry (reportProgram ids P (Δ + 1))).run G
    (toReport.run G ((ProgramMemory.carry (TaggedGather.program ids P L)).run G
      (fun u => (candidate G ids P s u, s u))))) = _
  rw [ProgramMemory.run G (TaggedGather.program ids P L)]
  change finishProgram.run G ((ProgramMemory.carry (reportProgram ids P (Δ + 1))).run G
    (fun u => (reports G ids P L s u, s u))) = _
  rw [ProgramMemory.run G (reportProgram ids P (Δ + 1))]
  rfl

/-- Full physical snapshot: all four hops, including packet truncation and self reads. -/
def snapshot (L Δ : ℕ) (s : V → Input V A) (v : V) : Output V A :=
  let seeds := fun r => (read r (G.neighborFinset r) (s r)
    (fun u => (sending (s u.val), (s u.val).payload))).toList
  let candidates := fun u => if gate (s u) then gather G 1 seeds u else []
  let unions := gather G L candidates
  let packets := fun r => makeReport (s r) (unions r)
  finish v (s v) (TaggedGather.collect (G.neighborFinset v)
    (accept v ⟨(packets v).owner, (TaggedDictionary.bounded (Δ + 1) (packets v).payloads).val⟩)
    (fun u => accept v ⟨(packets u.val).owner,
      (TaggedDictionary.bounded (Δ + 1) (packets u.val).payloads).val⟩))

theorem run_snapshot {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) (s : V → Input V A) :
    (route ids P L Δ).run G s = snapshot G L Δ s := by
  rw [run_route]
  rfl

theorem encoded_snapshot {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) (s : V → Input V A) :
    (route ids P L Δ).runEncoded G s = snapshot G L Δ s :=
  (Program.runEncoded_eq_run G _ s).trans (run_snapshot G ids P L Δ s)

theorem input_retained {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) (s : V → Input V A) (v : V) :
    ((route ids P L Δ).run G s v).input = s v := by
  rw [run_route]
  rfl

theorem none_guard {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) (s : V → Input V A)
    (v : V) (ho : (s v).metadata.owned.owner = none) :
    ((route ids P L Δ).run G s v).payloads = [] := by
  rw [run_route]
  simp [finish, enabled, ho]

theorem noncenter_guard {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ) (s : V → Input V A)
    (v : V) (hc : (s v).metadata.owned.input.center = false) :
    ((route ids P L Δ).run G s v).payloads = [] := by
  rw [run_route]
  simp [finish, enabled, hc]

theorem first_size {w : ℕ} (P : BitCode A w) (s : V → Input V A) (r : V) :
    (TaggedDictionary.keys (first G P s r).toList).card ≤ 1 := by
  cases first G P s r <;> simp [TaggedDictionary.keys]

theorem report_origin {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (K : ℕ)
    (s : V → Report V A) (v : V) (p : V × A)
    (hp : p ∈ (reportProgram ids P K).run G s v) :
    ∃ r ∈ closed G v, (s r).owner = some v ∧ p ∈ (s r).payloads := by
  change p ∈ TaggedGather.collect (G.neighborFinset v)
    (accept v ⟨(s v).owner, (TaggedDictionary.bounded K (s v).payloads).val⟩)
    (fun u => accept v ⟨(s u.val).owner, (TaggedDictionary.bounded K (s u.val).payloads).val⟩) at hp
  rcases (TaggedGather.mem_collect _ _ _ p).mp hp with hp | ⟨u, hp⟩
  · obtain ⟨ho, hp⟩ := (mem_accept _ _ p).mp hp
    exact ⟨v, self_mem_closed G v, ho, TaggedDictionary.bounded_mem K _ p hp⟩
  · obtain ⟨ho, hp⟩ := (mem_accept _ _ p).mp hp
    exact ⟨u.val, (mem_closed G u.val v).mpr (Or.inr
      ((G.mem_neighborFinset v u.val).mp u.property)), ho, TaggedDictionary.bounded_mem K _ p hp⟩

theorem report_delivers {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (K : ℕ)
    (s : V → Report V A) (v r : V) (hr : r ∈ closed G v) (ho : (s r).owner = some v)
    (hsize : (TaggedDictionary.keys (s r).payloads).card ≤ K) (k : V)
    (hk : k ∈ TaggedDictionary.keys (s r).payloads) :
    k ∈ TaggedDictionary.keys ((reportProgram ids P K).run G s v) := by
  have hk' : k ∈ TaggedDictionary.keys (TaggedDictionary.bounded K (s r).payloads).val := by
    rw [TaggedDictionary.keys_bounded_eq K _ hsize]
    exact hk
  obtain ⟨p, hp, hpk⟩ := (TaggedDictionary.mem_keys _ k).mp hk'
  apply (TaggedDictionary.mem_keys _ k).mpr
  refine ⟨p, ?_, hpk⟩
  change p ∈ TaggedGather.collect (G.neighborFinset v)
    (accept v ⟨(s v).owner, (TaggedDictionary.bounded K (s v).payloads).val⟩)
    (fun u => accept v ⟨(s u.val).owner, (TaggedDictionary.bounded K (s u.val).payloads).val⟩)
  apply (TaggedGather.mem_collect _ _ _ p).mpr
  rcases (mem_closed G r v).mp hr with he | ha
  · subst r
    exact Or.inl ((mem_accept _ _ p).mpr ⟨ho, hp⟩)
  · exact Or.inr ⟨⟨r, (G.mem_neighborFinset v r).mpr ha⟩, (mem_accept _ _ p).mpr ⟨ho, hp⟩⟩

/-- Producer composition, with active/payload kept private rather than encoded in metadata. -/
theorem run_program {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ : ℕ)
    (s : V → PrivateInput V A) :
    (program ids P L Δ).run G s = (route ids P L Δ).run G (fun v =>
      ⟨(GeneralCoveringOwnerSupport.program ids L).run G (fun u => (s u).localInput) v,
        (s v).active, (s v).payload⟩) := by
  change (route ids P L Δ).run G (attachInput.run G
    ((ProgramMemory.carry (GeneralCoveringOwnerSupport.program ids L)).run G
      (fun v => ((s v).localInput, ((s v).active, (s v).payload))))) = _
  rw [ProgramMemory.run G (GeneralCoveringOwnerSupport.program ids L)]
  rfl

noncomputable def expected (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (s : V → PrivateInput V A) (v : V) : Input V A :=
  ⟨GeneralCoveringOwnerSupport.expected G C D R L
      (fun u => ⟨(s u).localInput, GeneralCoveringOwners.owner C D R u⟩) v,
    (s v).active, (s v).payload⟩

theorem private_snapshot {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D))
    (hR : ∀ v, (s v).localInput.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).localInput.candidates = C v)
    (hTargets : ∀ v, (s v).localInput.targets = targets v) :
    (program ids P L Δ).runEncoded G s = snapshot G L Δ (expected G C D R L s) := by
  rw [Program.runEncoded_eq_run, run_program,
    GeneralCoveringOwnerSupport.correct G ids C targets D R L hinc hlocal
      (fun v => (s v).localInput) hD hR hC hTargets]
  exact run_snapshot G ids P L Δ _


/-- Reading an actual some-owner uses just its physical star edge or self. -/
theorem read_some {w : ℕ} (P : BitCode A w) (s : V → Input V A) (r i : V)
    (ho : (s r).metadata.owned.owner = some i) (hstar : i = r ∨ G.Adj i r) :
    first G P s r = if sending (s i) then some (i, (s i).payload) else none := by
  change read r (G.neighborFinset r) (s r) (fun u => (sending (s u.val), (s u.val).payload)) = _
  simp only [read, ho]
  by_cases he : i = r
  · subst i
    simp only [↓reduceIte]
  · have hn : i ∈ G.neighborFinset r := (G.mem_neighborFinset r i).mpr ((hstar.resolve_left he).symm)
    simp only [if_neg he, dif_pos hn]

theorem first_correct {w : ℕ} (P : BitCode A w) (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (r : V) :
    first G P (expected G C D R L s) r =
      match GeneralCoveringOwners.owner C D R r with
      | none => none
      | some i => if (s i).active then some (i, (s i).payload) else none := by
  cases ho : GeneralCoveringOwners.owner C D R r with
  | none =>
    change read r (G.neighborFinset r) (expected G C D R L s r)
      (fun u => (sending (expected G C D R L s u.val), (s u.val).payload)) = none
    simp only [read, expected, GeneralCoveringOwnerSupport.expected, ho]
  | some i =>
    have hi := GeneralCoveringOwners.owner_mem C D R ho
    have hs : sending (expected G C D R L s i) = (s i).active := by
      simp [sending, expected, GeneralCoveringOwnerSupport.expected, hD i, hi]
    simpa only [hs] using read_some G P (expected G C D R L s) r i ho
      (GeneralCoveringOwners.owner_star G C D R hlocal ho)

def activeSet (s : V → PrivateInput V A) : Finset V := Finset.univ.filter (fun v => (s v).active = true)

theorem mem_activeSet (s : V → PrivateInput V A) (v : V) :
    v ∈ activeSet s ↔ (s v).active = true := by simp [activeSet]

theorem first_keys_iff {w : ℕ} (P : BitCode A w) (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (r k : V) :
    k ∈ TaggedDictionary.keys (first G P (expected G C D R L s) r).toList ↔
      GeneralCoveringOwners.owner C D R r = some k ∧ k ∈ activeSet s := by
  rw [first_correct G P C D R L hlocal s hD r, mem_activeSet]
  cases ho : GeneralCoveringOwners.owner C D R r with
  | none => simp [TaggedDictionary.keys]
  | some i =>
    by_cases he : k = i
    · subst k
      cases ha : (s i).active <;> simp [TaggedDictionary.keys, ha]
    · have hn : i ≠ k := Ne.symm he
      cases ha : (s i).active <;> simp [TaggedDictionary.keys, ha, he, hn]

theorem first_consistent {w : ℕ} (P : BitCode A w) (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (r : V) :
    TaggedDictionary.Consistent (fun v => (s v).payload) (first G P (expected G C D R L s) r).toList := by
  intro p hp
  rw [first_correct G P C D R L hlocal s hD r] at hp
  cases ho : GeneralCoveringOwners.owner C D R r with
  | none => simp [ho] at hp
  | some i =>
    cases ha : (s i).active
    · simp [ho, ha] at hp
    · have he : p = (i, (s i).payload) := by simpa [ho, ha] using hp
      subst p
      rfl

theorem gate_expected (C : V → Finset V) (D R : Finset V) (L : ℕ) (s : V → PrivateInput V A) (v : V) :
    gate (expected G C D R L s v) =
      decide (v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L) := by
  by_cases ha : v ∈ CoveringSupport.admissible C R <;>
    by_cases hh : v ∈ GeneralCoveringOwnerSupport.heavy G C D R L <;>
      simp [gate, expected, GeneralCoveringOwnerSupport.expected, ha, hh]

theorem candidate_keys {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (v : V) :
    TaggedDictionary.keys (candidate G ids P (expected G C D R L s) v) =
      lightSupport G C D R L v ∩ activeSet s := by
  rw [candidate, gate_expected]
  by_cases hg : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · simp only [decide_eq_true hg, ↓reduceIte]
    rw [TaggedGather.keys_correct G ids P 1 _ (first_size G P _) v, lightSupport, if_pos hg]
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨r, hr, hk⟩
      obtain ⟨ho, ha⟩ := (first_keys_iff G P C D R L hlocal s hD r k).mp hk
      exact ⟨(GeneralCoveringOwnerSupport.mem_support G C D R v k).mpr ⟨r, hr, ho⟩, ha⟩
    · rintro ⟨hk, ha⟩
      obtain ⟨r, hr, ho⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R v k).mp hk
      exact ⟨r, hr, (first_keys_iff G P C D R L hlocal s hD r k).mpr ⟨ho, ha⟩⟩
  · simp [hg, lightSupport, TaggedDictionary.keys]

theorem candidate_bound {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (v : V) :
    (TaggedDictionary.keys (candidate G ids P (expected G C D R L s) v)).card ≤ L := by
  rw [candidate_keys G ids P C D R L hlocal s hD v]
  exact (Finset.card_le_card Finset.inter_subset_left).trans (lightSupport_bound G C D R L v)

theorem candidate_consistent {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (v : V) :
    TaggedDictionary.Consistent (fun v => (s v).payload) (candidate G ids P (expected G C D R L s) v) := by
  unfold candidate
  split
  · exact TaggedGather.consistent G ids P 1 _ _ (first_consistent G P C D R L hlocal s hD) v
  · intro p hp
    simp at hp

theorem received_keys {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (r : V) :
    TaggedDictionary.keys (received G ids P L (expected G C D R L s) r) =
      (closed G r).biUnion (fun v => lightSupport G C D R L v ∩ activeSet s) := by
  rw [received, TaggedGather.keys_correct G ids P L _ (candidate_bound G ids P C D R L hlocal s hD) r]
  have he : (fun v => TaggedDictionary.keys (candidate G ids P (expected G C D R L s) v)) =
      fun v => lightSupport G C D R L v ∩ activeSet s := funext (candidate_keys G ids P C D R L hlocal s hD)
  rw [he]

theorem received_consistent {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (r : V) :
    TaggedDictionary.Consistent (fun v => (s v).payload) (received G ids P L (expected G C D R L s) r) :=
  TaggedGather.consistent G ids P L _ _ (candidate_consistent G ids P C D R L hlocal s hD) r

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _

/-- Capacity is a consequence of the actual graph degree, including a possible self key. -/
theorem supportUnion_subset (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : D) (r : V)
    (ho : GeneralCoveringOwners.owner C D R r = some i.val) :
    GeneralCoveringOwnerDiscoveryCorrect.supportUnion G C D R L r ⊆
      insert i.val (GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i) := by
  intro j hj
  by_cases he : j = i.val
  · exact Finset.mem_insert.mpr (Or.inl he)
  · apply Finset.mem_insert_of_mem
    rw [← GeneralCoveringOwnerDiscoveryCorrect.root_neighbors G C D R L hlocal i]
    have hr : r ∈ closed G i.val := (mem_closed G r i.val).mpr
      ((GeneralCoveringOwners.owner_star G C D R hlocal ho).elim (fun h => Or.inl h.symm) Or.inr)
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, ho⟩, Finset.mem_erase.mpr ⟨he, hj⟩⟩

theorem received_bound {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D))
    (i : D) (hlow : (ownerGraph G C D R L).degree i ≤ Δ) (r : V)
    (ho : GeneralCoveringOwners.owner C D R r = some i.val) :
    (TaggedDictionary.keys (received G ids P L (expected G C D R L s) r)).card ≤ Δ + 1 := by
  rw [received_keys G ids P C D R L hlocal s hD r]
  have hsub : (closed G r).biUnion (fun v => lightSupport G C D R L v ∩ activeSet s) ⊆
      insert i.val (GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i) := by
    intro j hj
    obtain ⟨v, hv, hjv⟩ := Finset.mem_biUnion.mp hj
    exact supportUnion_subset G C D R L hlocal i r ho
      (Finset.mem_biUnion.mpr ⟨v, hv, (Finset.mem_inter.mp hjv).1⟩)
  have hc : (GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i).card =
      (ownerGraph G C D R L).degree i := by
    calc
      _ = ((ownerGraph G C D R L).neighborFinset i).card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      _ = _ := rfl
  have hb := Finset.card_insert_le i.val (GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i)
  rw [hc] at hb
  exact (Finset.card_le_card hsub).trans (hb.trans (Nat.add_le_add_right hlow 1))

theorem route_consistent {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (v : V) :
    TaggedDictionary.Consistent (fun v => (s v).payload)
      ((route ids P L Δ).run G (expected G C D R L s) v).payloads := by
  rw [run_route]
  intro p hp
  have hp' : p ∈ (reportProgram ids P (Δ + 1)).run G (reports G ids P L (expected G C D R L s)) v := by
    simp only [finish] at hp
    split_ifs at hp <;> first | exact hp | simp at hp
  obtain ⟨r, _, _, hr⟩ := report_origin G ids P (Δ + 1) _ v p hp'
  have hr' : p ∈ received G ids P L (expected G C D R L s) r := by
    exact makeReport_mem _ _ p hr
  exact received_consistent G ids P C D R L hlocal s hD r p hr'


/-- No spurious sender keys: only active owners adjacent to the receiver,
with a possible self key. This statement does not require a low degree. -/
theorem route_keys_subset {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D)) (i : D) :
    TaggedDictionary.keys ((route ids P L Δ).run G (expected G C D R L s) i.val).payloads ⊆
      insert i.val (GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i) ∩ activeSet s := by
  intro j hj
  rw [run_route] at hj
  obtain ⟨p, hp, hpk⟩ := (TaggedDictionary.mem_keys _ j).mp hj
  have hp' : p ∈ (reportProgram ids P (Δ + 1)).run G (reports G ids P L (expected G C D R L s)) i.val := by
    simp only [finish] at hp
    split_ifs at hp <;> first | exact hp | simp at hp
  obtain ⟨r, _, ho, hr⟩ := report_origin G ids P (Δ + 1) _ i.val p hp'
  have hor : GeneralCoveringOwners.owner C D R r = some i.val := by
    simpa only [reports, makeReport_owner, expected, GeneralCoveringOwnerSupport.expected] using ho
  have hk : j ∈ TaggedDictionary.keys (received G ids P L (expected G C D R L s) r) :=
    (TaggedDictionary.mem_keys _ j).mpr ⟨p, makeReport_mem _ _ p hr, hpk⟩
  rw [received_keys G ids P C D R L hlocal s hD r] at hk
  obtain ⟨v, hv, hjv⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨hl, ha⟩ := Finset.mem_inter.mp hjv
  exact Finset.mem_inter.mpr ⟨supportUnion_subset G C D R L hlocal i r hor
    (Finset.mem_biUnion.mpr ⟨v, hv, hl⟩), ha⟩

theorem delivers_key {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D))
    (i : D) (hlow : (ownerGraph G C D R L).degree i ≤ Δ) (j : V)
    (hj : j ∈ GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i) (ha : (s j).active = true) :
    j ∈ TaggedDictionary.keys ((route ids P L Δ).run G (expected G C D R L s) i.val).payloads := by
  rw [← GeneralCoveringOwnerDiscoveryCorrect.root_neighbors G C D R L hlocal i] at hj
  obtain ⟨r, hr, hjr⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨hstar, ho⟩ := Finset.mem_filter.mp hr
  obtain ⟨_, hju⟩ := Finset.mem_erase.mp hjr
  obtain ⟨v, hv, hjv⟩ := Finset.mem_biUnion.mp hju
  have hk : j ∈ TaggedDictionary.keys (received G ids P L (expected G C D R L s) r) := by
    rw [received_keys G ids P C D R L hlocal s hD r]
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_inter.mpr ⟨hjv, (mem_activeSet s j).mpr ha⟩⟩
  have he : reports G ids P L (expected G C D R L s) r =
      ⟨some i.val, received G ids P L (expected G C D R L s) r⟩ := by
    simp only [reports, makeReport, expected, GeneralCoveringOwnerSupport.expected, ho]
  have hen : enabled i.val (expected G C D R L s i.val) = true := by
    simp [enabled, expected, GeneralCoveringOwnerSupport.expected, hD i.val, i.property,
      GeneralCoveringOwners.owner_center C D R i.property]
  rw [run_route]
  change j ∈ TaggedDictionary.keys (if enabled i.val (expected G C D R L s i.val) then
    (reportProgram ids P (Δ + 1)).run G (reports G ids P L (expected G C D R L s)) i.val else [])
  rw [if_pos hen]
  apply report_delivers G ids P (Δ + 1) _ i.val r hstar
  · rw [he]
  · rw [he]
    exact received_bound G ids P C D R L Δ hlocal s hD i hlow r ho
  · rw [he]
    exact hk

/-- Exact low-center neighbor keys; self reception is deliberately removed. -/
theorem low_keys {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D))
    (i : D) (hlow : (ownerGraph G C D R L).degree i ≤ Δ) :
    (TaggedDictionary.keys ((route ids P L Δ).run G (expected G C D R L s) i.val).payloads).erase i.val =
      GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i ∩ activeSet s := by
  ext j
  constructor
  · intro hj
    obtain ⟨hne, hk⟩ := Finset.mem_erase.mp hj
    obtain ⟨hi, ha⟩ := Finset.mem_inter.mp (route_keys_subset G ids P C D R L Δ hlocal s hD i hk)
    rcases Finset.mem_insert.mp hi with he | hn
    · exact False.elim (hne he)
    · exact Finset.mem_inter.mpr ⟨hn, ha⟩
  · intro hj
    obtain ⟨hn, ha⟩ := Finset.mem_inter.mp hj
    have hroot := hn
    rw [← GeneralCoveringOwnerDiscoveryCorrect.root_neighbors G C D R L hlocal i] at hroot
    obtain ⟨r, _, hjr⟩ := Finset.mem_biUnion.mp hroot
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hjr).1,
      delivers_key G ids P C D R L Δ hlocal s hD i hlow j hn ((mem_activeSet s j).mp ha)⟩

theorem lookup_correct {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A) (hD : ∀ v, (s v).localInput.center = decide (v ∈ D))
    (i : D) (hlow : (ownerGraph G C D R L).degree i ≤ Δ) (j : V)
    (hj : j ∈ GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i) (ha : (s j).active = true) :
    TaggedDictionary.lookup ((route ids P L Δ).run G (expected G C D R L s) i.val).payloads j = some (s j).payload :=
  TaggedDictionary.lookup_correct (fun v => (s v).payload) _
    (route_consistent G ids P C D R L Δ hlocal s hD i.val) j
    (delivers_key G ids P C D R L Δ hlocal s hD i hlow j hj ha)

/-- Correctness of the actual encoded eight-round private program. No
metadata, neighbor list or per-representative capacity is a hypothesis. -/
theorem private_correct {b w : ℕ} (ids : BitCode V b) (P : BitCode A w)
    (C targets : V → Finset V) (D R : Finset V) (L Δ : ℕ)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (s : V → PrivateInput V A)
    (hD : ∀ v, (s v).localInput.center = decide (v ∈ D))
    (hR : ∀ v, (s v).localInput.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).localInput.candidates = C v)
    (hTargets : ∀ v, (s v).localInput.targets = targets v) :
    let out := (program ids P L Δ).runEncoded G s
    (∀ v, (out v).input.metadata.owned.input = (s v).localInput ∧
      (out v).input.active = (s v).active ∧ (out v).input.payload = (s v).payload) ∧
    (∀ v, TaggedDictionary.Consistent (fun u => (s u).payload) (out v).payloads) ∧
    (∀ i : D, TaggedDictionary.keys (out i.val).payloads ⊆
      insert i.val (GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i) ∩ activeSet s) ∧
    (∀ i : D, (ownerGraph G C D R L).degree i ≤ Δ →
      (TaggedDictionary.keys (out i.val).payloads).erase i.val =
        GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i ∩ activeSet s ∧
      ∀ j ∈ GeneralCoveringOwnerDiscoveryCorrect.neighbors G C D R L i,
        (s j).active = true → TaggedDictionary.lookup (out i.val).payloads j = some (s j).payload) ∧
    (∀ v, GeneralCoveringOwners.owner C D R v = none ∨ v ∉ D → (out v).payloads = []) := by
  have hr := private_snapshot G ids P C targets D R L Δ hinc hlocal s hD hR hC hTargets
  rw [← run_snapshot G ids P L Δ (expected G C D R L s)] at hr
  dsimp only
  rw [hr]
  refine ⟨?_, route_consistent G ids P C D R L Δ hlocal s hD,
    route_keys_subset G ids P C D R L Δ hlocal s hD, ?_, ?_⟩
  · intro v
    rw [input_retained]
    exact ⟨rfl, rfl, rfl⟩
  · intro i hi
    refine ⟨low_keys G ids P C D R L Δ hlocal s hD i hi, ?_⟩
    intro j hj ha
    exact lookup_correct G ids P C D R L Δ hlocal s hD i hi j hj ha
  · intro v hv
    rcases hv with hn | hc
    · exact none_guard G ids P L Δ _ v hn
    · apply noncenter_guard G ids P L Δ _ v
      change (s v).localInput.center = false
      rw [hD v]
      exact decide_eq_false hc

theorem logarithmic_bits {b w : ℕ} (ids : BitCode V b) (P : BitCode A w) (L Δ n c d : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) (hmsg : w ≤ d * Nat.clog 2 (n + 2)) :
    (program ids P L Δ).maxBits ≤ ((L + Δ + 3) * (c + d + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : b + w + 1 ≤ (c + d + 1) * Nat.clog 2 (n + 2) := by nlinarith
  apply (maxBits ids P L Δ).trans
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (L + Δ + 3) hb

end Paper.GeneralCoveringOwnerPayloadRoute

#print axioms Paper.GeneralCoveringOwnerPayloadRoute.makeReport_owner
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.makeReport_mem
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.mem_accept
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.route_rounds
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.rounds
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.route_maxBits
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.maxBits
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.run_route
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.run_snapshot
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.encoded_snapshot
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.input_retained
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.none_guard
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.noncenter_guard
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.first_size
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.report_origin
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.report_delivers
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.run_program
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.private_snapshot
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.read_some
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.first_correct
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.mem_activeSet
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.first_keys_iff
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.first_consistent
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.gate_expected
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.candidate_keys
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.candidate_bound
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.candidate_consistent
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.received_keys
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.received_consistent
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.supportUnion_subset
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.received_bound
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.route_consistent
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.route_keys_subset
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.delivers_key
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.low_keys
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.lookup_correct
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.private_correct
#print axioms Paper.GeneralCoveringOwnerPayloadRoute.logarithmic_bits
