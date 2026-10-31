import Paper.Solver.LocalSearch.GeneralCoveringTaskGeometry
import Paper.Preliminaries.SetNeighborhood
import Paper.Preliminaries.PrefixSet
import Paper.Communication.ProgramMemory
import Paper.Communication.EncodedProgram

/-! Executable two-stage discovery core for actual optional C-owners.
Only gated local supports are broadcast. Bounded reports carry an Option
address, and include physical self reception. Original metadata is retained.
This unit proves the exact physical snapshot and encoded/resource contracts;
its equality to ownerGraph neighborhoods and degree flags is a later bridge. -/
namespace Paper.GeneralCoveringOwnerDiscovery
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

structure Report (V : Type) where
  owner : Option V
  ids : Finset V

structure Output (V : Type) where
  metadata : GeneralCoveringOwnerSupport.State V
  neighbors : Finset V
  high : Bool

def outgoing (L : ℕ) (s : GeneralCoveringOwnerSupport.State V) : Finset V :=
  if s.admissible && !s.heavy then PrefixSet.take L s.support else ∅

theorem outgoing_bound (L : ℕ) (s : GeneralCoveringOwnerSupport.State V) : (outgoing L s).card ≤ L := by
  unfold outgoing
  split
  · exact PrefixSet.bound _ _
  · simp

def makeReport (Δ : ℕ) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V) : Report V :=
  match s.owned.owner with
  | none => ⟨none, ∅⟩
  | some i => ⟨some i, PrefixSet.take (Δ + 1) (raw.erase i)⟩

theorem makeReport_owner (Δ : ℕ) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V) :
    (makeReport Δ raw s).owner = s.owned.owner := by
  cases ho : s.owned.owner <;> simp [makeReport, ho]

theorem makeReport_bound (Δ : ℕ) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V) :
    (makeReport Δ raw s).ids.card ≤ Δ + 1 := by
  cases ho : s.owned.owner with
  | none => simp [makeReport, ho]
  | some i => simpa only [makeReport, ho] using PrefixSet.bound (Δ + 1) (raw.erase i)

def accept (v : V) (r : Report V) : Finset V := if r.owner = some v then r.ids else ∅

theorem accept_none (v : V) (r : Report V) (ho : r.owner = none) : accept v r = ∅ := by
  simp [accept, ho]

def decode {f : ℕ} (m : Option V × {l : List V // l.length ≤ f}) : Report V :=
  ⟨m.1, m.2.val.toFinset⟩

def reportRound (f : ℕ) : Round V (Report V) (Finset V) (Option V × {l : List V // l.length ≤ f}) where
  send _ _ s := (s.owner, ListIncidenceBroadcast.packet f s.ids)
  update v N own msg := accept v own ∪ N.attach.biUnion (fun u => accept v (decode (msg u)))

def reportProgram {bits : ℕ} (ids : BitCode V bits) (f : ℕ) : Program V (Report V) (Finset V) :=
  .broadcast ((bits + 1) + f * (bits + 1))
    (PacketCode.product ids.option (ListPacket.bounded ids f)) (reportRound f)

def enabled (v : V) (s : GeneralCoveringOwnerSupport.State V) : Bool :=
  s.owned.input.center && decide (s.owned.owner = some v)

def finish (Δ : ℕ) (v : V) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V) : Output V :=
  if enabled v s then
    let ns := PrefixSet.take (Δ + 1) raw
    ⟨s, ns, decide (Δ < ns.card)⟩
  else ⟨s, ∅, false⟩

theorem finish_metadata (Δ : ℕ) (v : V) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V) :
    (finish Δ v raw s).metadata = s := by
  unfold finish
  split <;> rfl

theorem finish_bound (Δ : ℕ) (v : V) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V) :
    (finish Δ v raw s).neighbors.card ≤ Δ + 1 := by
  unfold finish
  split
  · exact PrefixSet.bound _ _
  · simp

theorem finish_none (Δ : ℕ) (v : V) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V)
    (ho : s.owned.owner = none) : finish Δ v raw s = ⟨s, ∅, false⟩ := by
  simp [finish, enabled, ho]

theorem finish_noncenter (Δ : ℕ) (v : V) (raw : Finset V) (s : GeneralCoveringOwnerSupport.State V)
    (hc : s.owned.input.center = false) : finish Δ v raw s = ⟨s, ∅, false⟩ := by
  simp [finish, enabled, hc]

def prepare (L : ℕ) : Program V (GeneralCoveringOwnerSupport.State V)
    (Finset V × GeneralCoveringOwnerSupport.State V) := .local fun _ _ s => (outgoing L s, s)

def prepareReport (Δ : ℕ) : Program V (Finset V × GeneralCoveringOwnerSupport.State V)
    (Report V × GeneralCoveringOwnerSupport.State V) := .local fun _ _ s => (makeReport Δ s.1 s.2, s.2)

def finishProgram (Δ : ℕ) : Program V (Finset V × GeneralCoveringOwnerSupport.State V) (Output V) :=
  .local fun v _ s => finish Δ v s.1 s.2

/-- Public ids,L,Delta only. Metadata comes from the accepted local protocol. -/
def discover {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) :
    Program V (GeneralCoveringOwnerSupport.State V) (Output V) :=
  .seq (prepare L) (.seq (ProgramMemory.carry (SetNeighborhood.program ids L))
    (.seq (prepareReport Δ) (.seq (ProgramMemory.carry (reportProgram ids (Δ + 1))) (finishProgram Δ))))

def program {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (Output V) :=
  .seq (GeneralCoveringOwnerSupport.program ids L) (discover ids L Δ)

theorem discover_rounds {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) : (discover ids L Δ).rounds = 2 := rfl

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) : (program ids L Δ).rounds = 6 := rfl

theorem report_maxBits {bits : ℕ} (ids : BitCode V bits) (f : ℕ) :
    (reportProgram ids f).maxBits = (bits + 1) + f * (bits + 1) := rfl

theorem discover_maxBits {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) :
    (discover ids L Δ).maxBits ≤ (L + Δ + 2) * (bits + 1) := by
  simp only [discover, prepare, prepareReport, finishProgram, Program.maxBits, ProgramMemory.maxBits,
    SetNeighborhood.maxBits, report_maxBits, Nat.zero_max, Nat.max_zero]
  apply max_le
  · exact Nat.mul_le_mul_right (bits + 1) (by omega : L ≤ L + Δ + 2)
  · calc
      (bits + 1) + (Δ + 1) * (bits + 1) = (Δ + 2) * (bits + 1) := by ring
      _ ≤ (L + Δ + 2) * (bits + 1) := Nat.mul_le_mul_right _ (by omega)

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ) :
    (program ids L Δ).maxBits ≤ (L + Δ + 2) * (bits + 1) := by
  change max (GeneralCoveringOwnerSupport.program ids L).maxBits (discover ids L Δ).maxBits ≤ _
  apply max_le
  · rw [GeneralCoveringOwnerSupport.maxBits]
    simpa only [one_mul] using
      Nat.mul_le_mul_right (bits + 1) (by omega : 1 ≤ L + Δ + 2)
  · exact discover_maxBits ids L Δ

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem report_correct {bits : ℕ} (ids : BitCode V bits) (f : ℕ) (s : V → Report V)
    (hs : ∀ u, (s u).ids.card ≤ f) (v : V) :
    (reportProgram ids f).run G s v = (closed G v).biUnion (fun u => accept v (s u)) := by
  have hd (u : V) : decode ((s u).owner, ListIncidenceBroadcast.packet f (s u).ids) = s u := by
    simp only [decode, ListIncidenceBroadcast.packet_set f _ (hs u)]
  change accept v (s v) ∪ (G.neighborFinset v).attach.biUnion
    (fun u => accept v (decode ((s u.val).owner, ListIncidenceBroadcast.packet f (s u.val).ids))) = _
  simp only [hd]
  ext x
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach, true_and, mem_closed]
  constructor
  · rintro (hv | ⟨u, hu⟩)
    · exact ⟨v, Or.inl rfl, hv⟩
    · exact ⟨u.val, Or.inr ((G.mem_neighborFinset v u.val).mp u.property), hu⟩
  · rintro ⟨u, he | ha, hu⟩
    · subst u
      exact Or.inl hu
    · exact Or.inr ⟨⟨u, (G.mem_neighborFinset v u).mpr ha⟩, hu⟩

theorem run_discover {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V) :
    (discover ids L Δ).run G s = fun v =>
      let unions := (SetNeighborhood.program ids L).run G (fun u => outgoing L (s u))
      let reports := fun u => makeReport Δ (unions u) (s u)
      finish Δ v ((reportProgram ids (Δ + 1)).run G reports v) (s v) := by
  change (finishProgram Δ).run G ((ProgramMemory.carry (reportProgram ids (Δ + 1))).run G
    ((prepareReport Δ).run G ((ProgramMemory.carry (SetNeighborhood.program ids L)).run G
      (fun u => (outgoing L (s u), s u))))) = _
  rw [ProgramMemory.run G (SetNeighborhood.program ids L)]
  change (finishProgram Δ).run G ((ProgramMemory.carry (reportProgram ids (Δ + 1))).run G
    (fun u => (makeReport Δ ((SetNeighborhood.program ids L).run G (fun w => outgoing L (s w)) u) (s u), s u))) = _
  rw [ProgramMemory.run G (reportProgram ids (Δ + 1))]
  rfl

/-- Exact physical two-stage semantics; no virtual neighborhood is input. -/
def snapshot (L Δ : ℕ) (s : V → GeneralCoveringOwnerSupport.State V) (v : V) : Output V :=
  let unions := fun r => (closed G r).biUnion (fun u => outgoing L (s u))
  finish Δ v ((closed G v).biUnion (fun r => accept v (makeReport Δ (unions r) (s r)))) (s v)

theorem run_snapshot {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V) : (discover ids L Δ).run G s = snapshot G L Δ s := by
  have hu : (SetNeighborhood.program ids L).run G (fun u => outgoing L (s u)) =
      fun r => (closed G r).biUnion (fun u => outgoing L (s u)) :=
    funext (SetNeighborhood.correct G ids L _ (fun u => outgoing_bound L (s u)))
  have hr : (reportProgram ids (Δ + 1)).run G
      (fun r => makeReport Δ ((closed G r).biUnion (fun u => outgoing L (s u))) (s r)) =
      fun v => (closed G v).biUnion
        (fun r => accept v (makeReport Δ ((closed G r).biUnion (fun u => outgoing L (s u))) (s r))) :=
    funext (report_correct G ids (Δ + 1) _ (fun r => makeReport_bound Δ _ (s r)))
  simpa only [hu, hr, snapshot] using run_discover G ids L Δ s

theorem encoded_snapshot {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V) :
    (discover ids L Δ).runEncoded G s = snapshot G L Δ s :=
  (Program.runEncoded_eq_run G _ s).trans (run_snapshot G ids L Δ s)

theorem metadata_retained {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V) (v : V) :
    ((discover ids L Δ).run G s v).metadata = s v := by
  calc
    _ = (snapshot G L Δ s v).metadata :=
      congrArg (fun out : V → Output V => (out v).metadata) (run_snapshot G ids L Δ s)
    _ = s v := finish_metadata Δ v _ _

theorem output_bound {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V) (v : V) :
    ((discover ids L Δ).run G s v).neighbors.card ≤ Δ + 1 := by
  rw [run_snapshot]
  exact finish_bound Δ v _ _

theorem none_guard {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V) (v : V) (ho : (s v).owned.owner = none) :
    (discover ids L Δ).run G s v = ⟨s v, ∅, false⟩ := by
  rw [run_snapshot]
  exact finish_none Δ v _ _ ho

theorem noncenter_guard {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (s : V → GeneralCoveringOwnerSupport.State V) (v : V) (hc : (s v).owned.input.center = false) :
    (discover ids L Δ).run G s v = ⟨s v, ∅, false⟩ := by
  rw [run_snapshot]
  exact finish_noncenter Δ v _ _ hc

theorem outgoing_correct (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (s : GeneralCoveringOwnerSupport.State V) (v : V)
    (had : s.admissible = decide (v ∈ CoveringSupport.admissible C R))
    (hs : s.support = GeneralCoveringOwnerSupport.support G C D R v)
    (hh : s.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G C D R L)) :
    outgoing L s = lightSupport G C D R L v := by
  by_cases hv : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · have hb : (GeneralCoveringOwnerSupport.support G C D R v).card ≤ L := by
      simpa only [lightSupport, if_pos hv] using lightSupport_bound G C D R L v
    simp [outgoing, had, hs, hh, hv.1, hv.2, lightSupport, PrefixSet.eq_self L _ hb]
  · by_cases ha : v ∈ CoveringSupport.admissible C R
    · have hp : v ∈ GeneralCoveringOwnerSupport.heavy G C D R L := by
        by_contra hn
        exact hv ⟨ha, hn⟩
      simp [outgoing, had, hh, ha, hp, lightSupport]
    · simp [outgoing, had, hh, ha, lightSupport]

theorem program_metadata {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ).run G input v).metadata = (GeneralCoveringOwnerSupport.program ids L).run G input v :=
  metadata_retained G ids L Δ _ v

theorem private_input_retained {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (v : V) :
    ((program ids L Δ).run G input v).metadata.owned.input = input v :=
  congrArg (fun t : GeneralCoveringOwnerSupport.State V => t.owned.input) (program_metadata G ids L Δ input v)

theorem program_encoded {bits : ℕ} (ids : BitCode V bits) (L Δ : ℕ)
    (input : V → GeneralCoveringOwners.Input V) :
    (program ids L Δ).runEncoded G input = (program ids L Δ).run G input :=
  Program.runEncoded_eq_run G _ input

theorem private_snapshot {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (D R : Finset V) (L Δ : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (input : V → GeneralCoveringOwners.Input V)
    (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
    (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v) :
    (program ids L Δ).run G input = snapshot G L Δ
      (GeneralCoveringOwnerSupport.expected G C D R L
        (fun v => ⟨input v, GeneralCoveringOwners.owner C D R v⟩)) := by
  change (discover ids L Δ).run G ((GeneralCoveringOwnerSupport.program ids L).run G input) = _
  rw [GeneralCoveringOwnerSupport.correct G ids C targets D R L hinc hlocal input hD hR hC hTargets]
  exact run_snapshot G ids L Δ _

end Paper.GeneralCoveringOwnerDiscovery

#print axioms Paper.GeneralCoveringOwnerDiscovery.outgoing_bound
#print axioms Paper.GeneralCoveringOwnerDiscovery.makeReport_owner
#print axioms Paper.GeneralCoveringOwnerDiscovery.makeReport_bound
#print axioms Paper.GeneralCoveringOwnerDiscovery.accept_none
#print axioms Paper.GeneralCoveringOwnerDiscovery.finish_metadata
#print axioms Paper.GeneralCoveringOwnerDiscovery.finish_bound
#print axioms Paper.GeneralCoveringOwnerDiscovery.finish_none
#print axioms Paper.GeneralCoveringOwnerDiscovery.finish_noncenter
#print axioms Paper.GeneralCoveringOwnerDiscovery.discover_rounds
#print axioms Paper.GeneralCoveringOwnerDiscovery.rounds
#print axioms Paper.GeneralCoveringOwnerDiscovery.report_maxBits
#print axioms Paper.GeneralCoveringOwnerDiscovery.discover_maxBits
#print axioms Paper.GeneralCoveringOwnerDiscovery.maxBits
#print axioms Paper.GeneralCoveringOwnerDiscovery.report_correct
#print axioms Paper.GeneralCoveringOwnerDiscovery.run_discover
#print axioms Paper.GeneralCoveringOwnerDiscovery.run_snapshot
#print axioms Paper.GeneralCoveringOwnerDiscovery.encoded_snapshot
#print axioms Paper.GeneralCoveringOwnerDiscovery.metadata_retained
#print axioms Paper.GeneralCoveringOwnerDiscovery.output_bound
#print axioms Paper.GeneralCoveringOwnerDiscovery.none_guard
#print axioms Paper.GeneralCoveringOwnerDiscovery.noncenter_guard
#print axioms Paper.GeneralCoveringOwnerDiscovery.outgoing_correct
#print axioms Paper.GeneralCoveringOwnerDiscovery.program_metadata
#print axioms Paper.GeneralCoveringOwnerDiscovery.private_input_retained
#print axioms Paper.GeneralCoveringOwnerDiscovery.program_encoded
#print axioms Paper.GeneralCoveringOwnerDiscovery.private_snapshot
