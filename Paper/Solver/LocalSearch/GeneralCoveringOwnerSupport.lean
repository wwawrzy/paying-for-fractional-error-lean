import Paper.Solver.LocalSearch.GeneralCoveringOwners

/-! Physical S0 supports and exact C-residual flags from actual broadcasts.
Original demand bits determine admissibility through private inverse targets.
Computed optional owners are exchanged, then admissible heavy flags. No
support, admissibility or heavy set is supplied to the program. -/
namespace Paper.GeneralCoveringOwnerSupport
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  owned : GeneralCoveringOwners.Output V
  admissible : Bool
  support : Finset V
  heavy : Bool
  residual : Bool

def admitRound : Round V (GeneralCoveringOwners.Output V) (State V) Bool where
  send _ _ s := s.input.demand
  update v N s msg := ⟨s, decide ((s.input.targets ∩
    FlagNeighborhood.selected v N s.input.demand msg).Nonempty), ∅, false, false⟩

def admit : Program V (GeneralCoveringOwners.Output V) (State V) :=
  .broadcast 1 BitCode.bool admitRound

def supportRound (L : ℕ) : Round V (State V) (State V) (Option V) where
  send _ _ s := s.owned.owner
  update _ N s msg :=
    let labels := MaskedMinimum.pool N s.owned.owner msg
    { s with support := labels, heavy := s.admissible && decide (L < labels.card) }

def collect {bits : ℕ} (ids : BitCode V bits) (L : ℕ) : Program V (State V) (State V) :=
  .broadcast (bits + 1) ids.option (supportRound L)

def repairRound : Round V (State V) (State V) Bool where
  send _ _ s := s.heavy
  update v N s msg := { s with residual := (s.owned.input.demand &&
    decide (s.owned.input.candidates ∩ FlagNeighborhood.selected v N s.heavy msg = ∅)) }

def repair : Program V (State V) (State V) := .broadcast 1 BitCode.bool repairRound

def metadata {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    Program V (GeneralCoveringOwners.Output V) (State V) :=
  .seq admit (.seq (collect ids L) repair)

/-- This entry point computes its owner labels itself from private input. -/
def program {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    Program V (GeneralCoveringOwners.Input V) (State V) :=
  .seq GeneralCoveringOwners.program (metadata ids L)

/-- Public parameters precede the graph, and centers come from literal Run. -/
def initialized {bits : ℕ} (ids : BitCode V bits) (b h f T L : ℕ) :
    Program V (GeneralCoveringInitializerRun.Input V) (State V) :=
  .seq (GeneralCoveringOwners.initialized ids b h f T) (metadata ids L)

theorem metadata_rounds {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    (metadata ids L).rounds = 3 := rfl

theorem metadata_maxBits {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    (metadata ids L).maxBits = bits + 1 := by
  change max 1 (max (bits + 1) 1) = bits + 1
  omega

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    (program ids L).rounds = 4 := rfl

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L : ℕ) :
    (program ids L).maxBits = bits + 1 := by
  simpa only [program, Program.maxBits, GeneralCoveringOwners.maxBits, metadata_maxBits]
    using (max_eq_right (by omega : 1 ≤ bits + 1))

variable [Fintype V]

theorem initialized_rounds {bits : ℕ} (ids : BitCode V bits) (b h f T L : ℕ) :
    (initialized ids b h f T L).rounds = T * (5 + 2 * f) + 6 := by
  simp only [initialized, Program.rounds, GeneralCoveringOwners.initialized_rounds, metadata_rounds]

theorem initialized_maxBits {bits : ℕ} (ids : BitCode V bits) (b h f T L : ℕ) :
    (initialized ids b h f T L).maxBits ≤ max (bits + 1) (f * (bits + 1)) := by
  simp only [initialized, Program.maxBits, metadata_maxBits]
  exact max_le (GeneralCoveringOwners.initialized_maxBits ids b h f T) (le_max_left _ _)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Physical closed-neighborhood support. Optional labels contribute exactly
their present owner, and never an arbitrary default identifier. -/
noncomputable def support (C : V → Finset V) (D R : Finset V) (v : V) : Finset V :=
  (closed G v ∩ (R ∪ D)).biUnion (fun u => (GeneralCoveringOwners.owner C D R u).toFinset)

noncomputable def heavy (C : V → Finset V) (D R : Finset V) (L : ℕ) : Finset V :=
  (CoveringSupport.admissible C R).filter (fun v => L < (support G C D R v).card)

noncomputable def residual (C : V → Finset V) (D R : Finset V) (L : ℕ) : Finset V :=
  R.filter (fun r => C r ∩ heavy G C D R L = ∅)

theorem mem_support (C : V → Finset V) (D R : Finset V) (v i : V) :
    i ∈ support G C D R v ↔ ∃ u ∈ closed G v, GeneralCoveringOwners.owner C D R u = some i := by
  constructor
  · intro hi
    obtain ⟨u, hu, hoi⟩ := Finset.mem_biUnion.mp hi
    exact ⟨u, (Finset.mem_inter.mp hu).1, by simpa using hoi⟩
  · rintro ⟨u, hu, ho⟩
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_inter.mpr
      ⟨hu, GeneralCoveringOwners.owner_domain C D R ho⟩, by simp [ho]⟩

theorem support_labels (C : V → Finset V) (D R : Finset V) (v : V) :
    support G C D R v ⊆ D := by
  intro i hi
  obtain ⟨u, _, ho⟩ := (mem_support G C D R v i).mp hi
  exact GeneralCoveringOwners.owner_mem C D R ho

theorem center_in_support (C : V → Finset V) (D R : Finset V) {i : V} (hi : i ∈ D) :
    i ∈ support G C D R i :=
  (mem_support G C D R i i).mpr ⟨i, self_mem_closed G i, GeneralCoveringOwners.owner_center C D R hi⟩

theorem incidence_label (C : V → Finset V) (D R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {r v i : V}
    (hr : r ∈ R) (hv : v ∈ C r) (ho : GeneralCoveringOwners.owner C D R r = some i) :
    i ∈ support G C D R v :=
  (mem_support G C D R v i).mpr
    ⟨r, (closed_symm G r v).mpr (hlocal r hr hv), ho⟩

theorem heavy_admissible (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    heavy G C D R L ⊆ CoveringSupport.admissible C R := Finset.filter_subset _ _

/-- Every true covering candidate of a residual demand is light and
admissible. No claim about all physical neighbors of that demand is used. -/
theorem residual_candidates (C : V → Finset V) (D R : Finset V) (L : ℕ)
    {r v : V} (hr : r ∈ residual G C D R L) (hv : v ∈ C r) :
    v ∈ CoveringSupport.admissible C R ∧ v ∉ heavy G C D R L ∧
      (support G C D R v).card ≤ L := by
  obtain ⟨hrR, he⟩ := Finset.mem_filter.mp hr
  have had : v ∈ CoveringSupport.admissible C R := Finset.mem_biUnion.mpr ⟨r, hrR, hv⟩
  have hn : v ∉ heavy G C D R L := by
    intro hheavy
    exact (Finset.nonempty_iff_ne_empty.mp ⟨v, Finset.mem_inter.mpr ⟨hv, hheavy⟩⟩) he
  have hnot : ¬ L < (support G C D R v).card := by
    intro hlarge
    exact hn (Finset.mem_filter.mpr ⟨had, hlarge⟩)
  exact ⟨had, hn, by omega⟩

theorem snapshot_admissible (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (v : V) :
    (targets v ∩ (closed G v ∩ R)).Nonempty ↔ v ∈ CoveringSupport.admissible C R := by
  rw [GeneralCoveringInitializerPassLists.snapshot_targets G C targets R hinc hlocal v]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hrR, hvC⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_biUnion.mpr ⟨r, hrR, hvC⟩
  · intro hv
    obtain ⟨r, hrR, hvC⟩ := Finset.mem_biUnion.mp hv
    exact ⟨r, Finset.mem_filter.mpr ⟨hrR, hvC⟩⟩

theorem admit_correct (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → GeneralCoveringOwners.Output V)
    (hR : ∀ r, (s r).input.demand = decide (r ∈ R))
    (hTargets : ∀ v, (s v).input.targets = targets v) :
    admit.run G s = fun v => ⟨s v, decide (v ∈ CoveringSupport.admissible C R), ∅, false, false⟩ := by
  have hflags : (fun r => (s r).input.demand) = fun r => decide (r ∈ R) := funext hR
  funext v
  change (State.mk (s v) (decide (((s v).input.targets ∩
    FlagNeighborhood.program.run G (fun r => (s r).input.demand) v).Nonempty)) ∅ false false) = _
  rw [hflags, hTargets v, FlagNeighborhood.correct G R v]
  apply congrArg (fun flag => State.mk (s v) flag ∅ false false)
  apply Bool.decide_congr
  exact snapshot_admissible G C targets R hinc hlocal v

theorem pool_correct (C : V → Finset V) (D R : Finset V) (labels : V → Option V)
    (ho : ∀ u, labels u = GeneralCoveringOwners.owner C D R u) (v : V) :
    MaskedMinimum.pool (G.neighborFinset v) (labels v) (fun u => labels u.val) = support G C D R v := by
  ext i
  constructor
  · intro hi
    apply MaskedMinimum.pool_origin (G.neighborFinset v) (labels v) (fun u => labels u.val)
      (fun j => j ∈ support G C D R v) ?_ ?_ hi
    · intro j hj
      exact (mem_support G C D R v j).mpr ⟨v, self_mem_closed G v, (ho v).symm.trans hj⟩
    · intro u j hj
      exact (mem_support G C D R v j).mpr ⟨u.val,
        (mem_closed G u.val v).mpr (Or.inr ((G.mem_neighborFinset v u.val).mp u.property)),
        (ho u.val).symm.trans hj⟩
  · intro hi
    obtain ⟨u, hu, hou⟩ := (mem_support G C D R v i).mp hi
    have hmsg : labels u = some i := (ho u).trans hou
    rcases (mem_closed G u v).mp hu with he | ha
    · subst u
      exact MaskedMinimum.mem_pool_self _ _ hmsg
    · exact MaskedMinimum.mem_pool_incoming (G.neighborFinset v) (labels v)
        (fun w => labels w.val) ⟨u, (G.mem_neighborFinset v u).mpr ha⟩ hmsg

theorem collect_correct {bits : ℕ} (ids : BitCode V bits) (C : V → Finset V)
    (D R : Finset V) (L : ℕ) (s : V → State V)
    (ho : ∀ v, (s v).owned.owner = GeneralCoveringOwners.owner C D R v)
    (had : ∀ v, (s v).admissible = decide (v ∈ CoveringSupport.admissible C R)) :
    (collect ids L).run G s = fun v =>
      { s v with support := support G C D R v, heavy := decide (v ∈ heavy G C D R L) } := by
  funext v
  change { s v with
    support := MaskedMinimum.pool (G.neighborFinset v) (s v).owned.owner (fun u => (s u.val).owned.owner),
    heavy := (s v).admissible && decide (L < (MaskedMinimum.pool (G.neighborFinset v)
      (s v).owned.owner (fun u => (s u.val).owned.owner)).card) } = _
  rw [pool_correct G C D R (fun u => (s u).owned.owner) ho v]
  have hb : ((s v).admissible && decide (L < (support G C D R v).card)) =
      decide (v ∈ heavy G C D R L) := by
    rw [had v, ← Bool.decide_and]
    apply Bool.decide_congr
    simp only [heavy, Finset.mem_filter]
  rw [hb]

theorem snapshot_row (C : V → Finset V) (R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {r : V} (hr : r ∈ R) :
    C r ∩ (closed G r ∩ P) = C r ∩ P := by
  ext v
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hvC, _, hvP⟩
    exact ⟨hvC, hvP⟩
  · rintro ⟨hvC, hvP⟩
    exact ⟨hvC, hlocal r hr hvC, hvP⟩

theorem repair_correct (C : V → Finset V) (D R : Finset V) (L : ℕ) (s : V → State V)
    (hh : ∀ v, (s v).heavy = decide (v ∈ heavy G C D R L))
    (hR : ∀ r, (s r).owned.input.demand = decide (r ∈ R))
    (hC : ∀ r, (s r).owned.input.candidates = C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    repair.run G s = fun v => { s v with residual := decide (v ∈ residual G C D R L) } := by
  have hflags : (fun v => (s v).heavy) = fun v => decide (v ∈ heavy G C D R L) := funext hh
  funext v
  change { s v with residual := ((s v).owned.input.demand &&
    decide ((s v).owned.input.candidates ∩
      FlagNeighborhood.program.run G (fun u => (s u).heavy) v = ∅)) } = _
  rw [hflags, hR v, hC v, FlagNeighborhood.correct G (heavy G C D R L) v]
  by_cases hv : v ∈ R
  · rw [snapshot_row G C R (heavy G C D R L) hlocal hv]
    simp [residual, hv]
  · simp [residual, hv]

noncomputable def expected (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (s : V → GeneralCoveringOwners.Output V) (v : V) : State V :=
  ⟨s v, decide (v ∈ CoveringSupport.admissible C R), support G C D R v,
    decide (v ∈ heavy G C D R L), decide (v ∈ residual G C D R L)⟩

theorem metadata_correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (D R : Finset V) (L : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → GeneralCoveringOwners.Output V)
    (ho : ∀ v, (s v).owner = GeneralCoveringOwners.owner C D R v)
    (hR : ∀ r, (s r).input.demand = decide (r ∈ R))
    (hC : ∀ r, (s r).input.candidates = C r) (hTargets : ∀ v, (s v).input.targets = targets v) :
    (metadata ids L).run G s = expected G C D R L s := by
  let a : V → State V := fun v =>
    ⟨s v, decide (v ∈ CoveringSupport.admissible C R), ∅, false, false⟩
  let t : V → State V := fun v =>
    { a v with support := support G C D R v, heavy := decide (v ∈ heavy G C D R L) }
  have hs := collect_correct G ids C D R L a ho (fun _ => rfl)
  have hr := repair_correct G C D R L t (fun _ => rfl) hR hC hlocal
  change repair.run G ((collect ids L).run G (admit.run G s)) = _
  rw [admit_correct G C targets R hinc hlocal s hR hTargets, hs]
  exact hr

/-- Supports and flags are constructed after literal computed owners; only
private input bits/lists and public ids,L are supplied at this entry point. -/
theorem correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (D R : Finset V) (L : ℕ) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → GeneralCoveringOwners.Input V)
    (hD : ∀ v, (s v).center = decide (v ∈ D))
    (hR : ∀ r, (s r).demand = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    (program ids L).run G s = expected G C D R L
      (fun v => ⟨s v, GeneralCoveringOwners.owner C D R v⟩) := by
  change (metadata ids L).run G (GeneralCoveringOwners.program.run G s) = _
  rw [GeneralCoveringOwners.correct G C D R s hD hR hC hlocal]
  exact metadata_correct G ids C targets D R L hinc hlocal
    (fun v => ⟨s v, GeneralCoveringOwners.owner C D R v⟩) (fun _ => rfl) hR hC hTargets

/-- Complete composition with the accepted initializer. No center, owner,
support, admissible or heavy oracle is an input to this literal program. -/
theorem initialized_correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T L : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (s : V → GeneralCoveringInitializerRun.Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    (initialized ids b h f T L).run G s = expected G C D R L (fun v =>
      ⟨GeneralCoveringOwners.initializerInput ⟨decide (v ∈ D), false⟩ (s v),
        GeneralCoveringOwners.owner C D R v⟩) := by
  change (metadata ids L).run G ((GeneralCoveringOwners.initialized ids b h f T).run G s) = _
  rw [GeneralCoveringOwners.initialized_correct G ids C targets b h f T hb R
    hinc hlocal hrows s hR hC hTargets]
  exact metadata_correct G ids C targets (GeneralCoveringInitializerRun.selected C b h f R T) R L
    hinc hlocal (fun v =>
      ⟨GeneralCoveringOwners.initializerInput
        ⟨decide (v ∈ GeneralCoveringInitializerRun.selected C b h f R T), false⟩ (s v),
        GeneralCoveringOwners.owner C (GeneralCoveringInitializerRun.selected C b h f R T) R v⟩)
    (fun _ => rfl) hR hC hTargets

end Paper.GeneralCoveringOwnerSupport

#print axioms Paper.GeneralCoveringOwnerSupport.mem_support
#print axioms Paper.GeneralCoveringOwnerSupport.support_labels
#print axioms Paper.GeneralCoveringOwnerSupport.center_in_support
#print axioms Paper.GeneralCoveringOwnerSupport.incidence_label
#print axioms Paper.GeneralCoveringOwnerSupport.heavy_admissible
#print axioms Paper.GeneralCoveringOwnerSupport.residual_candidates
#print axioms Paper.GeneralCoveringOwnerSupport.snapshot_admissible
#print axioms Paper.GeneralCoveringOwnerSupport.admit_correct
#print axioms Paper.GeneralCoveringOwnerSupport.pool_correct
#print axioms Paper.GeneralCoveringOwnerSupport.collect_correct
#print axioms Paper.GeneralCoveringOwnerSupport.repair_correct
#print axioms Paper.GeneralCoveringOwnerSupport.metadata_correct
#print axioms Paper.GeneralCoveringOwnerSupport.correct
#print axioms Paper.GeneralCoveringOwnerSupport.initialized_correct
#print axioms Paper.GeneralCoveringOwnerSupport.rounds
#print axioms Paper.GeneralCoveringOwnerSupport.maxBits
#print axioms Paper.GeneralCoveringOwnerSupport.initialized_rounds
#print axioms Paper.GeneralCoveringOwnerSupport.initialized_maxBits
