import Paper.Solver.LocalSearch.GeneralCoveringInitializerRun

/-! Actual owners for arbitrary private covering lists. One center-bit
broadcast suffices: centers own themselves, other demands choose the minimum
of D intersect C(r), and vertices outside R union D have no owner label.
The initializer composition preserves the original private incidence lists. -/
namespace Paper.GeneralCoveringOwners
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

structure Input (V : Type) where
  center : Bool
  demand : Bool
  candidates : Finset V
  targets : Finset V

structure Output (V : Type) where
  input : Input V
  owner : Option V

def round : Round V (Input V) (Output V) Bool where
  send _ _ s := s.center
  update v N s msg := ⟨s, if s.center then some v else if s.demand then
    MaskedMinimum.minimum (FlagNeighborhood.selected v N s.center msg ∩ s.candidates) else none⟩

def program : Program V (Input V) (Output V) := .broadcast 1 BitCode.bool round

def initializerInput (out : GeneralCoveringRequests.Output)
    (s : GeneralCoveringInitializerRun.Input V) : Input V :=
  ⟨out.selected, s.residual, s.candidates, s.targets⟩

/-- All public parameters precede the graph. The accepted initializer's
literal output bit supplies the centers; no owner map is program input. -/
def initialized {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) :
    Program V (GeneralCoveringInitializerRun.Input V) (Output V) :=
  .seq (.local fun _ _ s => (s, s))
    (.seq (ProgramMemory.carry (GeneralCoveringInitializerRun.program ids b h f T))
      (.seq (.local fun _ _ s => initializerInput s.1 s.2) program))

theorem rounds : (program (V := V)).rounds = 1 := rfl

theorem maxBits : (program (V := V)).maxBits = 1 := rfl

def owner (C : V → Finset V) (D R : Finset V) (u : V) : Option V :=
  if u ∈ D then some u else if u ∈ R then MaskedMinimum.minimum (D ∩ C u) else none

theorem owner_center (C : V → Finset V) (D R : Finset V) {u : V} (hu : u ∈ D) :
    owner C D R u = some u := by simp [owner, hu]

/-- Self ownership of a center does not assert that it covers itself.
For noncenters the chosen owner has the exact required C-incidence. -/
theorem owner_incidence (C : V → Finset V) (D R : Finset V) {u i : V}
    (hu : u ∈ R) (hnot : u ∉ D) (ho : owner C D R u = some i) : i ∈ D ∩ C u := by
  apply MaskedMinimum.minimum_mem
  simpa only [owner, if_neg hnot, if_pos hu] using ho

theorem owner_minimum (C : V → Finset V) (D R : Finset V) {u i : V}
    (hu : u ∈ R) (hnot : u ∉ D) (ho : owner C D R u = some i) :
    ∀ j ∈ D ∩ C u, i ≤ j := by
  intro j hj
  have hi : MaskedMinimum.minimum (D ∩ C u) = some i := by
    simpa only [owner, if_neg hnot, if_pos hu] using ho
  obtain ⟨m, hm, hle⟩ := MaskedMinimum.minimum_le hj
  have he : i = m := Option.some.inj (hi.symm.trans hm)
  simpa only [he] using hle

theorem owner_mem (C : V → Finset V) (D R : Finset V) {u i : V}
    (ho : owner C D R u = some i) : i ∈ D := by
  by_cases hd : u ∈ D
  · have he : u = i := Option.some.inj ((owner_center C D R hd).symm.trans ho)
    exact he ▸ hd
  · by_cases hr : u ∈ R
    · exact (Finset.mem_inter.mp (owner_incidence C D R hr hd ho)).1
    · simp [owner, hd, hr] at ho

theorem owner_domain (C : V → Finset V) (D R : Finset V) {u i : V}
    (ho : owner C D R u = some i) : u ∈ R ∪ D := by
  by_cases hd : u ∈ D
  · exact Finset.mem_union_right R hd
  · by_cases hr : u ∈ R
    · exact Finset.mem_union_left D hr
    · simp [owner, hd, hr] at ho

variable [Fintype V]

theorem exists_owner (C : V → Finset V) (D R : Finset V)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) {u : V} (hu : u ∈ R ∪ D) :
    ∃ i ∈ D, owner C D R u = some i := by
  by_cases hd : u ∈ D
  · exact ⟨u, hd, owner_center C D R hd⟩
  · have hr : u ∈ R := (Finset.mem_union.mp hu).resolve_right hd
    obtain ⟨j, hj, hjC⟩ := hcover u hr
    obtain ⟨i, hi, _⟩ := MaskedMinimum.minimum_le (Finset.mem_inter.mpr ⟨hj, hjC⟩)
    have ho : owner C D R u = some i := by simp only [owner, if_neg hd, if_pos hr, hi]
    exact ⟨i, owner_mem C D R ho, ho⟩

def fiber (C : V → Finset V) (D R : Finset V) (i : V) : Finset V :=
  (R ∪ D).filter (fun u => owner C D R u = some i)

theorem fiber_center (C : V → Finset V) (D R : Finset V) {i : V} (hi : i ∈ D) :
    i ∈ fiber C D R i :=
  Finset.mem_filter.mpr ⟨Finset.mem_union_right R hi, owner_center C D R hi⟩

theorem fibers_disjoint (C : V → Finset V) (D R : Finset V) {i j : V} (hne : i ≠ j) :
    Disjoint (fiber C D R i) (fiber C D R j) := by
  apply Finset.disjoint_left.mpr
  intro u hi hj
  exact hne (Option.some.inj ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2))

theorem fibers_cover (C : V → Finset V) (D R : Finset V)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) :
    D.biUnion (fiber C D R) = R ∪ D := by
  ext u
  constructor
  · intro hu
    obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_filter.mp hui).1
  · intro hu
    obtain ⟨i, hi, ho⟩ := exists_owner C D R hcover hu
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hu, ho⟩⟩

theorem initialized_rounds {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) :
    (initialized ids b h f T).rounds = T * (5 + 2 * f) + 3 := by
  simp only [initialized, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringInitializerRun.rounds, rounds, Nat.zero_add, Nat.add_zero]

theorem initialized_maxBits {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) :
    (initialized ids b h f T).maxBits ≤ max (bits + 1) (f * (bits + 1)) := by
  have hp := GeneralCoveringInitializerRun.maxBits ids b h f T
  simp only [initialized, Program.maxBits, ProgramMemory.maxBits, maxBits, Nat.zero_max]
  exact max_le hp ((by omega : 1 ≤ bits + 1).trans (le_max_left _ _))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact execution of the one-bit protocol. Only original demands require
physical locality, and the owner intersection always remains D intersect C. -/
theorem correct (C : V → Finset V) (D R : Finset V) (s : V → Input V)
    (hD : ∀ u, (s u).center = decide (u ∈ D))
    (hR : ∀ u, (s u).demand = decide (u ∈ R))
    (hC : ∀ u, (s u).candidates = C u) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    program.run G s = fun v => ⟨s v, owner C D R v⟩ := by
  funext v
  have hnear := FlagNeighborhood.correct G D v
  change FlagNeighborhood.selected v (G.neighborFinset v) (decide (v ∈ D))
    (fun u => decide (u.val ∈ D)) = closed G v ∩ D at hnear
  change (⟨s v, if (s v).center then some v else if (s v).demand then
    MaskedMinimum.minimum (FlagNeighborhood.selected v (G.neighborFinset v) (s v).center
      (fun u => (s u.val).center) ∩ (s v).candidates) else none⟩ : Output V) = _
  simp only [hD, hR, hC]
  rw [hnear]
  by_cases hd : v ∈ D
  · simp [owner, hd]
  · by_cases hr : v ∈ R
    · have he : (closed G v ∩ D) ∩ C v = D ∩ C v := by
        ext u
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨⟨_, huD⟩, huC⟩
          exact ⟨huD, huC⟩
        · rintro ⟨huD, huC⟩
          exact ⟨⟨hlocal v hr huC, huD⟩, huC⟩
      rw [he]
      simp [owner, hd, hr]
    · simp [owner, hd, hr]

theorem correct_encoded (C : V → Finset V) (D R : Finset V) (s : V → Input V)
    (hD : ∀ u, (s u).center = decide (u ∈ D))
    (hR : ∀ u, (s u).demand = decide (u ∈ R))
    (hC : ∀ u, (s u).candidates = C u) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    program.runEncoded G s = fun v => ⟨s v, owner C D R v⟩ := by
  rw [Program.runEncoded_eq_run]
  exact correct G C D R s hD hR hC hlocal

theorem owner_star (C : V → Finset V) (D R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {u i : V} (ho : owner C D R u = some i) :
    i = u ∨ G.Adj i u := by
  by_cases hd : u ∈ D
  · have he : u = i := Option.some.inj ((owner_center C D R hd).symm.trans ho)
    exact Or.inl he.symm
  · have hr : u ∈ R := (Finset.mem_union.mp (owner_domain C D R ho)).resolve_right hd
    have hiC := (Finset.mem_inter.mp (owner_incidence C D R hr hd ho)).2
    exact ((mem_closed G i u).mp (hlocal u hr hiC)).elim Or.inl (fun ha => Or.inr ha.symm)

theorem fiber_subset_closed (C : V → Finset V) (D R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (i : V) : fiber C D R i ⊆ closed G i := by
  intro u hu
  rcases owner_star G C D R hlocal (Finset.mem_filter.mp hu).2 with he | ha
  · exact (mem_closed G u i).mpr (Or.inl he.symm)
  · exact (mem_closed G u i).mpr (Or.inr ha)

theorem fiber_connected (C : V → Finset V) (D R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {i : V} (hi : i ∈ D) :
    (G.induce (fiber C D R i : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  let root : {v // v ∈ (fiber C D R i : Set V)} := ⟨i, fiber_center C D R hi⟩
  refine ⟨root, ?_⟩
  intro u
  rcases owner_star G C D R hlocal (Finset.mem_filter.mp u.property).2 with he | ha
  · have hs : root = u := Subtype.ext he
    simpa only [hs] using
      (show (G.induce (fiber C D R i : Set V)).Reachable root root from SimpleGraph.Reachable.refl _)
  · exact (show (G.induce (fiber C D R i : Set V)).Adj root u from ha).reachable

theorem run_initialized {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ)
    (s : V → GeneralCoveringInitializerRun.Input V) :
    (initialized ids b h f T).run G s = program.run G (fun v => initializerInput
      ((GeneralCoveringInitializerRun.program ids b h f T).run G s v) (s v)) := by
  change program.run G (fun v => initializerInput
    (((ProgramMemory.carry (GeneralCoveringInitializerRun.program ids b h f T)).run G
      (fun u => (s u, s u)) v).1)
    (((ProgramMemory.carry (GeneralCoveringInitializerRun.program ids b h f T)).run G
      (fun u => (s u, s u)) v).2)) = _
  simp only [ProgramMemory.run]

/-- Owners are computed after the actual accepted initializer. The theorem
does not take a center set or an owner function as an extra program input. -/
theorem initialized_correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (s : V → GeneralCoveringInitializerRun.Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    (initialized ids b h f T).run G s = fun v =>
      ⟨initializerInput ⟨decide (v ∈ D), false⟩ (s v), owner C D R v⟩ := by
  rw [run_initialized, GeneralCoveringInitializerRun.correct G ids C targets b h f T hb R
    hinc hlocal hrows s hR hC hTargets]
  exact correct G C (GeneralCoveringInitializerRun.selected C b h f R T) R
    (fun v => initializerInput
      ⟨decide (v ∈ GeneralCoveringInitializerRun.selected C b h f R T), false⟩ (s v))
    (fun _ => rfl) hR hC hlocal

/-- The literal initialized protocol assigns every member of R union D a
center with star geometry; a noncenter demand has the exact C-incidence. -/
theorem initialized_spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (s : V → GeneralCoveringInitializerRun.Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    ∀ u ∈ R ∪ D, ∃ i ∈ D, ((initialized ids b h f T).run G s u).owner = some i ∧
      (i = u ∨ G.Adj i u) ∧ (u ∉ D → i ∈ C u) := by
  dsimp only
  rw [initialized_correct G ids C targets b h f T hb R hinc hlocal hrows s hR hC hTargets]
  intro u hu
  obtain ⟨i, hi, ho⟩ := exists_owner C (GeneralCoveringInitializerRun.selected C b h f R T) R
    (GeneralCoveringInitializerRun.selected_covers C b h f R T hrows) hu
  refine ⟨i, hi, ho, owner_star G C _ R hlocal ho, ?_⟩
  intro hnot
  have hr : u ∈ R := (Finset.mem_union.mp hu).resolve_right hnot
  exact (Finset.mem_inter.mp (owner_incidence C _ R hr hnot ho)).2

end Paper.GeneralCoveringOwners

#print axioms Paper.GeneralCoveringOwners.correct
#print axioms Paper.GeneralCoveringOwners.correct_encoded
#print axioms Paper.GeneralCoveringOwners.owner_center
#print axioms Paper.GeneralCoveringOwners.owner_incidence
#print axioms Paper.GeneralCoveringOwners.owner_minimum
#print axioms Paper.GeneralCoveringOwners.exists_owner
#print axioms Paper.GeneralCoveringOwners.fibers_disjoint
#print axioms Paper.GeneralCoveringOwners.fibers_cover
#print axioms Paper.GeneralCoveringOwners.fiber_subset_closed
#print axioms Paper.GeneralCoveringOwners.fiber_connected
#print axioms Paper.GeneralCoveringOwners.initialized_correct
#print axioms Paper.GeneralCoveringOwners.initialized_spec
#print axioms Paper.GeneralCoveringOwners.rounds
#print axioms Paper.GeneralCoveringOwners.maxBits
#print axioms Paper.GeneralCoveringOwners.initialized_rounds
#print axioms Paper.GeneralCoveringOwners.initialized_maxBits
