import Paper.Solver.LocalSearch.GeneralCoveringTaskGeometry
import Paper.Communication.EncodedProgram
import Paper.Preliminaries.CohostKnown
import Paper.Solver.LocalSearch.GeneralCoveringFractional

/-! Two actual broadcasts construct one owner's task masks. The first sends
local center part/interior bits, read only at the receiver's actual optional
owner. The second sends own-star membership. Costs and original incidence
lists stay private. Supplied marks are local intermediate fields, with a
proof-side meaning only at centers; I, Bdy and global masks are not inputs.
The accepted OwnerSupport producer is composed literally below. Computing
center marks from a partition and parallel owner routing remain separate. -/
namespace Paper.GeneralCoveringTaskInput
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

structure Fields (B : ℕ) where
  cost : Fin (B + 1)
  part : Bool
  interior : Bool

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringOwnerSupport.State V × Fields B

structure Routed (V : Type) (B : ℕ) where
  input : Input V B
  star : Bool
  interior : Bool

def readOwner (v : V) (N : Finset V) (own : Bool) (msg : N → Bool) : Option V → Bool
  | none => false
  | some u => CohostKnown.read v N own msg u

def routeRound (B : ℕ) : Round V (Input V B) (Routed V B) (Bool × Bool) where
  send _ _ s := (s.2.part, s.2.interior)
  update v N s msg :=
    ⟨s, readOwner v N s.2.part (fun u => (msg u).1) s.1.owned.owner,
      readOwner v N s.2.interior (fun u => (msg u).2) s.1.owned.owner⟩

def route (B : ℕ) : Program V (Input V B) (Routed V B) :=
  .broadcast 2 (BitCode.pairBool BitCode.bool) (routeRound B)

def finishRound (B : ℕ) : Round V (Routed V B) (GeneralCoveringFractional.Input V B) Bool where
  send _ _ s := s.star
  update v N s msg :=
    ⟨s.star || (s.input.1.admissible && !s.input.1.heavy &&
        decide (FlagNeighborhood.selected v N s.star msg).Nonempty),
      s.input.2.cost, s.input.1.residual && s.interior,
      s.input.1.owned.input.candidates, s.input.1.owned.input.targets⟩

def finish (B : ℕ) : Program V (Routed V B) (GeneralCoveringFractional.Input V B) :=
  .broadcast 1 BitCode.bool (finishRound B)

def program (B : ℕ) : Program V (Input V B) (GeneralCoveringFractional.Input V B) :=
  .seq (route B) (finish B)

/-- The existing producer executes while retaining only local fields. -/
def lift {A : Type} (P : Program V A (GeneralCoveringOwnerSupport.State V)) (B : ℕ) :
    Program V (A × Fields B) (GeneralCoveringFractional.Input V B) :=
  .seq (ProgramMemory.carry P) (program B)

def fromOwners {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) :
    Program V (GeneralCoveringOwners.Input V × Fields B) (GeneralCoveringFractional.Input V B) :=
  lift (GeneralCoveringOwnerSupport.program ids L) B

theorem rounds (B : ℕ) : (program (V := V) B).rounds = 2 := rfl

theorem maxBits (B : ℕ) : (program (V := V) B).maxBits = 2 := rfl

theorem lift_rounds {A : Type} (P : Program V A (GeneralCoveringOwnerSupport.State V)) (B : ℕ) :
    (lift P B).rounds = P.rounds + 2 := by
  simp only [lift, Program.rounds, ProgramMemory.rounds, rounds]

theorem lift_maxBits {A : Type} (P : Program V A (GeneralCoveringOwnerSupport.State V)) (B : ℕ) :
    (lift P B).maxBits = max P.maxBits 2 := by
  simp only [lift, Program.maxBits, ProgramMemory.maxBits, maxBits]

theorem fromOwners_rounds {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) :
    (fromOwners ids L B).rounds = 6 := by
  simp only [fromOwners, lift_rounds, GeneralCoveringOwnerSupport.rounds]

theorem fromOwners_maxBits {bits : ℕ} (ids : BitCode V bits) (L B : ℕ) :
    (fromOwners ids L B).maxBits = max (bits + 1) 2 := by
  simp only [fromOwners, lift_maxBits, GeneralCoveringOwnerSupport.maxBits]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- These two sets specify local center marks and stars; neither is runtime data. -/
def centers (D : Finset V) (Q : Finset D) (J : Finset (Low D Q)) : Finset V :=
  J.image (fun i => i.val.val)

def stars (cover : V → Finset V) (D R : Finset V) (Q : Finset D)
    (J : Finset (Low D Q)) : Finset V := J.biUnion (fun i => GeneralCoveringOwners.fiber cover D R i.val.val)

theorem mem_centers (D : Finset V) (Q : Finset D) (J : Finset (Low D Q)) (u : V) :
    u ∈ centers D Q J ↔ ∃ i ∈ J, i.val.val = u := Finset.mem_image

theorem mem_stars (cover : V → Finset V) (D R : Finset V) (Q : Finset D)
    (J : Finset (Low D Q)) (v : V) :
    v ∈ stars cover D R Q J ↔ ∃ i ∈ J, GeneralCoveringOwners.owner cover D R v = some i.val.val := by
  constructor
  · intro hv
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
    exact ⟨i, hi, (Finset.mem_filter.mp hv).2⟩
  · rintro ⟨i, hi, ho⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr
      ⟨GeneralCoveringOwners.owner_domain cover D R ho, ho⟩⟩

theorem read_local (m : V → Bool) (v u : V) (hu : u ∈ closed G v) :
    CohostKnown.read v (G.neighborFinset v) (m v) (fun w => m w.val) u = m u := by
  by_cases he : u = v
  · subst u
    simp [CohostKnown.read]
  · have hn : u ∈ G.neighborFinset v :=
      (G.mem_neighborFinset v u).mpr (((mem_closed G u v).mp hu).resolve_left he)
    simp only [CohostKnown.read, if_neg he, dif_pos hn]

theorem read_owner (cover : V → Finset V) (D R : Finset V) (Q : Finset D)
    (J : Finset (Low D Q)) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (labels : V → Option V) (ho : ∀ v, labels v = GeneralCoveringOwners.owner cover D R v)
    (m : V → Bool) (hm : ∀ u ∈ D, m u = decide (u ∈ centers D Q J)) (v : V) :
    readOwner v (G.neighborFinset v) (m v) (fun u => m u.val) (labels v) =
      decide (v ∈ stars cover D R Q J) := by
  rw [ho v]
  cases hown : GeneralCoveringOwners.owner cover D R v with
  | none =>
    have hv : v ∉ stars cover D R Q J := by
      intro hv
      obtain ⟨i, _, hi⟩ := (mem_stars cover D R Q J v).mp hv
      rw [hown] at hi
      cases hi
    simp [readOwner, hv]
  | some u =>
    have huD := GeneralCoveringOwners.owner_mem cover D R hown
    have hnear : u ∈ closed G v := (mem_closed G u v).mpr
      ((GeneralCoveringOwners.owner_star G cover D R hlocal hown).elim Or.inl (fun h => Or.inr h.symm))
    change CohostKnown.read v (G.neighborFinset v) (m v) (fun w => m w.val) u = _
    rw [read_local G m v u hnear, hm u huD]
    apply Bool.decide_congr
    constructor
    · intro hu
      obtain ⟨i, hi, he⟩ := (mem_centers D Q J u).mp hu
      exact (mem_stars cover D R Q J v).mpr ⟨i, hi, by rw [he]; exact hown⟩
    · intro hv
      obtain ⟨i, hi, he⟩ := (mem_stars cover D R Q J v).mp hv
      exact (mem_centers D Q J u).mpr ⟨i, hi, (Option.some.inj (hown.symm.trans he)).symm⟩

theorem touch_support (cover : V → Finset V) (D R : Finset V) (Q : Finset D)
    (J : Finset (Low D Q)) (v : V) :
    (closed G v ∩ stars cover D R Q J).Nonempty ↔
      ∃ i ∈ J, i.val.val ∈ GeneralCoveringOwnerSupport.support G cover D R v := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hun, hus⟩ := Finset.mem_inter.mp hu
    obtain ⟨i, hi, ho⟩ := (mem_stars cover D R Q J u).mp hus
    exact ⟨i, hi, (GeneralCoveringOwnerSupport.mem_support G cover D R v i.val.val).mpr ⟨u, hun, ho⟩⟩
  · rintro ⟨i, hi, hs⟩
    obtain ⟨u, hun, ho⟩ := (GeneralCoveringOwnerSupport.mem_support G cover D R v i.val.val).mp hs
    exact ⟨u, Finset.mem_inter.mpr ⟨hun, (mem_stars cover D R Q J u).mpr ⟨i, hi, ho⟩⟩⟩

theorem vertices_iff (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (v : V) :
    v ∈ vertices G cover D R L Q I ↔ v ∈ stars cover D R Q I ∨
      ((v ∈ CoveringSupport.admissible cover R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G cover D R L) ∧
        (closed G v ∩ stars cover D R Q I).Nonempty) := by
  simp only [vertices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  change (v ∈ stars cover D R Q I ∨ ∃ i ∈ I, i.val.val ∈ lightSupport G cover D R L v) ↔ _
  constructor
  · rintro (hs | ⟨i, hi, hil⟩)
    · exact Or.inl hs
    · obtain ⟨had, hh, hsup⟩ := (mem_lightSupport G cover D R L v i.val.val).mp hil
      exact Or.inr ⟨⟨had, hh⟩, (touch_support G cover D R Q I v).mpr ⟨i, hi, hsup⟩⟩
  · rintro (hs | ⟨⟨had, hh⟩, ht⟩)
    · exact Or.inl hs
    · obtain ⟨i, hi, hsup⟩ := (touch_support G cover D R Q I v).mp ht
      exact Or.inr ⟨i, hi, (mem_lightSupport G cover D R L v i.val.val).mpr ⟨had, hh, hsup⟩⟩

theorem demands_iff (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (v : V) :
    v ∈ demands G cover D R L Q I Bdy ↔
      v ∈ GeneralCoveringOwnerSupport.residual G cover D R L ∧ v ∈ stars cover D R Q (I \ Bdy) := by
  constructor
  · intro hv
    obtain ⟨hr, i, hi, hb, ho⟩ := Finset.mem_filter.mp hv
    exact ⟨hr, (mem_stars cover D R Q (I \ Bdy) v).mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hb⟩, ho⟩⟩
  · rintro ⟨hr, hs⟩
    obtain ⟨i, hi, ho⟩ := (mem_stars cover D R Q (I \ Bdy) v).mp hs
    obtain ⟨hi, hb⟩ := Finset.mem_sdiff.mp hi
    exact Finset.mem_filter.mpr ⟨hr, i, hi, hb, ho⟩

theorem route_correct (cover : V → Finset V) (D R : Finset V) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (B : ℕ) (s : V → Input V B)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (hp : ∀ u ∈ D, (s u).2.part = decide (u ∈ centers D Q I))
    (hi : ∀ u ∈ D, (s u).2.interior = decide (u ∈ centers D Q (I \ Bdy))) :
    (route B).run G s = fun v =>
      ⟨s v, decide (v ∈ stars cover D R Q I), decide (v ∈ stars cover D R Q (I \ Bdy))⟩ := by
  funext v
  change (⟨s v,
    readOwner v (G.neighborFinset v) (s v).2.part (fun u => (s u.val).2.part) (s v).1.owned.owner,
    readOwner v (G.neighborFinset v) (s v).2.interior (fun u => (s u.val).2.interior)
      (s v).1.owned.owner⟩ : Routed V B) = _
  rw [read_owner G cover D R Q I hlocal (fun u => (s u).1.owned.owner) ho (fun u => (s u).2.part) hp v,
    read_owner G cover D R Q (I \ Bdy) hlocal (fun u => (s u).1.owned.owner) ho
      (fun u => (s u).2.interior) hi v]

noncomputable def expected (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (B : ℕ) (s : V → Input V B) (v : V) : GeneralCoveringFractional.Input V B :=
  ⟨decide (v ∈ vertices G cover D R L Q I), (s v).2.cost,
    decide (v ∈ demands G cover D R L Q I Bdy),
    (s v).1.owned.input.candidates, (s v).1.owned.input.targets⟩

theorem correct (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (B : ℕ) (s : V → Input V B)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (had : ∀ v, (s v).1.admissible = decide (v ∈ CoveringSupport.admissible cover R))
    (hh : ∀ v, (s v).1.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G cover D R L))
    (hr : ∀ v, (s v).1.residual = decide (v ∈ GeneralCoveringOwnerSupport.residual G cover D R L))
    (hp : ∀ u ∈ D, (s u).2.part = decide (u ∈ centers D Q I))
    (hi : ∀ u ∈ D, (s u).2.interior = decide (u ∈ centers D Q (I \ Bdy))) :
    (program B).runEncoded G s = expected G cover D R L Q I Bdy B s := by
  rw [Program.runEncoded_eq_run]
  change (finish B).run G ((route B).run G s) = _
  rw [route_correct G cover D R Q I Bdy B s hlocal ho hp hi]
  funext v
  have hnear := FlagNeighborhood.correct G (stars cover D R Q I) v
  change FlagNeighborhood.selected v (G.neighborFinset v) (decide (v ∈ stars cover D R Q I))
    (fun u => decide (u.val ∈ stars cover D R Q I)) = closed G v ∩ stars cover D R Q I at hnear
  have hactive : (decide (v ∈ stars cover D R Q I) || ((s v).1.admissible && !(s v).1.heavy &&
      decide (closed G v ∩ stars cover D R Q I).Nonempty)) = decide (v ∈ vertices G cover D R L Q I) := by
    rw [had v, hh v]
    simp only [← _root_.decide_not, ← Bool.decide_and, ← Bool.decide_or]
    exact Bool.decide_congr (vertices_iff G cover D R L Q I v).symm
  have hdemand : ((s v).1.residual && decide (v ∈ stars cover D R Q (I \ Bdy))) =
      decide (v ∈ demands G cover D R L Q I Bdy) := by
    rw [hr v, ← Bool.decide_and]
    exact Bool.decide_congr (demands_iff G cover D R L Q I Bdy v).symm
  change (⟨decide (v ∈ stars cover D R Q I) || ((s v).1.admissible && !(s v).1.heavy &&
      decide (FlagNeighborhood.selected v (G.neighborFinset v) (decide (v ∈ stars cover D R Q I))
        (fun u => decide (u.val ∈ stars cover D R Q I))).Nonempty),
    (s v).2.cost, (s v).1.residual && decide (v ∈ stars cover D R Q (I \ Bdy)),
    (s v).1.owned.input.candidates, (s v).1.owned.input.targets⟩ : GeneralCoveringFractional.Input V B) = _
  rw [hnear, hactive, hdemand]
  rfl

theorem preserves (B : ℕ) (s : V → Input V B) (v : V) :
    ((program B).runEncoded G s v).cost = (s v).2.cost ∧
      ((program B).runEncoded G s v).candidates = (s v).1.owned.input.candidates ∧
      ((program B).runEncoded G s v).targets = (s v).1.owned.input.targets := by
  rw [Program.runEncoded_eq_run]
  exact ⟨rfl, rfl, rfl⟩

theorem none_owner (B : ℕ) (s : V → Input V B) (v : V) (ho : (s v).1.owned.owner = none) :
    ((program B).runEncoded G s v).demand = false := by
  rw [Program.runEncoded_eq_run]
  change ((s v).1.residual && readOwner v (G.neighborFinset v) (s v).2.interior
    (fun u => (s u.val).2.interior) (s v).1.owned.owner) = false
  rw [ho]
  simp [readOwner]

theorem not_admissible (B : ℕ) (s : V → Input V B) (v : V) (ha : (s v).1.admissible = false) :
    ((program B).runEncoded G s v).active = ((route B).run G s v).star := by
  rw [Program.runEncoded_eq_run]
  change (((route B).run G s v).star || ((s v).1.admissible && !(s v).1.heavy &&
    decide (FlagNeighborhood.selected v (G.neighborFinset v) ((route B).run G s v).star
      (fun u => ((route B).run G s u.val).star)).Nonempty)) = _
  rw [ha]
  simp

theorem empty_part (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (Bdy : Finset (Low D Q)) (B : ℕ) (s : V → Input V B)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (ho : ∀ v, (s v).1.owned.owner = GeneralCoveringOwners.owner cover D R v)
    (had : ∀ v, (s v).1.admissible = decide (v ∈ CoveringSupport.admissible cover R))
    (hh : ∀ v, (s v).1.heavy = decide (v ∈ GeneralCoveringOwnerSupport.heavy G cover D R L))
    (hr : ∀ v, (s v).1.residual = decide (v ∈ GeneralCoveringOwnerSupport.residual G cover D R L))
    (hp : ∀ u ∈ D, (s u).2.part = false) (hi : ∀ u ∈ D, (s u).2.interior = false) (v : V) :
    ((program B).runEncoded G s v).active = false ∧ ((program B).runEncoded G s v).demand = false := by
  have hp' : ∀ u ∈ D, (s u).2.part = decide (u ∈ centers D Q ∅) := by
    intro u hu
    simpa [centers] using hp u hu
  have hi' : ∀ u ∈ D, (s u).2.interior = decide (u ∈ centers D Q (∅ \ Bdy)) := by
    intro u hu
    simpa [centers] using hi u hu
  rw [correct G cover D R L Q ∅ Bdy B s hlocal ho had hh hr hp' hi']
  simp [expected, vertices, demands]

theorem lift_run {A : Type} (P : Program V A (GeneralCoveringOwnerSupport.State V)) (B : ℕ)
    (s : V → A) (fields : V → Fields B) :
    (lift P B).runEncoded G (fun v => (s v, fields v)) =
      (program B).runEncoded G (fun v => (P.runEncoded G s v, fields v)) := by
  change (program B).runEncoded G
    ((ProgramMemory.carry (X := Fields B) P).runEncoded G (fun v => (s v, fields v))) = _
  rw [Program.runEncoded_eq_run G (ProgramMemory.carry (X := Fields B) P),
    ProgramMemory.run (X := Fields B) G P,
    Program.runEncoded_eq_run G P]

/-- Literal accepted producer, with all task masks constructed afterward. -/
theorem fromOwners_correct {bits : ℕ} (ids : BitCode V bits) (cover targets : V → Finset V)
    (D R : Finset V) (L B : ℕ) (Q : Finset D) (I Bdy : Finset (Low D Q))
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → Fields B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
    (hp : ∀ u ∈ D, (fields u).part = decide (u ∈ centers D Q I))
    (hi : ∀ u ∈ D, (fields u).interior = decide (u ∈ centers D Q (I \ Bdy))) :
    (fromOwners ids L B).runEncoded G (fun v => (s v, fields v)) = fun v =>
      (⟨decide (v ∈ vertices G cover D R L Q I), (fields v).cost,
        decide (v ∈ demands G cover D R L Q I Bdy), cover v, targets v⟩ : GeneralCoveringFractional.Input V B) := by
  change (lift (GeneralCoveringOwnerSupport.program ids L) B).runEncoded G (fun v => (s v, fields v)) = _
  rw [lift_run, Program.runEncoded_eq_run G (GeneralCoveringOwnerSupport.program ids L),
    GeneralCoveringOwnerSupport.correct G ids cover targets D R L hinc hlocal s hD hR hC ht]
  let t : V → Input V B := fun v =>
    (GeneralCoveringOwnerSupport.expected G cover D R L
      (fun u => ⟨s u, GeneralCoveringOwners.owner cover D R u⟩) v, fields v)
  have hcorrect := correct G cover D R L Q I Bdy B t hlocal
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hp hi
  calc
    _ = expected G cover D R L Q I Bdy B t := hcorrect
    _ = _ := by
      funext v
      change (⟨decide (v ∈ vertices G cover D R L Q I), (fields v).cost,
        decide (v ∈ demands G cover D R L Q I Bdy),
        (s v).candidates, (s v).targets⟩ : GeneralCoveringFractional.Input V B) = _
      rw [hC v, ht v]
end Paper.GeneralCoveringTaskInput

#print axioms Paper.GeneralCoveringTaskInput.read_owner
#print axioms Paper.GeneralCoveringTaskInput.touch_support
#print axioms Paper.GeneralCoveringTaskInput.correct
#print axioms Paper.GeneralCoveringTaskInput.preserves
#print axioms Paper.GeneralCoveringTaskInput.none_owner
#print axioms Paper.GeneralCoveringTaskInput.not_admissible
#print axioms Paper.GeneralCoveringTaskInput.empty_part
#print axioms Paper.GeneralCoveringTaskInput.lift_run
#print axioms Paper.GeneralCoveringTaskInput.fromOwners_correct
#print axioms Paper.GeneralCoveringTaskInput.rounds
#print axioms Paper.GeneralCoveringTaskInput.maxBits
#print axioms Paper.GeneralCoveringTaskInput.fromOwners_rounds
#print axioms Paper.GeneralCoveringTaskInput.fromOwners_maxBits
