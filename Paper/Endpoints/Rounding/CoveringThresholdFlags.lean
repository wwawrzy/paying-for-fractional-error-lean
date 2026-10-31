import Paper.Endpoints.Rounding.CoveringThresholdInput
import Paper.Communication.ProgramMemory

/-! One broadcast bit determines the threshold from the original incidence.
No global promise or global self-covering test is supplied to the program. -/
namespace Paper.CoveringThresholdFlags
open BroadcastModel SevenFoundation
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B : ℕ) where
  demand : Bool
  cost : Fin (B + 1)
  candidates : Finset V
  targets : Finset V
  numerator : ℕ

def self (v : V) {B : ℕ} (s : Input V B) : Bool :=
  s.demand && decide (v ∈ s.candidates)

def finish {B : ℕ} (a q : ℕ) (marked : Finset V) (s : Input V B) :
    CoveringRoundingProtocol.Input V B :=
  let t := if (s.targets ∩ marked).Nonempty then 2 * a + 1 else 2 * a
  ⟨decide (q ≤ t * s.numerator), s.demand, s.cost, s.candidates⟩

def program (B a q : ℕ) : Program V (Input V B) (CoveringRoundingProtocol.Input V B) :=
  .seq (.local fun v _ s => (self v s, s))
    (.seq (ProgramMemory.carry (X := Input V B) FlagNeighborhood.program)
      (.local fun _ _ s => finish a q s.1 s.2))

theorem rounds (B a q : ℕ) : (program (V := V) B a q).rounds = 1 := by
  simp only [program, Program.rounds, ProgramMemory.rounds, FlagNeighborhood.rounds,
    Nat.add_zero, Nat.zero_add]

theorem maxBits (B a q : ℕ) : (program (V := V) B a q).maxBits = 1 := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, FlagNeighborhood.maxBits,
    Nat.max_zero, Nat.zero_max]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def selfDemands {B : ℕ} (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun r => (s r).demand = true ∧ r ∈ (s r).candidates)

theorem self_eq {B : ℕ} (s : V → Input V B) (v : V) :
    self v (s v) = decide (v ∈ selfDemands s) := by
  simp [self, selfDemands, Bool.decide_and]

theorem run {B : ℕ} (a q : ℕ) (s : V → Input V B) :
    (program B a q).runEncoded G s =
      fun v => finish a q (closed G v ∩ selfDemands s) (s v) := by
  simp only [Program.runEncoded_eq_run, program, Program.run]
  rw [ProgramMemory.run]
  have he : (fun v => self v (s v)) = fun v => decide (v ∈ selfDemands s) :=
    funext (self_eq s)
  rw [he]
  funext v
  exact congrArg (fun marked => finish a q marked (s v)) (FlagNeighborhood.correct G (selfDemands s) v)

theorem marked_iff {B : ℕ} (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) (v : V) :
    ((s v).targets ∩ (closed G v ∩ selfDemands s)).Nonempty ↔
      ∃ r, (s r).demand = true ∧ r ∈ (s r).candidates ∧ v ∈ (s r).candidates := by
  constructor
  · rintro ⟨r, hr⟩
    rcases Finset.mem_inter.mp hr with ⟨ht, hc⟩
    have hs := (Finset.mem_filter.mp (Finset.mem_inter.mp hc).2).2
    exact ⟨r, hs.1, hs.2, (hinc v r).mp ht⟩
  · rintro ⟨r, hd, hs, hv⟩
    refine ⟨r, Finset.mem_inter.mpr ⟨(hinc v r).mpr hv, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
    · exact (closed_symm G v r).mp (hlocal r hd hv)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hs⟩

theorem selected_iff {B : ℕ} (a q : ℕ) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) (v : V) :
    ((program B a q).runEncoded G s v).selected = true ↔
      q ≤ (if ∃ r, (s r).demand = true ∧ r ∈ (s r).candidates ∧ v ∈ (s r).candidates
        then 2 * a + 1 else 2 * a) * (s v).numerator := by
  rw [run]
  simp only [finish, decide_eq_true_eq, marked_iff G s hinc hlocal v]

theorem no_self_threshold {B : ℕ} (a q : ℕ) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ (s v).targets ↔ v ∈ (s r).candidates)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r)
    (hself : ∀ r, (s r).demand = true → r ∉ (s r).candidates) (v : V) :
    ((program B a q).runEncoded G s v).selected = true ↔
      q ≤ (2 * a) * (s v).numerator := by
  rw [selected_iff G a q s hinc hlocal v]
  have hn : ¬ ∃ r, (s r).demand = true ∧ r ∈ (s r).candidates ∧ v ∈ (s r).candidates := by
    rintro ⟨r, hd, hr, _⟩
    exact hself r hd hr
  rw [if_neg hn]

def roundedProgram {ids : ℕ} (I : BitCode V ids) (B a q : ℕ) :
    Program V (Input V B) GeneralCoveringRequests.Output :=
  .seq (program B a q) (CoveringRoundingProtocol.normalizedProgram I B)

omit [Fintype V] in
theorem rounded_rounds {ids : ℕ} (I : BitCode V ids) (B a q : ℕ) :
    (roundedProgram I B a q).rounds = 4 := by
  simp only [roundedProgram, Program.rounds, rounds, CoveringRoundingProtocol.normalized_rounds]

omit [Fintype V] in
theorem rounded_maxBits {ids : ℕ} (I : BitCode V ids) (B a q : ℕ) :
    (roundedProgram I B a q).maxBits ≤ max (B + 2) (ids + 1) := by
  simp only [roundedProgram, Program.maxBits, maxBits]
  exact max_le (by omega) (CoveringRoundingProtocol.normalized_maxBits I B)

theorem rounded_run {ids : ℕ} (I : BitCode V ids) (B a q : ℕ) (s : V → Input V B) :
    (roundedProgram I B a q).runEncoded G s =
      (CoveringRoundingProtocol.normalizedProgram I B).runEncoded G
        (fun v => finish a q (closed G v ∩ selfDemands s) (s v)) := by
  have he := run G a q s
  simp only [Program.runEncoded_eq_run] at he ⊢
  change (CoveringRoundingProtocol.normalizedProgram I B).run G ((program B a q).run G s) = _
  rw [he]

end Paper.CoveringThresholdFlags

#print axioms Paper.CoveringThresholdFlags.rounds
#print axioms Paper.CoveringThresholdFlags.maxBits
#print axioms Paper.CoveringThresholdFlags.self_eq
#print axioms Paper.CoveringThresholdFlags.run
#print axioms Paper.CoveringThresholdFlags.marked_iff


#print axioms Paper.CoveringThresholdFlags.selected_iff
#print axioms Paper.CoveringThresholdFlags.no_self_threshold

#print axioms Paper.CoveringThresholdFlags.rounded_rounds
#print axioms Paper.CoveringThresholdFlags.rounded_maxBits
#print axioms Paper.CoveringThresholdFlags.rounded_run
