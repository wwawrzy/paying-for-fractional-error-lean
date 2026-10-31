import Paper.Endpoints.Components.PhysicalAcceptance
import Paper.Endpoints.Components.NormalizedComponentSearch

/-! Executable small-component pipeline and exact execution/resource equations.
Acceptance changes only the original active field. Raw normalized search keeps
that field privately, and the decoder checks both participation and word cost.
No solved-component, covering, or optimality theorem is asserted here. -/
namespace Paper.SmallComponentProgram
open BroadcastModel
variable {V : Type} [LinearOrder V]

def radius (K : ℕ) : ℕ := 5 * K - 1

def install {B : ℕ} (s : Bool × GeneralCoveringFractional.Input V B) :
    GeneralCoveringFractional.Input V B := { s.2 with active := s.1 }

def acceptance {b : ℕ} (ids : BitCode V b) (B K : ℕ) :
    Program V (GeneralCoveringFractional.Input V B) (GeneralCoveringFractional.Input V B) :=
  .seq (.local fun _ _ s => (s, s))
    (.seq (ProgramMemory.carry (PhysicalComponentAcceptance.logical B ids (radius K)))
      (.local fun _ _ s => install s))

/-- Accessible raw result: the unchanged optional word and saved acceptance bit. -/
def raw {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B) :
    Program V (GeneralCoveringFractional.Input V B) (Option (SolutionWord.Word V B) × Bool) :=
  .seq (acceptance ids B K)
    (.seq (.local fun _ _ s => (s, s.active))
      (ProgramMemory.carry (NormalizedComponentSearch.program ids (2 * radius K) a B K hB)))

/-- The returned pair is `(solved, selected)`. Rejected vertices, absent words,
and words above the public cost budget all decode to `(false, false)`. -/
def decode {B : ℕ} (K : ℕ) (v : V) (s : Option (SolutionWord.Word V B) × Bool) : Bool × Bool :=
  if s.2 then
    match s.1 with
    | none => (false, false)
    | some w => if SolutionWord.cost w ≤ K then
        (true, decide (0 < SolutionWord.copies w v)) else (false, false)
  else (false, false)

def logical {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B) :
    Program V (GeneralCoveringFractional.Input V B) (Bool × Bool) :=
  .seq (raw ids a B K hB) (.local fun v _ s => decode K v s)

def program {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B) :
    Program V (GeneralCoveringFractional.Input V B) (Bool × Bool) :=
  IncidenceExecution.program B (logical ids a B K hB)

def portProgram {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B) :
    PortBroadcastModel.Program V (GeneralCoveringFractional.Input V B) (Bool × Bool) :=
  KT0Compiler.program ids (program ids a B K hB)

def roundBound (a K : ℕ) : ℕ :=
  3 * radius K + 3 + RecursiveSearch.roundBound (2 * radius K) a K

def messageConstant (a B K c : ℕ) : ℕ :=
  3 * c + RecursiveSearch.extraBits (2 * radius K) a B 1 K + 1

theorem acceptance_rounds {b : ℕ} (ids : BitCode V b) (B K : ℕ) :
    (acceptance ids B K).rounds = 3 * radius K + 1 := by
  simp only [acceptance, Program.rounds, ProgramMemory.rounds,
    PhysicalComponentAcceptance.logical, ComponentAcceptance.program_rounds]
  omega

theorem raw_rounds [Fintype V] {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B) :
    (raw ids a B K hB).rounds =
      3 * radius K + 2 + RecursiveSearch.roundBound (2 * radius K) a K := by
  simp only [raw, Program.rounds, acceptance_rounds, ProgramMemory.rounds,
    NormalizedComponentSearch.rounds]
  omega

theorem rounds [Fintype V] {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B) :
    (program ids a B K hB).rounds = roundBound a K := by
  simp only [program, IncidenceExecution.rounds, logical, Program.rounds, raw_rounds, roundBound]
  omega

theorem port_rounds [Fintype V] {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B) :
    (portProgram ids a B K hB).rounds = 1 + roundBound a K := by
  rw [portProgram, KT0Compiler.program_rounds, rounds]

theorem acceptance_bits {b : ℕ} (ids : BitCode V b) (B K : ℕ) :
    (acceptance ids B K).maxBits ≤ b + 1 := by
  simp only [acceptance, Program.maxBits, ProgramMemory.maxBits,
    PhysicalComponentAcceptance.logical, Program.maxBits, Nat.zero_max, Nat.max_zero]
  exact ComponentAcceptance.program_bits ids (radius K)

theorem logarithmic_bits [Fintype V] {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program ids a B K hB).maxBits ≤ messageConstant a B K c * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hc : c + 1 ≤ messageConstant a B K c := by unfold messageConstant; omega
  have hacc := (acceptance_bits ids B K).trans
    ((BroadcastModel.logarithmic_message_budget n b c hids).1.trans
      (Nat.mul_le_mul_right (Nat.clog 2 (n + 2)) hc))
  have hs := NormalizedComponentSearch.logarithmic_bits ids (2 * radius K) a B K hB n c hids
  have hone : 1 ≤ messageConstant a B K c * Nat.clog 2 (n + 2) := by
    have hcoeff : 1 ≤ messageConstant a B K c := by unfold messageConstant; omega
    exact Nat.mul_le_mul hcoeff hl
  simp only [program, IncidenceExecution.maxBits, logical, raw, Program.maxBits,
    ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact max_le hone (max_le hacc hs)

theorem port_logarithmic_bits [Fintype V] {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (portProgram ids a B K hB).maxBits ≤
      max c (messageConstant a B K c) * Nat.clog 2 (n + 2) :=
  KT0Compiler.logarithmic_bits ids (program ids a B K hB) n c _ hids
    (logarithmic_bits ids a B K hB n c hids)

variable [Fintype V] (I : SimpleGraph V) [DecidableRel I.Adj]

def acceptedInput {B b : ℕ} (ids : BitCode V b) (K : ℕ)
    (s : V → GeneralCoveringFractional.Input V B) : V → GeneralCoveringFractional.Input V B :=
  fun v => { s v with active :=
    (PhysicalComponentAcceptance.logical B ids (radius K)).runEncoded I s v }

theorem acceptedInput_active {B b : ℕ} (ids : BitCode V b) (K : ℕ)
    (s : V → GeneralCoveringFractional.Input V B) (v : V) :
    (acceptedInput I ids K s v).active =
      (ComponentAcceptance.program ids (radius K)).runEncoded I (fun _ => PUnit.unit) v := rfl

theorem acceptedInput_fields {B b : ℕ} (ids : BitCode V b) (K : ℕ)
    (s : V → GeneralCoveringFractional.Input V B) (v : V) :
    (acceptedInput I ids K s v).cost = (s v).cost ∧
    (acceptedInput I ids K s v).demand = (s v).demand ∧
    (acceptedInput I ids K s v).candidates = (s v).candidates ∧
    (acceptedInput I ids K s v).targets = (s v).targets := ⟨rfl, rfl, rfl, rfl⟩

theorem carry_encoded {In Out X : Type} (P : Program V In Out) (s : V → In) (x : V → X) :
    (ProgramMemory.carry P).runEncoded I (fun v => (s v, x v)) =
      fun v => (P.runEncoded I s v, x v) := by
  simp only [Program.runEncoded_eq_run]
  exact ProgramMemory.run I P s x

theorem acceptance_run {b : ℕ} (ids : BitCode V b) (B K : ℕ)
    (s : V → GeneralCoveringFractional.Input V B) :
    (acceptance ids B K).runEncoded I s = acceptedInput I ids K s := by
  change (fun v => install ((ProgramMemory.carry
    (PhysicalComponentAcceptance.logical B ids (radius K))).runEncoded I
      (fun u => (s u, s u)) v)) = _
  rw [carry_encoded]
  rfl

/-- Literal raw optional result and the saved acceptance decision. -/
theorem raw_run {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringFractional.Input V B) :
    (raw ids a B K hB).runEncoded I s = fun v =>
      ((NormalizedComponentSearch.program ids (2 * radius K) a B K hB).runEncoded I
        (acceptedInput I ids K s) v, (acceptedInput I ids K s v).active) := by
  change (ProgramMemory.carry (NormalizedComponentSearch.program ids (2 * radius K) a B K hB)).runEncoded I
    (fun v => ((acceptance ids B K).runEncoded I s v,
      ((acceptance ids B K).runEncoded I s v).active)) = _
  rw [acceptance_run, carry_encoded]

theorem logical_run {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringFractional.Input V B) :
    (logical ids a B K hB).runEncoded I s = fun v => decode K v
      ((NormalizedComponentSearch.program ids (2 * radius K) a B K hB).runEncoded I
        (acceptedInput I ids K s) v, (acceptedInput I ids K s v).active) := by
  change (fun v => decode K v ((raw ids a B K hB).runEncoded I s v)) = _
  rw [raw_run]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem physical_run (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ SevenFoundation.closed G r)
    {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v) (ht : ∀ v, (s v).targets = targets v) :
    (program ids a B K hB).runEncoded G s =
      (logical ids a B K hB).runEncoded (CoveringIncidence.graph C R) s :=
  IncidenceExecution.run_correct G C targets R hinc hlocal B (logical ids a B K hB) s hd hC ht

theorem port_run (ports : PortBroadcastModel.Numbering G)
    {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringFractional.Input V B) :
    (portProgram ids a B K hB).runEncoded G ports s = (program ids a B K hB).runEncoded G s :=
  KT0Compiler.program_encoded_correct G ids (program ids a B K hB) ports s

theorem port_incidence_run (ports : PortBroadcastModel.Numbering G)
    (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ SevenFoundation.closed G r)
    {b : ℕ} (ids : BitCode V b) (a B K : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v) (ht : ∀ v, (s v).targets = targets v) :
    (portProgram ids a B K hB).runEncoded G ports s =
      (logical ids a B K hB).runEncoded (CoveringIncidence.graph C R) s := by
  rw [port_run]
  exact physical_run G C targets R hinc hlocal ids a B K hB s hd hC ht

end Paper.SmallComponentProgram

#print axioms Paper.SmallComponentProgram.acceptedInput_fields
#print axioms Paper.SmallComponentProgram.raw_run
#print axioms Paper.SmallComponentProgram.logical_run
#print axioms Paper.SmallComponentProgram.physical_run
#print axioms Paper.SmallComponentProgram.port_incidence_run
#print axioms Paper.SmallComponentProgram.rounds
#print axioms Paper.SmallComponentProgram.port_rounds
#print axioms Paper.SmallComponentProgram.logarithmic_bits
#print axioms Paper.SmallComponentProgram.port_logarithmic_bits
