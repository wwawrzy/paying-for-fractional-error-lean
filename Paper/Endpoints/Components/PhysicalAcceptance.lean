import Paper.Endpoints.Components.IncidenceExecution
import Paper.Endpoints.Components.Acceptance
import Paper.Endpoints.Components.IncidenceDiameter
import Paper.Averaging.Tasks.KT0Compiler

/-! Actual component acceptance on the original physical network. The private
covering input first prepares incidence neighbors, then is projected locally to
unit input for the existing logical acceptance program. A KT0 wrapper adds own-ID
discovery. Neither constructor receives a graph or global incidence data.
Acceptance is not a solved-component or exact-search certificate. -/
namespace Paper.PhysicalComponentAcceptance
open BroadcastModel
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def logical (B : ℕ) {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    Program V (GeneralCoveringFractional.Input V B) Bool :=
  .seq (.local fun _ _ _ => PUnit.unit) (ComponentAcceptance.program ids d)

def program (B : ℕ) {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    Program V (GeneralCoveringFractional.Input V B) Bool :=
  IncidenceExecution.program B (logical B ids d)

def portProgram (B : ℕ) {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    PortBroadcastModel.Program V (GeneralCoveringFractional.Input V B) Bool :=
  KT0Compiler.program ids (program B ids d)

theorem rounds (B : ℕ) {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    (program B ids d).rounds = 3 * d + 2 := by
  simp only [program, IncidenceExecution.rounds, logical, Program.rounds,
    ComponentAcceptance.program_rounds]
  omega

theorem bits (B : ℕ) {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    (program B ids d).maxBits ≤ b + 1 := by
  simp only [program, IncidenceExecution.maxBits, logical, Program.maxBits, Nat.zero_max]
  exact max_le (by omega) (ComponentAcceptance.program_bits ids d)

theorem port_rounds (B : ℕ) {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    (portProgram B ids d).rounds = 3 * d + 3 := by
  rw [portProgram, KT0Compiler.program_rounds, rounds]
  omega

theorem port_bits (B : ℕ) {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    (portProgram B ids d).maxBits ≤ b + 1 := by
  rw [portProgram, KT0Compiler.program_maxBits]
  exact max_le (by omega) (bits B ids d)

theorem port_logarithmic_bits (B : ℕ) {b : ℕ} (ids : BitCode V b) (d n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (portProgram B ids d).maxBits ≤ (c + 1) * Nat.clog 2 (n + 2) :=
  (port_bits B ids d).trans (BroadcastModel.logarithmic_message_budget n b c hids).1

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem port_eq (ports : PortBroadcastModel.Numbering G) (B : ℕ)
    {b : ℕ} (ids : BitCode V b) (d : ℕ) (s : V → GeneralCoveringFractional.Input V B) :
    (portProgram B ids d).runEncoded G ports s = (program B ids d).runEncoded G s :=
  KT0Compiler.program_encoded_correct G ids (program B ids d) ports s

variable (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ SevenFoundation.closed G r)
    (B : ℕ) (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v)
    (ht : ∀ v, (s v).targets = targets v)
include hinc hlocal hd hC ht

/-- Equality for literal encoded physical execution, with all incidence data
confined to the specification. -/
theorem run_correct {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    (program B ids d).runEncoded G s =
      (ComponentAcceptance.program ids d).runEncoded (CoveringIncidence.graph C R)
        (fun _ => PUnit.unit) := by
  rw [program, IncidenceExecution.run_correct G C targets R hinc hlocal B
    (logical B ids d) s hd hC ht]
  rfl

theorem port_correct (ports : PortBroadcastModel.Numbering G)
    {b : ℕ} (ids : BitCode V b) (d : ℕ) :
    (portProgram B ids d).runEncoded G ports s =
      (ComponentAcceptance.program ids d).runEncoded (CoveringIncidence.graph C R)
        (fun _ => PUnit.unit) := by
  rw [port_eq]
  exact run_correct G C targets R hinc hlocal B s hd hC ht ids d

theorem uniform {b : ℕ} (ids : BitCode V b) (d : ℕ) {v w : V}
    (p : (CoveringIncidence.graph C R).Walk v w) :
    (program B ids d).runEncoded G s v = (program B ids d).runEncoded G s w := by
  simp only [run_correct G C targets R hinc hlocal B s hd hC ht ids d]
  exact ComponentAcceptance.encoded_uniform _ ids d p

theorem component_uniform {b : ℕ} (ids : BitCode V b) (d : ℕ)
    (X : (CoveringIncidence.graph C R).ConnectedComponent) (x y : X) :
    (program B ids d).runEncoded G s x.val = (program B ids d).runEncoded G s y.val := by
  obtain ⟨p⟩ := X.reachable_of_mem_supp x.property y.property
  exact uniform G C targets R hinc hlocal B s hd hC ht ids d p

/-- Acceptance supplies bounded logical incidence walks within the component;
physical-network distances are not substituted for incidence distances. -/
theorem accepted_diameter {b : ℕ} (ids : BitCode V b) (d : ℕ) {v : V}
    (hv : (program B ids d).runEncoded G s v = true) {u w : V}
    (p : (CoveringIncidence.graph C R).Walk v u)
    (q : (CoveringIncidence.graph C R).Walk v w) :
    ∃ r : (CoveringIncidence.graph C R).Walk u w, r.length ≤ 2 * d := by
  rw [run_correct G C targets R hinc hlocal B s hd hC ht ids d] at hv
  exact ComponentAcceptance.encoded_diameter _ ids d hv p q

theorem small_component {b : ℕ} (ids : BitCode V b) (d : ℕ) (v : V)
    (hdiam : ∀ u w, Nonempty ((CoveringIncidence.graph C R).Walk v u) →
      Nonempty ((CoveringIncidence.graph C R).Walk v w) →
      ∃ p : (CoveringIncidence.graph C R).Walk u w, p.length ≤ d) :
    (program B ids d).runEncoded G s v = true := by
  rw [run_correct G C targets R hinc hlocal B s hd hC ht ids d]
  exact ComponentAcceptance.encoded_small_component _ ids d v hdiam

/-- An actual feasible cover with cost at most `K` suffices for acceptance.
The singleton exception is already included in the incidence diameter theorem;
no optimum witness or nonisolation premise is supplied to this endpoint. -/
theorem covered_component {b : ℕ} (ids : BitCode V b)
    (X : (CoveringIncidence.graph C R).ConnectedComponent)
    (D : Finset V) (K : ℕ) (hK : 1 ≤ K)
    (hc : ∀ u ∈ D, 1 ≤ (s u).cost.val) (hcost : (∑ u ∈ D, (s u).cost.val) ≤ K)
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ u ∈ D, u ∈ C r)
    (v : V) (hv : v ∈ X.supp) :
    (program B ids (5 * K - 1)).runEncoded G s v = true := by
  apply small_component G C targets R hinc hlocal B s hd hC ht ids (5 * K - 1) v
  intro u w hu hw
  have mem_of_walk : ∀ {z : V}, (CoveringIncidence.graph C R).Walk v z → z ∈ X.supp := by
    intro z p
    have he := SimpleGraph.ConnectedComponent.sound p.reachable
    exact he.symm.trans hv
  have hcr : ∀ u ∈ D, (1 : ℝ) ≤ ((s u).cost.val : ℝ) := by
    intro u hu; exact_mod_cast hc u hu
  have hcostr : (∑ u ∈ D, ((s u).cost.val : ℝ)) ≤ (K : ℝ) := by
    exact_mod_cast hcost
  exact CoveringIncidence.component_walk_le_five C R X D
    (fun u => ((s u).cost.val : ℝ)) K hK hcr hcostr hcover
    (mem_of_walk hu.some) (mem_of_walk hw.some)

theorem port_covered_component (ports : PortBroadcastModel.Numbering G)
    {b : ℕ} (ids : BitCode V b)
    (X : (CoveringIncidence.graph C R).ConnectedComponent)
    (D : Finset V) (K : ℕ) (hK : 1 ≤ K)
    (hc : ∀ u ∈ D, 1 ≤ (s u).cost.val) (hcost : (∑ u ∈ D, (s u).cost.val) ≤ K)
    (hcover : ∀ r ∈ R, r ∈ X.supp → ∃ u ∈ D, u ∈ C r)
    (v : V) (hv : v ∈ X.supp) :
    (portProgram B ids (5 * K - 1)).runEncoded G ports s v = true := by
  rw [port_eq]
  exact covered_component G C targets R hinc hlocal B s hd hC ht ids X D K hK hc hcost hcover v hv

end Paper.PhysicalComponentAcceptance

#print axioms Paper.PhysicalComponentAcceptance.run_correct
#print axioms Paper.PhysicalComponentAcceptance.port_correct
#print axioms Paper.PhysicalComponentAcceptance.rounds
#print axioms Paper.PhysicalComponentAcceptance.bits
#print axioms Paper.PhysicalComponentAcceptance.port_rounds
#print axioms Paper.PhysicalComponentAcceptance.port_logarithmic_bits
#print axioms Paper.PhysicalComponentAcceptance.component_uniform
#print axioms Paper.PhysicalComponentAcceptance.accepted_diameter
#print axioms Paper.PhysicalComponentAcceptance.small_component
#print axioms Paper.PhysicalComponentAcceptance.covered_component
#print axioms Paper.PhysicalComponentAcceptance.port_covered_component
