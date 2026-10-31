import Paper.Preliminaries.VirtualSimulationCorrect
import Paper.Averaging.Tasks.KT0Compiler

/-! The paper's owner-communication interface: actual discovery of the
high flags and low-owner neighbor lists, followed by encoded simulation.
The implementation packs parameter-bounded lists into O(log n)-bit records;
it realizes the stated complexity, not the paper's slot-by-slot schedule. -/
namespace Paper.CurrentOwnerSimulation
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance publicAdj (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- No neighbor list or high-degree flag is an input. The only inputs are
the local owner and residual membership bits. -/
theorem discovery {bits : ℕ} (C : BitCode V bits) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L Δ : ℕ) :
    let env := (OwnerVirtualPrepare.program C L Δ).runEncoded G
      (fun v => (decide (v ∈ D), decide (v ∈ R)))
    (∀ i : D, (env i.val).high = decide (i ∈ OwnerVirtualFacts.high G D R L Δ)) ∧
      (∀ v, (env v).low = decide (v ∈ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))) ∧
      (∀ v, (env v).neighbors =
        (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ)).neighborFinset v) ∧
      (OwnerVirtualPrepare.program C L Δ).rounds = 10 ∧
      ∀ n c : ℕ, bits ≤ c * Nat.clog 2 (n + 2) →
        (OwnerVirtualPrepare.program C L Δ).maxBits ≤
          ((L + Δ + 4) * (c + 2)) * Nat.clog 2 (n + 2) := by
  dsimp only
  rw [Program.runEncoded_eq_run]
  exact ⟨OwnerVirtualCorrect.high_correct G C D R hcover L Δ,
    OwnerVirtualCorrect.low_correct G C D R hcover L Δ,
    OwnerVirtualCorrect.neighbors_correct G C D R hcover L Δ,
    OwnerVirtualPrepare.rounds C L Δ,
    fun n c hids => OwnerVirtualPrepare.logarithmic_bits C L Δ n c hids⟩

/-- After discovery, every encoded virtual broadcast program is simulated
on the actual physical graph. In particular, one virtual round takes four
physical rounds, with parameter-bounded message overhead. -/
theorem simulation {bits : ℕ} (C : BitCode V bits) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L Δ : ℕ) {In Out : Type}
    (P : Program V In Out) (s : V → In) :
    (VirtualSimulation.execute C L Δ P).runEncoded G
        (fun v => ((decide (v ∈ D), decide (v ∈ R)), s v)) =
      (fun v => (P.runEncoded
        (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ)) s v,
        (OwnerVirtualPrepare.program C L Δ).runEncoded G
          (fun u => (decide (u ∈ D), decide (u ∈ R))) v)) ∧
      (VirtualSimulation.execute C L Δ P).rounds = 10 + 4 * P.rounds ∧
      ∀ n c d : ℕ, bits ≤ c * Nat.clog 2 (n + 2) →
        P.maxBits ≤ d * Nat.clog 2 (n + 2) →
        (VirtualSimulation.execute C L Δ P).maxBits ≤
          ((L + Δ + 4) * (c + d + 2)) * Nat.clog 2 (n + 2) := by
  refine ⟨?_, VirtualSimulation.execute_rounds C L Δ P,
    fun n c d hids hmsg => VirtualSimulation.execute_logarithmic_bits C L Δ P n c d hids hmsg⟩
  simp only [Program.runEncoded_eq_run]
  exact VirtualSimulationCorrect.execute_correct G C D R hcover L Δ P s

/-- Starting from numbered ports and own IDs adds exactly one discovery
round. Neither the physical graph nor its neighbor-ID table is a program input. -/
theorem simulation_KT0 {bits : ℕ} (C : BitCode V bits) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L Δ : ℕ) {In Out : Type}
    (P : Program V In Out) (s : V → In) (ports : PortBroadcastModel.Numbering G) :
    (KT0Compiler.program C (VirtualSimulation.execute C L Δ P)).runEncoded G ports
        (fun v => ((decide (v ∈ D), decide (v ∈ R)), s v)) =
      (fun v => (P.runEncoded
        (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ)) s v,
        (OwnerVirtualPrepare.program C L Δ).runEncoded G
          (fun u => (decide (u ∈ D), decide (u ∈ R))) v)) ∧
      (KT0Compiler.program C (VirtualSimulation.execute C L Δ P)).rounds = 11 + 4 * P.rounds ∧
      ∀ n c d : ℕ, bits ≤ c * Nat.clog 2 (n + 2) →
        P.maxBits ≤ d * Nat.clog 2 (n + 2) →
        (KT0Compiler.program C (VirtualSimulation.execute C L Δ P)).maxBits ≤
          max c ((L + Δ + 4) * (c + d + 2)) * Nat.clog 2 (n + 2) := by
  have hs := simulation G C D R hcover L Δ P s
  refine ⟨?_, ?_, ?_⟩
  · rw [KT0Compiler.program_encoded_correct]
    exact hs.1
  · rw [KT0Compiler.program_rounds, hs.2.1]
    omega
  · intro n c d hids hmsg
    exact KT0Compiler.logarithmic_bits C (VirtualSimulation.execute C L Δ P) n c _
      hids (hs.2.2 n c d hids hmsg)

end Paper.CurrentOwnerSimulation

#print axioms Paper.CurrentOwnerSimulation.discovery
#print axioms Paper.CurrentOwnerSimulation.simulation_KT0
