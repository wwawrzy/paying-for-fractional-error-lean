import Paper.Endpoints.Components.IncidenceGraph
import Paper.Communication.SubgraphBroadcast

/-! Execute a covering algorithm on its actual incidence graph through the
physical network. One initial demand-bit broadcast prepares private logical
neighbor lists; the original input and all subsequent messages are preserved. -/
namespace Paper.IncidenceExecution
open BroadcastModel
variable {V : Type} [DecidableEq V]

def program (B : ℕ) {Out : Type}
    (P : Program V (GeneralCoveringFractional.Input V B) Out) :
    Program V (GeneralCoveringFractional.Input V B) Out :=
  .seq (CoveringIncidence.program B) (SubgraphBroadcast.program P)

theorem rounds (B : ℕ) {Out : Type}
    (P : Program V (GeneralCoveringFractional.Input V B) Out) :
    (program B P).rounds = 1 + P.rounds := by
  simp only [program, Program.rounds, CoveringIncidence.rounds, SubgraphBroadcast.rounds]

theorem maxBits (B : ℕ) {Out : Type}
    (P : Program V (GeneralCoveringFractional.Input V B) Out) :
    (program B P).maxBits = max 1 P.maxBits := by
  simp only [program, Program.maxBits, CoveringIncidence.maxBits, SubgraphBroadcast.maxBits]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Correctness for the literal encoded physical execution. The graph and
global incidence data are proof parameters, never constructor arguments. -/
theorem run_correct (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ SevenFoundation.closed G r)
    (B : ℕ) {Out : Type}
    (P : Program V (GeneralCoveringFractional.Input V B) Out)
    (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v)
    (ht : ∀ v, (s v).targets = targets v) :
    (program B P).runEncoded G s = P.runEncoded (CoveringIncidence.graph C R) s := by
  have hp : (CoveringIncidence.program B).runEncoded G s =
      fun v => ((CoveringIncidence.graph C R).neighborFinset v, s v) := by
    funext v
    exact Prod.ext (CoveringIncidence.prepared_neighbors G C targets R hinc hlocal s hd hC ht v)
      (CoveringIncidence.retains_input G B s v)
  change (SubgraphBroadcast.program P).runEncoded G
    ((CoveringIncidence.program B).runEncoded G s) = _
  rw [hp]
  exact SubgraphBroadcast.runEncoded_correct G (CoveringIncidence.graph C R)
    (CoveringIncidence.graph_le G C R hlocal) P _ (fun _ => rfl) s

end Paper.IncidenceExecution

#print axioms Paper.IncidenceExecution.rounds
#print axioms Paper.IncidenceExecution.maxBits
#print axioms Paper.IncidenceExecution.run_correct
