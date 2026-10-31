import Paper.RedBlue.SolverInput
import Paper.Averaging.Tasks.KT0Compiler
namespace Paper.RedBlue
open BroadcastModel
variable {V : Type} [LinearOrder V]
structure LocalInput (M : ℕ) where
  red : Bool
  blue : Bool
  cost : Fin (M+1)
def localPreparation (M : ℕ) : Program V (LocalInput M) (GeneralCoveringFractionalEndpoint.Input V M) :=
  .broadcast 2 (BitCode.pairBool BitCode.bool) {
    send := fun _ _ s => (s.red,s.blue)
    update := fun _ N s incoming =>
      (⟨s.red,
        if s.red then (N.attach.filter (fun u => (incoming u).2 = true)).image Subtype.val else ∅,
        if s.blue then (N.attach.filter (fun u => (incoming u).1 = true)).image Subtype.val else ∅⟩,s.cost) }
theorem localPreparation_rounds (M : ℕ) : (localPreparation (V := V) M).rounds = 1 := rfl
theorem localPreparation_bits (M : ℕ) : (localPreparation (V := V) M).maxBits = 2 := rfl
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def localInput {M : ℕ} (R B : Finset V) (c : V → Fin (M+1)) (v : V) : LocalInput M := by
  classical
  exact ⟨decide (v ∈ R),decide (v ∈ B),c v⟩
theorem localPreparation_correct {M : ℕ} (R B : Finset V) (c : V → Fin (M+1)) :
    (localPreparation M).run G (localInput R B c) = solverInput G R B c := by
  classical
  have hfilter (S : Finset V) (v : V) :
      ((G.neighborFinset v).attach.filter (fun u => u.val ∈ S)).image Subtype.val =
        G.neighborFinset v ∩ S := by
    ext u
    simp [and_comm]
  funext v
  simp [localPreparation,Program.run,eval,localInput,solverInput,rows,targets,hfilter]
end Paper.RedBlue
#print axioms Paper.RedBlue.localPreparation_correct
