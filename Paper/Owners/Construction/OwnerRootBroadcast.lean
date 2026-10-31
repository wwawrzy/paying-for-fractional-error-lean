import Paper.Preliminaries.LabelNeighborhood
import Paper.Communication.ProgramMemory
import Paper.Owners.Construction.OwnerSupport

/-! Actual minimum-ID owner assignment, including self-owned centers and
self fallback outside the covered set. A single bit broadcast suffices. -/
namespace Paper.OwnerRootBroadcast
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def choose (v : V) (own : Bool) (roots : Finset V) : V :=
  if own then v else if h : roots.Nonempty then roots.min' h else v

def program : Program V Bool V :=
  .seq (.local fun _ _ s => (s, s)) (.seq (ProgramMemory.carry FlagNeighborhood.program)
    (.local fun v _ s => choose v s.2 s.1))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (D : Finset V) :
    program.run G (fun v => decide (v ∈ D)) = OwnerSupport.owner G D := by
  change (fun v => choose v (((ProgramMemory.carry FlagNeighborhood.program).run G
    (fun u => (decide (u ∈ D), decide (u ∈ D)))) v).2
      (((ProgramMemory.carry FlagNeighborhood.program).run G (fun u => (decide (u ∈ D), decide (u ∈ D)))) v).1) = _
  rw [ProgramMemory.run G FlagNeighborhood.program]
  funext v
  dsimp only
  rw [FlagNeighborhood.correct G D v]
  unfold OwnerSupport.owner
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  simp only [choose, decide_eq_true_eq]

theorem rounds : (program (V := V)).rounds = 1 := rfl

theorem maxBits : (program (V := V)).maxBits = 1 := rfl
end Paper.OwnerRootBroadcast
