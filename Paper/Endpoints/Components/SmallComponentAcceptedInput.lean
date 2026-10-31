import Paper.Endpoints.Components.SmallComponentProgram
set_option maxHeartbeats 200000
namespace Paper.SmallComponentAcceptedInput

theorem accepted_input_active_uniform
    {V : Type} [Fintype V] [LinearOrder V]
    (I : SimpleGraph V) [DecidableRel I.Adj]
    {B b : Nat} (ids : Paper.BroadcastModel.BitCode V b) (K : Nat)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    {v u : V} (p : I.Walk v u) :
    (Paper.SmallComponentProgram.acceptedInput I ids K s v).active =
      (Paper.SmallComponentProgram.acceptedInput I ids K s u).active := by
  simp only [Paper.SmallComponentProgram.acceptedInput_active]
  exact Paper.ComponentAcceptance.encoded_uniform I ids (Paper.SmallComponentProgram.radius K) p

theorem component_active_of_active
    {V : Type} [Fintype V] [LinearOrder V]
    (I : SimpleGraph V) [DecidableRel I.Adj]
    {B b : Nat} (ids : Paper.BroadcastModel.BitCode V b) (K : Nat)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (X : I.ConnectedComponent) (v : V) (hv : v ∈ X.supp)
    (hactive : (Paper.SmallComponentProgram.acceptedInput I ids K s v).active = true) :
    ∀ u ∈ X.supp, (Paper.SmallComponentProgram.acceptedInput I ids K s u).active = true := by
  intro u hu
  obtain ⟨p⟩ := X.reachable_of_mem_supp hv hu
  rw [← accepted_input_active_uniform I ids K s p]
  exact hactive

end Paper.SmallComponentAcceptedInput

#print axioms Paper.SmallComponentAcceptedInput.accepted_input_active_uniform
#print axioms Paper.SmallComponentAcceptedInput.component_active_of_active
