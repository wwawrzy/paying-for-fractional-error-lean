import Paper.Endpoints.Components.SmallComponentAcceptedInput

namespace Paper.SmallComponentAcceptedContext

theorem accepted_component_context
    {V : Type} [Fintype V] [LinearOrder V]
    (I : SimpleGraph V) [DecidableRel I.Adj]
    {B b : Nat} (ids : Paper.BroadcastModel.BitCode V b) (K : Nat)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (X : I.ConnectedComponent) (v : V) (hv : v ∈ X.supp)
    (hactive : (Paper.SmallComponentProgram.acceptedInput I ids K s v).active = true) :
    (∀ u ∈ X.supp, (Paper.SmallComponentProgram.acceptedInput I ids K s u).active = true) ∧
    (∀ u ∈ X.supp, ∀ w ∈ X.supp, ∃ p : I.Walk u w,
      p.length ≤ 2 * Paper.SmallComponentProgram.radius K) := by
  constructor
  · exact Paper.SmallComponentAcceptedInput.component_active_of_active I ids K s X v hv hactive
  · rw [Paper.SmallComponentProgram.acceptedInput_active] at hactive
    intro u hu w hw
    obtain ⟨p⟩ := X.reachable_of_mem_supp hv hu
    obtain ⟨q⟩ := X.reachable_of_mem_supp hv hw
    exact Paper.ComponentAcceptance.encoded_diameter I ids (Paper.SmallComponentProgram.radius K) hactive p q

end Paper.SmallComponentAcceptedContext

#print axioms Paper.SmallComponentAcceptedContext.accepted_component_context
