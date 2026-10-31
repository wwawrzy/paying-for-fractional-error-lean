import Paper.Endpoints.Girth.HighGirthStaticThree
import Paper.Communication.PortBroadcastModel

/-! One physical Boolean broadcast in KT0. The instruction receives only
own identifier, degree, own state and messages indexed by local ports. -/
namespace Paper.HighGirthPortObservation
open BroadcastModel

def program {V S : Type} (flag : S → Bool) (update : V → Nat → S → Nat → S) :
    PortBroadcastModel.Program V S S := .broadcast 1 BitCode.bool {
  send := fun _ _ st => flag st
  update := fun v degree st incoming => update v degree st
    ((if flag st then 1 else 0) + (Finset.univ.filter (fun i => incoming i = true)).card) }

theorem rounds {V S : Type} (flag : S → Bool) (update : V → Nat → S → Nat → S) :
    (program flag update).rounds = 1 := rfl

theorem maxBits {V S : Type} (flag : S → Bool) (update : V → Nat → S → Nat → S) :
    (program flag update).maxBits = 1 := rfl

theorem port_neighbor_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ports : PortBroadcastModel.Numbering G)
    (A : Finset V) (v : V) :
    (Finset.univ.filter (fun i : Fin (G.degree v) => (ports v i).val ∈ A)).card =
      (G.neighborFinset v ∩ A).card := by
  classical
  apply Finset.card_bij (fun i _ => (ports v i).val)
  · intro i hi
    exact Finset.mem_inter.mpr ⟨(ports v i).property,(Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj he
    apply (ports v).injective
    exact Subtype.ext he
  · intro u hu
    obtain ⟨huN,huA⟩ := Finset.mem_inter.mp hu
    refine ⟨(ports v).symm ⟨u,huN⟩,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using huA⟩
    · simp

end Paper.HighGirthPortObservation
#print axioms Paper.HighGirthPortObservation.program
#print axioms Paper.HighGirthPortObservation.rounds
#print axioms Paper.HighGirthPortObservation.maxBits
#print axioms Paper.HighGirthPortObservation.port_neighbor_count
