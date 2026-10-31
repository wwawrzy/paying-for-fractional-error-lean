import Paper.Endpoints.Rounding.OrdinaryAbsorption
import Paper.Endpoints.Rounding.AbsorptionPortResources
namespace Paper.OrdinaryAbsorption
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]
def prepare : Program V Unit (GeneralCoveringFractional.Input V 1) :=
  .local fun v neighbors _ => ⟨true,1,true,insert v neighbors,insert v neighbors⟩
noncomputable def portProgram {bits : ℕ} (ids : BitCode V bits) (a K : ℕ)
    (A : Program V Unit Bool) : PortBroadcastModel.Program V Unit Bool :=
  KT0Compiler.program ids (.seq prepare (program ids a K A))
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem prepare_run : prepare.run G (fun _ => ()) = input G := by
  funext v
  have hc : insert v (G.neighborFinset v) = closed G v := by
    ext u
    simp [mem_closed]
  simp only [prepare,Program.run,input,hc]
theorem port_correct {bits : ℕ} (ids : BitCode V bits) (a K : ℕ)
    (A : Program V Unit Bool) (ports : PortBroadcastModel.Numbering G) :
    (portProgram ids a K A).runEncoded G ports (fun _ => ()) =
      (program ids a K A).runEncoded G (input G) := by
  rw [portProgram,KT0Compiler.program_encoded_correct]
  simp only [Program.runEncoded_eq_run,Program.run,prepare_run]
theorem port_rounds {bits : ℕ} (ids : BitCode V bits) (a K : ℕ)
    (A : Program V Unit Bool) :
    (portProgram ids a K A).rounds = 1+(A.rounds+SmallComponentProgram.roundBound a K) := by
  simp [portProgram,KT0Compiler.program_rounds,Program.rounds,prepare,program,
    ComponentReplacementProgram.rounds,lift,SmallComponentProgram.rounds]
theorem port_bits {bits : ℕ} (ids : BitCode V bits) (a K : ℕ)
    (A : Program V Unit Bool) (n cid C : ℕ)
    (hids : bits ≤ cid*Nat.clog 2 (n+2))
    (hA : A.maxBits ≤ C*Nat.clog 2 (n+2)) :
    (portProgram ids a K A).maxBits ≤
      max cid (max C (SmallComponentProgram.messageConstant a 1 K cid))*Nat.clog 2 (n+2) := by
  apply KT0Compiler.logarithmic_bits ids _ n cid _ hids
  simp only [Program.maxBits,prepare,Nat.zero_max,program,
    ComponentReplacementProgram.maxBits,lift]
  have hs := SmallComponentProgram.logarithmic_bits ids a 1 K (by omega) n cid hids
  exact (max_le_max hA hs).trans_eq (by rw [max_mul_mul_right])
end Paper.OrdinaryAbsorption
#print axioms Paper.OrdinaryAbsorption.port_correct
#print axioms Paper.OrdinaryAbsorption.port_rounds
#print axioms Paper.OrdinaryAbsorption.port_bits
