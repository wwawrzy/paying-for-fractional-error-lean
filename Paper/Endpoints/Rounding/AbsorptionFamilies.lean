import Paper.Endpoints.Rounding.AbsorptionPhysicalEndpoint
import Paper.Endpoints.Rounding.AbsorptionPublicParameters

/-! Uniform algorithm families and instance predicates for fv:imp:absorb.
Programs receive only their original local input. Graphs/optima occur only in
semantic specifications. Round/message constants are outside the quantifier over
all finite vertex types, codecs, physical graphs and private inputs. -/
namespace Paper.AbsorptionFamilies

structure Instance (V : Type) (B : Nat) where
  graph : SimpleGraph V
  cover : V → Finset V
  targets : V → Finset V
  demands : Finset V
  input : V → GeneralCoveringFractional.Input V B

abbrev BroadcastFamily (B : Nat) :=
  (V : Type) → [Fintype V] → [LinearOrder V] → {bits : Nat} →
    BroadcastModel.BitCode V bits →
    BroadcastModel.Program V (GeneralCoveringFractional.Input V B) Bool

abbrev PortFamily (B : Nat) :=
  (V : Type) → [Fintype V] → [LinearOrder V] → {bits : Nat} →
    BroadcastModel.BitCode V bits →
    PortBroadcastModel.Program V (GeneralCoveringFractional.Input V B) Bool

abbrev InstanceClass (B : Nat) :=
  (V : Type) → [Fintype V] → [LinearOrder V] → Instance V B → Prop

noncomputable def Valid {V : Type} [Fintype V] [LinearOrder V] {B : Nat}
    (rho : Rat) (i : Instance V B) : Prop := by
  classical
  exact (∀ v r, r ∈ i.targets v ↔ v ∈ i.cover r) ∧
    (∀ r ∈ i.demands, i.cover r ⊆ SevenFoundation.closed i.graph r) ∧
    Incidence.InducedDensityBound i.graph (rho : Real) ∧
    (∀ v, (i.input v).demand = decide (v ∈ i.demands)) ∧
    (∀ v, (i.input v).candidates = i.cover v) ∧
    (∀ v, (i.input v).targets = i.targets v) ∧
    (∀ v, 1 ≤ (i.input v).cost.val) ∧
    (∀ r ∈ i.demands, (i.cover r).Nonempty)

noncomputable def Accuracy {V : Type} [Fintype V] [LinearOrder V] {B : Nat}
    (A : BroadcastModel.Program V (GeneralCoveringFractional.Input V B) Bool)
    (i : Instance V B) (factor : Real) (q : Nat) : Prop := by
  classical
  let D := Finset.univ.filter (fun u => A.runEncoded i.graph i.input u = true)
  exact GeneralCoveringIntegral.Covers i.cover i.demands D ∧
    ((D.sum (fun u => (i.input u).cost.val) : Nat) : Real) ≤
      factor * CoveringOptimum.number i.cover i.demands
        (fun u => ((i.input u).cost.val : Real)) + (q : Real)

noncomputable def Correct {V : Type} [Fintype V] [LinearOrder V] {B : Nat}
    (A : PortBroadcastModel.Program V (GeneralCoveringFractional.Input V B) Bool)
    (i : Instance V B) (factor : Real) : Prop := by
  classical
  exact ∀ ports : PortBroadcastModel.Numbering i.graph,
    let D := Finset.univ.filter (fun u => A.runEncoded i.graph ports i.input u = true)
    GeneralCoveringIntegral.Covers i.cover i.demands D ∧
      ((D.sum (fun u => (i.input u).cost.val) : Nat) : Real) ≤
        factor * (IntegralCoverOptimum.optimum i.cover i.demands
          (fun u => (i.input u).cost.val) : Real)

def BroadcastBounds {B : Nat} (A : BroadcastFamily B) (T C cid : Nat) : Prop :=
  ∀ (V : Type) [Fintype V] [LinearOrder V] (bits : Nat) (ids : BroadcastModel.BitCode V bits),
    bits ≤ cid * Nat.clog 2 (Fintype.card V + 2) →
      (A V ids).rounds ≤ T ∧ (A V ids).maxBits ≤ C * Nat.clog 2 (Fintype.card V + 2)

def PortBounds {B : Nat} (A : PortFamily B) (T C cid : Nat) : Prop :=
  ∀ (V : Type) [Fintype V] [LinearOrder V] (bits : Nat) (ids : BroadcastModel.BitCode V bits),
    bits ≤ cid * Nat.clog 2 (Fintype.card V + 2) →
      (A V ids).rounds ≤ T ∧ (A V ids).maxBits ≤ C * Nat.clog 2 (Fintype.card V + 2)

/-- Uses only public parameters, original algorithm and original local input. -/
noncomputable def absorb {B : Nat} (hB : 1 ≤ B) (rho : Rat) (K : Nat)
    (A : BroadcastFamily B) : PortFamily B :=
  fun V _ _ _ ids => KT0Compiler.program ids
    (ComponentReplacementProgram.program (A V ids)
      (SmallComponentProgram.program ids (Nat.ceil (rho : Real)) B K hB))

end Paper.AbsorptionFamilies

#print axioms Paper.AbsorptionFamilies.Valid
#print axioms Paper.AbsorptionFamilies.Accuracy
#print axioms Paper.AbsorptionFamilies.Correct
#print axioms Paper.AbsorptionFamilies.BroadcastBounds
#print axioms Paper.AbsorptionFamilies.PortBounds
#print axioms Paper.AbsorptionFamilies.absorb
