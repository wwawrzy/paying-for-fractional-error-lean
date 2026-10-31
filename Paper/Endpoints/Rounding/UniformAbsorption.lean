import Paper.Endpoints.Rounding.AbsorptionFamilies
set_option maxHeartbeats 200000
namespace Paper.UniformAbsorption

theorem uniform_absorption
    (rho : Rat) (hrho : 1 ≤ rho) (B : Nat) (hB : 1 ≤ B)
    (q : Nat) (r : Real) (hr : 1 ≤ r) (cid : Nat)
    (cls : Paper.AbsorptionFamilies.InstanceClass B)
    (hfamily : ∀ delta : Rat, 0 < delta →
      ∃ (T C : Nat) (A : Paper.AbsorptionFamilies.BroadcastFamily B),
        Paper.AbsorptionFamilies.BroadcastBounds A T C cid ∧
        ∀ (V : Type) [Fintype V] [LinearOrder V] (bits : Nat)
          (ids : Paper.BroadcastModel.BitCode V bits)
          (i : Paper.AbsorptionFamilies.Instance V B),
          bits ≤ cid * Nat.clog 2 (Fintype.card V + 2) →
          cls V i → Paper.AbsorptionFamilies.Valid rho i →
          Paper.AbsorptionFamilies.Accuracy (A V ids) i (r * (1 + (delta : Real))) q)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ (T C : Nat) (P : Paper.AbsorptionFamilies.PortFamily B),
      Paper.AbsorptionFamilies.PortBounds P T C cid ∧
      ∀ (V : Type) [Fintype V] [LinearOrder V] (bits : Nat)
        (ids : Paper.BroadcastModel.BitCode V bits)
        (i : Paper.AbsorptionFamilies.Instance V B),
        bits ≤ cid * Nat.clog 2 (Fintype.card V + 2) →
        cls V i → Paper.AbsorptionFamilies.Valid rho i →
        Paper.AbsorptionFamilies.Correct (P V ids) i (r + epsilon) := by
  obtain ⟨delta, hdelta, hsmall, hK, hthreshold⟩ :=
    Paper.AbsorptionPublicParameters.public_absorption_parameters r epsilon q hr hepsilon
  obtain ⟨T, C, A, hbounds, haccuracy⟩ := hfamily delta hdelta
  let K := max 1 (Nat.ceil (2 * (q : Real) / epsilon))
  let a := Nat.ceil (rho : Real)
  let P := Paper.AbsorptionFamilies.absorb hB rho K A
  refine ⟨1 + (T + Paper.SmallComponentProgram.roundBound a K),
    max cid (max C (Paper.SmallComponentProgram.messageConstant a B K cid)), P, ?_, ?_⟩
  · intro V _ _ bits ids hids
    have hb := hbounds V bits ids hids
    constructor
    · simp only [P, Paper.AbsorptionFamilies.absorb, Paper.KT0Compiler.program_rounds,
        Paper.ComponentReplacementProgram.rounds, Paper.SmallComponentProgram.rounds]
      exact Nat.add_le_add_left (Nat.add_le_add_right hb.1 _) 1
    · apply Paper.KT0Compiler.logarithmic_bits ids _ (Fintype.card V) cid
        (max C (Paper.SmallComponentProgram.messageConstant a B K cid)) hids
      rw [Paper.ComponentReplacementProgram.maxBits]
      have hs := Paper.SmallComponentProgram.logarithmic_bits ids a B K hB (Fintype.card V) cid hids
      exact (max_le_max hb.2 hs).trans_eq (by rw [max_mul_mul_right])
  · intro V _ _ bits ids i hids hcls hvalid
    classical
    have hacc := haccuracy V bits ids i hids hcls hvalid
    obtain ⟨hinc, hlocal, hden, hd, hC, ht, hc, hrows⟩ := hvalid
    intro ports
    have hout := Paper.AbsorptionPhysicalEndpoint.absorption_physical_endpoint i.graph ports
      i.cover i.targets i.demands hinc hlocal rho hrho hden B K hB ids i.input
      hd hC ht (fun x _ => hc x) hK hrows (A V ids) hacc.1
      r epsilon q delta hr hepsilon hdelta hsmall hthreshold hacc.2 cid C hids
      (hbounds V bits ids hids).2
    exact ⟨hout.1, hout.2.1⟩

end Paper.UniformAbsorption

#print axioms Paper.UniformAbsorption.uniform_absorption
