import Paper.Endpoints.Girth.HighGirthNearOptimalInput
namespace Paper.HighGirthSolverParameters
theorem planar_solver_input_parameters
    :
    ∃ A L Δ r k t Q T s q M : Nat, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar → ∀ {idBits : Nat} (C : Paper.BroadcastModel.BitCode V idBits),
        let raw := fun v => (((Paper.GeneralFractionalBroadcast.program C
          A L Δ r k t Q T s 3 q M hQ).runEncoded (Paper.HighGirthMaskedInput.graph G)
            (fun u => (decide (u ∈ Paper.HighGirthTransformation.demands G),
              Paper.HighGirthMaskedInput.weight G u)) v).val : Real) /
            Paper.PartialFractionalProgram.denominator Δ k Q T s q
        let x := Paper.HighGirthMaskedInput.capped G raw
        Paper.SevenFoundation.feasible (Paper.HighGirthAuxiliary.auxiliary G) x ∧
        (∀ v ∈ Paper.HighGirthTransformation.zone G, x v ≤ 1) ∧
        Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) x ≤
          (1 + (5 : Real)/8482) * Paper.HighGirthAuxiliary.number G := by
  classical
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,hp⟩ :=
    Paper.HighGirthNearOptimalInput.weighted_solver_guarantee
  refine ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,?_⟩
  intro V _ _ G _ hplanar idBits C
  have h := hp (Paper.HighGirthMaskedInput.graph G)
    (Paper.HighGirthNearOptimalInput.masked_planar_density G hplanar) C
    (Paper.HighGirthTransformation.demands G) (Paper.HighGirthMaskedInput.weight G)
    (Paper.HighGirthMaskedInput.weight_pos G)
  exact Paper.HighGirthNearOptimalInput.transfer G _ ((5 : Real)/8482) h.1 h.2
end Paper.HighGirthSolverParameters
#print axioms Paper.HighGirthSolverParameters.planar_solver_input_parameters
