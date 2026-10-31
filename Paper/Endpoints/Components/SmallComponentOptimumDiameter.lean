import Paper.Endpoints.Components.OptimumAcceptance
set_option maxHeartbeats 200000
namespace Paper.SmallComponentOptimumDiameter

theorem small_optimum_diameter
    {V : Type} [Fintype V] [LinearOrder V]
    (cover : V → Finset V) (R : Finset V) (c : V → Nat)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (K : Nat) (hK : 1 ≤ K)
    (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (hc : ∀ u ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ c u)
    (hopt : Paper.IntegralCoverOptimum.optimum cover
      (R ∩ Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X) c ≤ K) :
    (∀ x y : X, X.toSimpleGraph.dist x y ≤ 5 * K - 1) ∧
    ((∀ r ∈ X.supp, r ∈ R) → ∀ x y : X, X.toSimpleGraph.dist x y ≤ 3 * K - 1) := by
  classical
  let I := Paper.CoveringIncidence.graph cover R
  let H := Paper.IncidenceComponent.vertices I X
  obtain ⟨D, hD, hcost⟩ := (Paper.IntegralCoverOptimum.optimum_le_iff cover (R ∩ H) c
    (fun r hr => hrows r (Finset.mem_inter.mp hr).1) K).mp hopt
  have hcD : ∀ u ∈ D, 1 ≤ (c u : Real) := by
    intro u hu
    have hadm := hD.1 hu
    obtain ⟨r, hr, hur⟩ := Finset.mem_biUnion.mp hadm
    have hglobal : u ∈ Paper.CoveringSupport.admissible cover R :=
      Finset.mem_biUnion.mpr ⟨r, (Finset.mem_inter.mp hr).1, hur⟩
    exact_mod_cast hc u hglobal
  have hcostR : D.sum (fun u => (c u : Real)) ≤ (K : Real) := by
    exact_mod_cast hcost
  have hcover : ∀ r ∈ R, r ∈ X.supp → ∃ d ∈ D, d ∈ cover r := by
    intro r hr hrX
    exact hD.2 r (Finset.mem_inter.mpr ⟨hr,
      (Paper.IncidenceComponent.mem_vertices I X r).mpr hrX⟩)
  refine ⟨?_, ?_⟩
  · exact Paper.CoveringIncidence.component_distance_le_five cover R X D
      (fun u => (c u : Real)) K hK hcD hcostR hcover
  · intro hall
    exact Paper.CoveringIncidence.component_distance_le_three cover R X D
      (fun u => (c u : Real)) K hK hcD hcostR hall hcover

end Paper.SmallComponentOptimumDiameter

#print axioms Paper.SmallComponentOptimumDiameter.small_optimum_diameter
