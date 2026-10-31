import Paper.Endpoints.Components.PhysicalAcceptance
import Paper.Endpoints.Components.ComponentContext
import Paper.Endpoints.Components.IntegralCoverOptimum

/-! Small actual component optima imply acceptance of the physical program. -/
namespace Paper.PhysicalComponentAcceptance
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]

theorem small_optimum (G : SimpleGraph V) [DecidableRel G.Adj]
    (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ SevenFoundation.closed G r)
    (B : ℕ) (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v)
    (ht : ∀ v, (s v).targets = targets v)
    {b : ℕ} (ids : BitCode V b)
    (X : (CoveringIncidence.graph C R).ConnectedComponent)
    (K : ℕ) (hK : 1 ≤ K)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hc : ∀ u ∈ CoveringSupport.admissible C R, 1 ≤ (s u).cost.val)
    (hopt : IntegralCoverOptimum.optimum C
      (R ∩ IncidenceComponent.vertices (CoveringIncidence.graph C R) X)
      (fun u => (s u).cost.val) ≤ K)
    (v : V) (hv : v ∈ X.supp) :
    (program B ids (5 * K - 1)).runEncoded G s v = true := by
  let H := IncidenceComponent.vertices (CoveringIncidence.graph C R) X
  obtain ⟨D, hD, hcost⟩ := (IntegralCoverOptimum.optimum_le_iff C (R ∩ H)
    (fun u => (s u).cost.val) (fun r hr => hrows r (Finset.mem_inter.mp hr).1) K).mp hopt
  have hcD : ∀ u ∈ D, 1 ≤ (s u).cost.val := by
    intro u hu
    apply hc u
    obtain ⟨r, hr, hur⟩ := Finset.mem_biUnion.mp (hD.1 hu)
    exact Finset.mem_biUnion.mpr ⟨r, (Finset.mem_inter.mp hr).1, hur⟩
  apply covered_component G C targets R hinc hlocal B s hd hC ht ids X D K hK
    hcD hcost ?_ v hv
  intro r hr hrX
  exact hD.2 r (Finset.mem_inter.mpr ⟨hr,
    (IncidenceComponent.mem_vertices _ X r).mpr hrX⟩)

end Paper.PhysicalComponentAcceptance

#print axioms Paper.PhysicalComponentAcceptance.small_optimum
