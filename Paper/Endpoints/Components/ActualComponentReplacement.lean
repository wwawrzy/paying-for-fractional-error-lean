import Paper.Endpoints.Components.ComponentReplacementProgram
import Paper.Endpoints.Components.SmallComponentPhysicalCorrectness
set_option maxHeartbeats 200000
namespace Paper.ActualComponentReplacement

theorem replacement_covers
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ Paper.SevenFoundation.closed G r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (A0 : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool)
    (hcover0 : Paper.GeneralCoveringIntegral.Covers cover R
      (Finset.univ.filter (fun u => A0.runEncoded G s u = true))) :
    Paper.GeneralCoveringIntegral.Covers cover R
      (Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A0
        (Paper.SmallComponentProgram.program ids a B K hB)).runEncoded G s u = true)) := by
  classical
  let I := Paper.CoveringIncidence.graph cover R
  let out := (Paper.SmallComponentProgram.program ids a B K hB).runEncoded G s
  intro r hr
  let X := I.connectedComponentMk r
  have hrX : r ∈ X.supp := by rfl
  have hspec := Paper.SmallComponentPhysicalCorrectness.physical_correct G cover targets R
    hinc hlocal a ha hden B K hB ids s hd hC ht X hc hK hrows
  by_cases hs : (out r).1 = true
  · obtain ⟨hfeas, _⟩ := hspec.2.1 r hrX hs
    have hrH : r ∈ R ∩ Paper.IncidenceComponent.vertices I X :=
      Finset.mem_inter.mpr ⟨hr, (Paper.IncidenceComponent.mem_vertices I X r).mpr hrX⟩
    obtain ⟨u, huD, hur⟩ := hfeas.2 r hrH
    obtain ⟨huH, hselected⟩ := Finset.mem_filter.mp huD
    have huX := (Paper.IncidenceComponent.mem_vertices I X u).mp huH
    have hsu : (out u).1 = true := (hspec.1 r hrX u huX).symm.trans hs
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩, hur⟩
    rw [Paper.ComponentReplacementProgram.run_encoded]
    change (if (out u).1 then (out u).2 else A0.runEncoded G s u) = true
    have hsel : (out u).2 = true := hselected
    simpa only [hsu, ↓reduceIte] using hsel
  · obtain ⟨u, hu0, hur⟩ := hcover0 r hr
    have huX : u ∈ X.supp := by
      rcases Paper.CoveringIncidence.candidate_self_or_adj cover R hr hur with he | hadj
      · simpa only [he] using hrX
      · exact X.mem_supp_of_adj_mem_supp hrX hadj
    have hsu : (out u).1 ≠ true := by
      intro hu
      exact hs ((hspec.1 r hrX u huX).trans hu)
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩, hur⟩
    rw [Paper.ComponentReplacementProgram.run_encoded]
    change (if (out u).1 then (out u).2 else A0.runEncoded G s u) = true
    simpa only [hsu, ↓reduceIte] using (Finset.mem_filter.mp hu0).2

end Paper.ActualComponentReplacement

#print axioms Paper.ActualComponentReplacement.replacement_covers
