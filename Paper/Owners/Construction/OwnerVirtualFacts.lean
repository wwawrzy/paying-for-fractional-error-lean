import Paper.Owners.Construction.OwnerVirtualPrepare
import Paper.Owners.Construction.PublicOwners

/-! Identify the actual preparer's private metadata and routed high bits.
All global sets/marker functions here are proof-side evaluation objects. -/
namespace Paper.OwnerVirtualFacts
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable def high (D R : Finset V) (L Δ : ℕ) : Finset D :=
  HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ

noncomputable def marker (D R : Finset V) (L Δ : ℕ) (v : V) : Bool :=
  decide (Δ < (OwnerDiscoveryCorrect.capped G D R L Δ v).card)

theorem base_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L : ℕ) :
    OwnerVirtualPrepare.base G C L (fun v => (decide (v ∈ D), decide (v ∈ R))) =
      OwnerMetadataCorrect.expected G D R L := OwnerMetadataCorrect.correct G C D R L

theorem info_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) :
    OwnerVirtualPrepare.info G C L Δ (fun v => (decide (v ∈ D), decide (v ∈ R))) =
      fun v => (OwnerDiscoveryCorrect.capped G D R L Δ v, marker G D R L Δ v) := by
  unfold OwnerVirtualPrepare.info
  rw [base_correct]
  exact OwnerDiscoveryCorrect.discover_expected G C D R L Δ

theorem routeInput_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) :
    OwnerVirtualPrepare.routeInput G C L Δ (fun v => (decide (v ∈ D), decide (v ∈ R))) =
      OwnerPayloadInputs.expected G D R L D (marker G D R L Δ) := by
  funext v
  unfold OwnerVirtualPrepare.routeInput
  rw [base_correct, info_correct]
  rfl

theorem marker_high {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : D) : marker G D R L Δ i.val = decide (i ∈ high G D R L Δ) := by
  have hh := OwnerDiscoveryCorrect.high_correct G C D R hcover L Δ i
  rw [OwnerDiscoveryCorrect.correct] at hh
  exact hh

theorem low_degree (D R : Finset V) (L Δ : ℕ) (i : OwnerTasks.Low D (high G D R L Δ)) :
    (OwnerInteraction.graph G D R L).degree i.val ≤ Δ := by
  apply Nat.le_of_not_lt
  intro hh
  exact i.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)

theorem cap_low {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : D) (hlow : (OwnerInteraction.graph G D R L).degree i ≤ Δ) :
    OwnerDiscoveryCorrect.capped G D R L Δ i.val =
      ((OwnerInteraction.graph G D R L).neighborFinset i).image Subtype.val := by
  have hh := OwnerDiscoveryCorrect.low_exact G C D R hcover L Δ i hlow
  rw [OwnerDiscoveryCorrect.correct] at hh
  exact hh

theorem neighbors_image (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (i : D) :
    OwnerNeighborReports.neighbors G D R L i.val =
      ((OwnerInteraction.graph G D R L).neighborFinset i).image Subtype.val := by
  have hh := OwnerNeighborReports.neighbors_eq_image G D R
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hh
  exact hh hcover L i

theorem dictionary_lookup {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i j : D) (hlow : (OwnerInteraction.graph G D R L).degree i ≤ Δ)
    (hij : (OwnerInteraction.graph G D R L).Adj i j) :
    TaggedDictionary.lookup (OwnerVirtualPrepare.dictionary G C L Δ
      (fun v => (decide (v ∈ D), decide (v ∈ R))) i.val) j.val = some (marker G D R L Δ j.val) := by
  unfold OwnerVirtualPrepare.dictionary
  rw [routeInput_correct]
  apply OwnerPayloadRouteCorrect.lookup_correct G C BitCode.bool D R hcover L Δ D
    (marker G D R L Δ) i hlow j.val
  · rw [neighbors_image G D R hcover L i]
    exact Finset.mem_image.mpr ⟨j, (SimpleGraph.mem_neighborFinset _ i j).mpr hij, rfl⟩
  · exact j.property

theorem marker_low {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : OwnerTasks.Low D (high G D R L Δ)) : marker G D R L Δ i.val.val = false := by
  rw [marker_high G C D R hcover L Δ i.val]
  exact decide_eq_false i.property

theorem low_image (D : Finset V) (Q : Finset D) (v : V) (hv : v ∈ D) :
    v ∈ PublicOwners.image D Q ↔ (⟨v, hv⟩ : D) ∉ Q := by
  rw [PublicOwners.mem_image]
  constructor
  · rintro ⟨d, he, hlow⟩
    have hd : d = (⟨v, hv⟩ : D) := Subtype.ext he
    rwa [hd] at hlow
  · intro hlow
    exact ⟨⟨v, hv⟩, rfl, hlow⟩
end Paper.OwnerVirtualFacts
