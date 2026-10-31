import Paper.Owners.Construction.OwnerVirtualFacts

/-! The ten-round physical preparer really learns every public low-owner
neighbor set. No graph/neighbor oracle is an input to the actual code. -/
namespace Paper.OwnerVirtualCorrect
open BroadcastModel SevenFoundation OwnerVirtualFacts
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (PublicOwners.graph G D R L (high G D R L Δ)).Adj := fun _ _ => Classical.propDecidable _

def learned {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) :=
  (OwnerVirtualPrepare.program C L Δ).run G (fun v => (decide (v ∈ D), decide (v ∈ R)))

theorem learned_eq {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) (v : V) :
    learned G C D R L Δ v = OwnerVirtualPrepare.assemble (OwnerMetadataCorrect.expected G D R L v)
      (OwnerDiscoveryCorrect.capped G D R L Δ v, marker G D R L Δ v)
      (OwnerVirtualPrepare.dictionary G C L Δ (fun u => (decide (u ∈ D), decide (u ∈ R))) v) := by
  unfold learned
  rw [OwnerVirtualPrepare.run_program, base_correct, info_correct]

theorem metadata_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) (v : V) :
    (learned G C D R L Δ v).metadata = OwnerMetadataCorrect.expected G D R L v := by
  rw [learned_eq]
  rfl

theorem high_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : D) : (learned G C D R L Δ i.val).high = decide (i ∈ high G D R L Δ) := by
  rw [learned_eq]
  exact marker_high G C D R hcover L Δ i

theorem low_at {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : OwnerTasks.Low D (high G D R L Δ)) : (learned G C D R L Δ i.val.val).low = true := by
  rw [learned_eq]
  change (decide (i.val.val ∈ D) && !marker G D R L Δ i.val.val) = true
  rw [decide_eq_true i.val.property, marker_low G C D R hcover L Δ i]
  rfl

theorem low_outside {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (v : V) (hv : v ∉ PublicOwners.image D (high G D R L Δ)) :
    (learned G C D R L Δ v).low = false := by
  rw [learned_eq]
  change (decide (v ∈ D) && !marker G D R L Δ v) = false
  by_cases hvD : v ∈ D
  · let d : D := ⟨v, hvD⟩
    have hd : d ∈ high G D R L Δ := by
      by_contra hn
      exact hv ((low_image D (high G D R L Δ) v hvD).mpr hn)
    have hm : marker G D R L Δ v = true := (marker_high G C D R hcover L Δ d).trans (decide_eq_true hd)
    rw [hm]
    simp
  · simp [hvD]

theorem low_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (v : V) :
    (learned G C D R L Δ v).low = decide (v ∈ PublicOwners.image D (high G D R L Δ)) := by
  by_cases hv : v ∈ PublicOwners.image D (high G D R L Δ)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have he : i.val.val = v := hi
    rw [decide_eq_true hv]
    simpa only [he] using low_at G C D R hcover L Δ i
  · rw [decide_eq_false hv]
    exact low_outside G C D R hcover L Δ v hv

theorem neighbors_at {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : OwnerTasks.Low D (high G D R L Δ)) :
    (learned G C D R L Δ i.val.val).neighbors =
      (PublicOwners.graph G D R L (high G D R L Δ)).neighborFinset i.val.val := by
  rw [learned_eq]
  change (if decide (i.val.val ∈ D) && !marker G D R L Δ i.val.val then
    (OwnerDiscoveryCorrect.capped G D R L Δ i.val.val).filter (fun u => TaggedDictionary.lookup
      (OwnerVirtualPrepare.dictionary G C L Δ (fun v => (decide (v ∈ D), decide (v ∈ R))) i.val.val) u = some false)
    else ∅) = _
  simp only [decide_eq_true i.val.property, marker_low G C D R hcover L Δ i, Bool.not_false, Bool.true_and, ↓reduceIte]
  have hlow := low_degree G D R L Δ i
  rw [cap_low G C D R hcover L Δ i.val hlow, PublicOwners.neighbor_filter G D R L _ i]
  ext v
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨d, hd, he⟩, hlook⟩
    have hadj := (SimpleGraph.mem_neighborFinset (OwnerInteraction.graph G D R L) i.val d).mp hd
    have hl := dictionary_lookup G C D R hcover L Δ i.val d hlow hadj
    have hlookD : TaggedDictionary.lookup (OwnerVirtualPrepare.dictionary G C L Δ
        (fun u => (decide (u ∈ D), decide (u ∈ R))) i.val.val) d.val = some false := by
      rw [he]
      exact hlook
    have hm : marker G D R L Δ d.val = false := Option.some.inj (hl.symm.trans hlookD)
    rw [marker_high G C D R hcover L Δ d] at hm
    exact ⟨d, ⟨hd, of_decide_eq_false hm⟩, he⟩
  · rintro ⟨d, ⟨hd, hnot⟩, he⟩
    refine ⟨⟨d, hd, he⟩, ?_⟩
    rw [← he, dictionary_lookup G C D R hcover L Δ i.val d hlow
      ((SimpleGraph.mem_neighborFinset (OwnerInteraction.graph G D R L) i.val d).mp hd),
      marker_high G C D R hcover L Δ d, decide_eq_false hnot]

theorem neighbors_outside {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (v : V) (hv : v ∉ PublicOwners.image D (high G D R L Δ)) :
    (learned G C D R L Δ v).neighbors =
      (PublicOwners.graph G D R L (high G D R L Δ)).neighborFinset v := by
  have hl := low_outside G C D R hcover L Δ v hv
  rw [learned_eq] at hl ⊢
  change (decide (v ∈ D) && !marker G D R L Δ v) = false at hl
  change (if decide (v ∈ D) && !marker G D R L Δ v then
    (OwnerDiscoveryCorrect.capped G D R L Δ v).filter (fun u => TaggedDictionary.lookup
      (OwnerVirtualPrepare.dictionary G C L Δ (fun w => (decide (w ∈ D), decide (w ∈ R))) v) u = some false)
    else ∅) = _
  rw [hl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (PublicOwners.neighbor_outside G D R L _ v hv).symm

theorem neighbors_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (v : V) :
    (learned G C D R L Δ v).neighbors =
      (PublicOwners.graph G D R L (high G D R L Δ)).neighborFinset v := by
  by_cases hv : v ∈ PublicOwners.image D (high G D R L Δ)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have he : i.val.val = v := hi
    subst v
    exact neighbors_at G C D R hcover L Δ i
  · exact neighbors_outside G C D R hcover L Δ v hv

theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D) (L Δ : ℕ) (v : V) :
    (learned G C D R L Δ v).metadata = OwnerMetadataCorrect.expected G D R L v ∧
      (learned G C D R L Δ v).low = decide (v ∈ PublicOwners.image D (high G D R L Δ)) ∧
      (learned G C D R L Δ v).neighbors = (PublicOwners.graph G D R L (high G D R L Δ)).neighborFinset v :=
  ⟨metadata_correct G C D R L Δ v, low_correct G C D R hcover L Δ v, neighbors_correct G C D R hcover L Δ v⟩
end Paper.OwnerVirtualCorrect
