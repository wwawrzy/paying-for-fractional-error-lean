import Paper.Owners.Construction.OwnerPayloadSize

/-! Full delivery theorem for the literal four-round physical router.
Every active true neighbor's payload reaches each low-degree owner root;
no sender-size or path-delivery oracle remains in the final statement. -/
namespace Paper.OwnerPayloadRouteCorrect
open BroadcastModel SevenFoundation
variable {V A : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance virtualAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

theorem consistent {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L Δ : ℕ) (active : Finset V) (f : V → A) (v : V) :
    TaggedDictionary.Consistent f ((OwnerPayloadRoute.program C P L Δ).run G
      (OwnerPayloadInputs.expected G D R L active f) v) := by
  rw [OwnerPayloadRoute.run_program]
  exact TaggedOwnedGather.consistent G C P (Δ + 1) _ f
    (OwnerPayloadLocalKeys.demand_consistent G C P D R hcover L active f) v

theorem delivers_key {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L Δ : ℕ) (active : Finset V) (f : V → A) (i : D)
    (hlow : (OwnerInteraction.graph G D R L).degree i ≤ Δ) (j : V)
    (hj : j ∈ OwnerNeighborReports.neighbors G D R L i.val) (hactive : j ∈ active) :
    j ∈ TaggedDictionary.keys ((OwnerPayloadRoute.program C P L Δ).run G
      (OwnerPayloadInputs.expected G D R L active f) i.val) := by
  have hroot := OwnerNeighborReports.rootUnion_eq G D R
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hroot
  rw [← hroot hcover L i.val] at hj
  rw [OwnerNeighborReports.rootUnion, hinst] at hj
  obtain ⟨r, hr, hjr⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨hstar, hrem, howner⟩ := (OwnerPayloadSize.owned_iff G D R L i.val r).mp hr
  obtain ⟨_, v, hv, hjv⟩ := (OwnerPayloadSize.report_mem G D R L r j).mp hjr
  have hcandidate : j ∈ TaggedDictionary.keys (OwnerPayloadRoute.candidate G C P
      (OwnerPayloadInputs.expected G D R L active f) v) := by
    rw [OwnerPayloadLocalKeys.candidate_keys G C P D R hcover L active f v]
    exact Finset.mem_inter.mpr ⟨hjv, hactive⟩
  have hdemand : j ∈ TaggedDictionary.keys (OwnerPayloadRoute.demand G C P L
      (OwnerPayloadInputs.expected G D R L active f) r) := by
    rw [OwnerPayloadLocalKeys.demand_keys G C P D R hcover L active f r]
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_inter.mpr ⟨hjv, hactive⟩⟩
  have hsize := OwnerPayloadSize.demand_bound G C P D R hcover L Δ active f i hlow r hrem howner
  rw [OwnerPayloadRoute.run_program]
  exact TaggedOwnedGather.delivers G C P (Δ + 1)
    (OwnerPayloadRoute.finalInput G C P L (OwnerPayloadInputs.expected G D R L active f)) i.val r hstar
    (decide_eq_true hrem) howner hsize j hdemand

theorem lookup_correct {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L Δ : ℕ) (active : Finset V) (f : V → A) (i : D)
    (hlow : (OwnerInteraction.graph G D R L).degree i ≤ Δ) (j : V)
    (hj : j ∈ OwnerNeighborReports.neighbors G D R L i.val) (hactive : j ∈ active) :
    TaggedDictionary.lookup ((OwnerPayloadRoute.program C P L Δ).run G
      (OwnerPayloadInputs.expected G D R L active f) i.val) j = some (f j) :=
  TaggedDictionary.lookup_correct f _ (consistent G C P D R hcover L Δ active f i.val) j
    (delivers_key G C P D R hcover L Δ active f i hlow j hj hactive)
end Paper.OwnerPayloadRouteCorrect
