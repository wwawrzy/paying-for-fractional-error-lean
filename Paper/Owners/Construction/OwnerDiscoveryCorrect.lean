import Paper.Owners.Construction.OwnerDiscoveryBroadcast

/-! Bounded physical reports discover the exact high flags and every low
owner's full virtual neighborhood, with strict Δ<degree as in the compiler. -/
namespace Paper.OwnerDiscoveryCorrect
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def reports (D R : Finset V) (L Δ : ℕ) (r : V) : OwnedReportNeighborhood.Report V :=
  ⟨OwnerSupport.owner G D r, decide (r ∈ OwnerInteraction.remaining G D R L),
    PrefixSet.take (Δ + 1) (OwnerNeighborReports.report G D R L r)⟩

noncomputable def family (D R : Finset V) (L : ℕ) (i : V) : Finset (Finset V) :=
  (OwnerNeighborReports.owned G D R L i).image (OwnerNeighborReports.report G D R L)

noncomputable def capped (D R : Finset V) (L Δ : ℕ) (i : V) : Finset V :=
  PrefixSet.take (Δ + 1) (PrefixSet.union (family G D R L i) (Δ + 1))

theorem family_union (D R : Finset V) (L : ℕ) (i : V) :
    (family G D R L i).biUnion id = OwnerNeighborReports.rootUnion G D R L i := by
  ext j
  simp only [family, OwnerNeighborReports.rootUnion, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨r, hr, rfl⟩, hj⟩
    exact ⟨r, hr, hj⟩
  · rintro ⟨r, hr, hj⟩
    exact ⟨OwnerNeighborReports.report G D R L r, ⟨r, hr, rfl⟩, hj⟩

theorem raw_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) (i : V) :
    (OwnedReportNeighborhood.program C (Δ + 1)).run G (reports G D R L Δ) i =
      PrefixSet.union (family G D R L i) (Δ + 1) := by
  rw [OwnedReportNeighborhood.correct G C (Δ + 1) (reports G D R L Δ)
    (fun u => PrefixSet.bound _ _) i]
  ext j
  simp only [PrefixSet.union, family, Finset.mem_biUnion, Finset.mem_image]
  have howned (r : V) : r ∈ OwnerNeighborReports.owned G D R L i ↔
      r ∈ closed G i ∧ r ∈ OwnerInteraction.remaining G D R L ∧ OwnerSupport.owner G D r = i := by
    unfold OwnerNeighborReports.owned
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst]
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  constructor
  · rintro ⟨r, hr, hj⟩
    dsimp only [OwnedReportNeighborhood.accept, reports] at hj
    split_ifs at hj with hf
    · have hflags := Bool.and_eq_true_iff.mp hf
      have hrOwned := (howned r).mpr ⟨hr, of_decide_eq_true hflags.1, of_decide_eq_true hflags.2⟩
      exact ⟨OwnerNeighborReports.report G D R L r, ⟨r, hrOwned, rfl⟩, hj⟩
    · simp at hj
  · rintro ⟨s, ⟨r, hr, rfl⟩, hj⟩
    obtain ⟨hstar, hrem, hri⟩ := (howned r).mp hr
    refine ⟨r, hstar, ?_⟩
    simpa only [OwnedReportNeighborhood.accept, reports, decide_eq_true hrem, decide_eq_true hri,
      Bool.true_and, ↓reduceIte] using hj

theorem discover_expected {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) :
    (OwnerDiscoveryBroadcast.discover C L Δ).run G (OwnerMetadataCorrect.expected G D R L) =
      fun i => (capped G D R L Δ i, decide (Δ < (capped G D R L Δ i).card)) := by
  rw [OwnerDiscoveryBroadcast.run_discover]
  dsimp only [OwnerMetadataCorrect.expected]
  have hs : (SetNeighborhood.program C L).run G (OwnerInteraction.actualSupport G D R L) =
      fun r => (closed G r).biUnion (OwnerInteraction.actualSupport G D R L) :=
    funext (SetNeighborhood.correct G C L _ (OwnerInteraction.support_bound G D R L))
  rw [hs]
  have hr : (fun u => (⟨OwnerSupport.owner G D u, decide (u ∈ OwnerInteraction.remaining G D R L),
      PrefixSet.take (Δ + 1) (((closed G u).biUnion (OwnerInteraction.actualSupport G D R L)).erase (OwnerSupport.owner G D u))⟩ :
        OwnedReportNeighborhood.Report V)) = reports G D R L Δ := by
    funext u
    unfold reports OwnerNeighborReports.report
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst]
  dsimp only
  rw [hr]
  funext i
  rw [raw_correct G C D R L Δ i]
  rfl

theorem correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (L Δ : ℕ) :
    (OwnerDiscoveryBroadcast.program C L Δ).run G (fun v => (decide (v ∈ D), decide (v ∈ R))) =
      fun i => (capped G D R L Δ i, decide (Δ < (capped G D R L Δ i).card)) := by
  change (OwnerDiscoveryBroadcast.discover C L Δ).run G
    ((OwnerMetadataBroadcast.program C L).run G (fun v => (decide (v ∈ D), decide (v ∈ R)))) = _
  rw [OwnerMetadataCorrect.correct G C D R L]
  exact discover_expected G C D R L Δ

noncomputable local instance virtualAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

theorem card_family (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (i : D) :
    ((family G D R L i.val).biUnion id).card = (OwnerInteraction.graph G D R L).degree i := by
  rw [family_union]
  have hh := OwnerNeighborReports.card_rootUnion G D R
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hh
  exact hh hcover L i

theorem family_neighbors (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (i : D) :
    (family G D R L i.val).biUnion id = ((OwnerInteraction.graph G D R L).neighborFinset i).image Subtype.val := by
  have h1 := OwnerNeighborReports.rootUnion_eq G D R
  have h2 := OwnerNeighborReports.neighbors_eq_image G D R
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at h1 h2
  rw [family_union, h1 hcover L i.val, h2 hcover L i]

theorem high_correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : D) :
    ((OwnerDiscoveryBroadcast.program C L Δ).run G (fun v => (decide (v ∈ D), decide (v ∈ R))) i.val).2 =
      decide (i ∈ HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ) := by
  rw [correct G C D R L Δ]
  have hh := PrefixSet.capped_union_small_iff (family G D R L i.val) (Δ + 1)
  rw [card_family G D R hcover L i] at hh
  apply Bool.decide_congr
  simp only [HighDegreeCut.high, Finset.mem_filter, Finset.mem_univ, true_and]
  change (Δ < (capped G D R L Δ i.val).card) ↔ Δ < (OwnerInteraction.graph G D R L).degree i
  change (capped G D R L Δ i.val).card < Δ + 1 ↔ _ at hh
  omega

theorem low_exact {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ : ℕ) (i : D) (hlow : (OwnerInteraction.graph G D R L).degree i ≤ Δ) :
    ((OwnerDiscoveryBroadcast.program C L Δ).run G (fun v => (decide (v ∈ D), decide (v ∈ R))) i.val).1 =
      ((OwnerInteraction.graph G D R L).neighborFinset i).image Subtype.val := by
  rw [correct G C D R L Δ]
  have hcard : ((family G D R L i.val).biUnion id).card < Δ + 1 := by
    rw [card_family G D R hcover L i]
    omega
  have hs := (PrefixSet.capped_union_small_iff (family G D R L i.val) (Δ + 1)).mpr hcard
  change capped G D R L Δ i.val = _
  rw [capped, PrefixSet.capped_union_low_eq _ _ hs, family_neighbors G D R hcover L i]
end Paper.OwnerDiscoveryCorrect
