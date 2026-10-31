import Paper.Solver.LocalSearch.GeneralCoveringInitializedPhysical
import Paper.Solver.LocalSearch.GeneralCoveringOwnerSeparator
import Paper.Partitions.Separators.MappedSeparatorProfile

/-! Uniform boundary analysis of the SAME computed and physically simulated
partition. The graph-independent witnesses select only public natural program
parameters; no runtime separator/partition/boundary oracle is introduced. -/
namespace Paper.GeneralCoveringPhysicalBoundaryBound
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry

noncomputable local instance mappedAdj {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V) :
    DecidableRel (PublicEmbedding.graph J e).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance ownerAdj {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance lowAdj {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _
private noncomputable local instance cutAdj {W : Type} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (S : Finset W) (P : Finset (Finset W)) :
    DecidableRel (PartCut.graph J S P).Adj := fun _ _ => Classical.propDecidable _

/-- The inherited half balance is stronger than the partition API's 2/3 balance. -/
theorem half_to_two_thirds {W : Type} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] {C : ℝ} (hp : SeparatorProfile.Bound J C) :
    SeparatorBalance.Bound J C (2 / 3) := by
  intro S
  obtain ⟨X, hX, hbal⟩ := hp S
  refine ⟨X, hX, ?_⟩
  intro U
  apply (hbal U).trans
  have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  linarith

section Embedding
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V)

/-- Exact boundary image for the actual data pullback, not merely an upper bound. -/
theorem boundary_image (S : Finset V) (k : ℕ) (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e)
    (P : SmallParts.Data (PublicEmbedding.graph J e) S k) :
    (BoundaryOwners.vertices J Finset.univ (PublicPartitionPullback.data J e S k hS P).parts).image e =
      BoundaryOwners.vertices (PublicEmbedding.graph J e) S P.parts := by
  ext v
  constructor
  · rintro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (PublicPartitionPullback.boundary J e S k hS P w).mp hw
  · intro hv
    obtain ⟨w, rfl⟩ := (hS v).mp (BoundaryOwners.subset (PublicEmbedding.graph J e) S P.parts hv)
    exact Finset.mem_image.mpr ⟨w, (PublicPartitionPullback.boundary J e S k hS P w).mpr hv, rfl⟩

theorem boundary_card (S : Finset V) (k : ℕ) (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e)
    (P : SmallParts.Data (PublicEmbedding.graph J e) S k) :
    (BoundaryOwners.vertices J Finset.univ (PublicPartitionPullback.data J e S k hS P).parts).card =
      (BoundaryOwners.vertices (PublicEmbedding.graph J e) S P.parts).card := by
  rw [← boundary_image J e S k hS P, Finset.card_image_of_injective _ e.injective]
end Embedding

section Physical
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Alias for the exact frozen PhysicalMarks.partition boundary. -/
noncomputable def boundary {bits : ℕ} (ids : BitCode V bits) (C : V → Finset V)
    (D R : Finset V) (L Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) :=
  BoundaryOwners.vertices (graph G C D R L (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ))
    Finset.univ (GeneralCoveringTaskPhysicalMarks.partition G ids C D R L Δ k t T hk ht).parts

theorem low_card (D : Finset V) (Q : Finset D) : Fintype.card (Low D Q) ≤ D.card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (fun i : Low D Q => i.val) (fun _ _ he => Subtype.ext he)

/-- Physical density and original-R locality produce the public profile;
the extra one accounts for isolated public IDs outside the actual Low image. -/
theorem public_profile (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (Q : Finset D)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (s : ℕ) (hs : 2 * a + 1 < (s : ℝ)) :
    SeparatorBalance.Bound (PublicEmbedding.graph (graph G C D R L Q)
      (GeneralCoveringTaskPartitionMarks.lowEmbedding D Q)) (GeneralCoveringOwnerSeparator.constant a s L + 1) (2 / 3) := by
  apply half_to_two_thirds
  apply MappedSeparatorProfile.bound _ _ (GeneralCoveringOwnerSeparator.constant_nonneg a s L)
  exact GeneralCoveringOwnerSeparator.low_profile G C D R L hL Q hlocal hden ha s hs

theorem empty_low {bits : ℕ} (ids : BitCode V bits) (C : V → Finset V) (D R : Finset V) (L Δ k t T : ℕ)
    [IsEmpty (Low D (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ))]
    (hk : 0 < k) (ht : 0 < t) : boundary G ids C D R L Δ k t T hk ht = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (fun i => isEmptyElim i)

theorem empty_centers {bits : ℕ} (ids : BitCode V bits) (C : V → Finset V) (D R : Finset V)
    (L Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) (hD : D = ∅) : boundary G ids C D R L Δ k t T hk ht = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i _
  exact Finset.notMem_empty _ ((congrArg (fun S : Finset V => (i.val : V) ∈ S) hD).mp i.val.property)

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (C : V → Finset V)
    (D R : Finset V) (L Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t) : boundary G ids C D R L Δ k t T hk ht = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (fun i => isEmptyElim i.val.val)
end Physical

/-- Public t,k,T are chosen BEFORE physical V,G, ID representation and private
incidence data. No identifier bound by the private Low cardinal is used. -/
theorem uniform_parameters (a : ℝ) (ha : 0 ≤ a) (L : ℕ) (hL : 1 ≤ L) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k T : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ (C : V → Finset V) (D R : Finset V),
        (∀ r ∈ R, C r ⊆ closed G r) → ∀ {bits : ℕ} (ids : BitCode V bits),
        let Q := GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
        ((boundary G ids C D R L Δ k t T hk ht).card : ℝ) ≤ 2 * η * Fintype.card (Low D Q) ∧
        ((boundary G ids C D R L Δ k t T hk ht).card : ℝ) ≤ 2 * η * D.card := by
  obtain ⟨s, hs⟩ := exists_nat_gt (2 * a + 1)
  have hC : 0 ≤ GeneralCoveringOwnerSeparator.constant a s L + 1 := by
    have hc := GeneralCoveringOwnerSeparator.constant_nonneg a s L
    linarith
  obtain ⟨t, k, T, ht, hk, hcut⟩ := DeterministicPartitionComputedProgram.uniform_cut
    (GeneralCoveringOwnerSeparator.constant a s L + 1) hC Δ η hη
  refine ⟨t, k, T, ht, hk, ?_⟩
  intro V _ _ G _ hden C D R hlocal bits ids
  let Q := GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
  let J := graph G C D R L Q
  let e := GeneralCoveringTaskPartitionMarks.lowEmbedding D Q
  have hdeg := GeneralCoveringTaskPhysicalMarks.low_degree G C D R L Δ
  have hp := public_profile G C D R L hL Q hlocal hden ha s hs
  let S := GeneralCoveringTaskPartitionMarks.activeImage e
  let P := GeneralCoveringTaskPartitionMarks.publicPartition J e ids Δ k t T hk ht hdeg
  have hc : ((PartCut.graph (PublicEmbedding.graph J e) S P.parts).edgeFinset.card : ℝ) ≤ η * S.card :=
    hcut (PublicEmbedding.graph J e) hp (PublicEmbedding.degree_bound J e Δ hdeg) ids S
  have hn : ((BoundaryOwners.vertices (PublicEmbedding.graph J e) S P.parts).card : ℝ) ≤
      2 * ((PartCut.graph (PublicEmbedding.graph J e) S P.parts).edgeFinset.card : ℝ) := by
    exact_mod_cast BoundaryOwners.count (PublicEmbedding.graph J e) S P.parts
  have hb : ((BoundaryOwners.vertices (PublicEmbedding.graph J e) S P.parts).card : ℝ) ≤ 2 * η * S.card := by
    calc
      _ ≤ 2 * ((PartCut.graph (PublicEmbedding.graph J e) S P.parts).edgeFinset.card : ℝ) := hn
      _ ≤ 2 * (η * S.card) := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ = _ := by ring
  have hcard : (boundary G ids C D R L Δ k t T hk ht).card =
      (BoundaryOwners.vertices (PublicEmbedding.graph J e) S P.parts).card :=
    boundary_card J e S k (GeneralCoveringTaskPartitionMarks.activeImage_iff e) P
  have hS : S.card = Fintype.card (Low D Q) := by
    dsimp only [S, GeneralCoveringTaskPartitionMarks.activeImage]
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ]
  have hlow : ((boundary G ids C D R L Δ k t T hk ht).card : ℝ) ≤ 2 * η * Fintype.card (Low D Q) := by
    rw [hcard]
    simpa only [hS] using hb
  have hsize : (Fintype.card (Low D Q) : ℝ) ≤ D.card := by exact_mod_cast low_card (V := V) D Q
  exact ⟨hlow, hlow.trans (mul_le_mul_of_nonneg_left hsize (by positivity))⟩

/-- The same witnesses bound InitializedPhysical.boundary at centers produced
by its actual initializer. No center set is an input of the executable. -/
theorem initialized_parameters (a : ℝ) (ha : 0 ≤ a) (L : ℕ) (hL : 1 ≤ L) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k T : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ {bits : ℕ} (ids : BitCode V bits) (b h f U B : ℕ)
        (x : V → GeneralCoveringInitializedPhysical.Input V B) (d : GeneralCoveringInitializedPhysical.Original G k t B x),
        let D := GeneralCoveringInitializedPhysical.centers G ids b h f U B x
        let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover D d.R L Δ
        let Bdy := GeneralCoveringInitializedPhysical.boundary (b := b) (h := h) (f := f) (U := U)
          (L := L) (Δ := Δ) (T := T) G ids d
        ((Bdy.card : ℝ) ≤ 2 * η * Fintype.card (Low D Q)) ∧ ((Bdy.card : ℝ) ≤ 2 * η * D.card) := by
  obtain ⟨t, k, T, ht, hk, h⟩ := uniform_parameters a ha L hL Δ η hη
  refine ⟨t, k, T, ht, hk, ?_⟩
  intro V _ _ G _ hden bits ids b hinit f U B x d
  have hb := h G hden d.cover (GeneralCoveringInitializedPhysical.centers G ids b hinit f U B x) d.R d.local_rows ids
  simpa only [boundary, GeneralCoveringInitializedPhysical.boundary, GeneralCoveringTaskPhysicalRepair.boundary,
    GeneralCoveringInitializedPhysical.original] using hb

end Paper.GeneralCoveringPhysicalBoundaryBound

#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.half_to_two_thirds
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.boundary_image
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.boundary_card
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.low_card
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.public_profile
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.empty_low
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.empty_centers
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.empty_physical
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.uniform_parameters
#print axioms Paper.GeneralCoveringPhysicalBoundaryBound.initialized_parameters
