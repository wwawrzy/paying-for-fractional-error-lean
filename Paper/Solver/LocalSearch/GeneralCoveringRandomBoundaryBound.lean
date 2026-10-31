import Paper.Solver.LocalSearch.GeneralCoveringTaskRandomPhysicalMarks
import Paper.Solver.LocalSearch.GeneralCoveringPhysicalBoundaryBound

/-! Exact expected boundary of the SAME native random partition. Every sum
uses the original public-V Boolean source beta; no private-Low law or change
of probability space is used. This module adds analysis only, no runtime. -/
namespace Paper.GeneralCoveringRandomBoundaryBound
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
abbrev Coins := GeneralCoveringTaskRandomPhysicalMarks.Coins
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance mappedAdj {W : Type} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V) :
    DecidableRel (PublicEmbedding.graph J e).Adj := fun _ _ => Classical.propDecidable _

noncomputable def boundary (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k)
    (t b n : ℕ) (β : V → Coins Δ k b n) :=
  BoundaryOwners.vertices (graph G C D R L (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) Finset.univ
    (GeneralCoveringTaskRandomPhysicalMarks.partition G C D R L hk t β).parts

def flagged {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) : Finset V :=
  Finset.univ.filter (fun v => ((GeneralCoveringTaskRandomPhysicalMarks.program I L Δ k t b n B).runEncoded G
    (fun u => (input u, (c u, β u))) v).boundary = true)

/-- The actual preparer is fixed before beta and is retained for every outcome. -/
theorem preparation_independent {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β γ : V → Coins Δ k b n) (v : V) :
    ((GeneralCoveringTaskRandomPhysicalMarks.program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, β u))) v).env =
      ((GeneralCoveringTaskRandomPhysicalMarks.program I L Δ k t b n B).runEncoded G (fun u => (input u, (c u, γ u))) v).env :=
  (GeneralCoveringTaskRandomPhysicalMarks.env_retained G I L Δ k t b n B input c β v).trans
    (GeneralCoveringTaskRandomPhysicalMarks.env_retained G I L Δ k t b n B input c γ v).symm

theorem flag_at_low {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n)
    (i : Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) :
    ((GeneralCoveringTaskRandomPhysicalMarks.program I L Δ k t b n B).runEncoded G
      (fun v => (input v, (c v, β v))) i.val.val).boundary = decide (i ∈ boundary G d.cover d.D d.R L Δ k hk t b n β) := by
  obtain ⟨U, hU, hi⟩ := (GeneralCoveringTaskRandomPhysicalMarks.partition G d.cover d.D d.R L hk t β).covers i (Finset.mem_univ i)
  exact congrArg (fun s : GeneralCoveringTaskRandomPhysicalMarks.Output V B Δ k b n => s.boundary)
    (GeneralCoveringTaskRandomPhysicalMarks.part_output G I L Δ k hk t ht b n B input d c β U hU i hi)

/-- Physical boundary flags are exactly the injective image of this outcome's
actual pulled-back Low boundary, including all nonlow/inactive vertices. -/
theorem flagged_image {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    flagged G I L Δ k t b n B input c β = (boundary G d.cover d.D d.R L Δ k hk t b n β).image
      (GeneralCoveringTaskPartitionMarks.lowEmbedding d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)) := by
  ext v
  constructor
  · intro hf
    have htrue := (Finset.mem_filter.mp hf).2
    by_cases hv : v ∈ GeneralCoveringOwnerVirtualPrepare.image d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      have hi := of_decide_eq_true ((flag_at_low G I L Δ k hk t ht b n B input d c β i).symm.trans htrue)
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · have he : ((GeneralCoveringTaskRandomPhysicalMarks.program I L Δ k t b n B).runEncoded G
          (fun u => (input u, (c u, β u))) v).boundary = false := by
        simpa only using congrArg (fun s : GeneralCoveringTaskRandomPhysicalMarks.Output V B Δ k b n => s.boundary)
          (GeneralCoveringTaskRandomPhysicalMarks.outside_low G I L Δ k hk t ht b n B input d c β v hv)
      have hbad : (false : Bool) = true := he.symm.trans htrue
      cases hbad
  · intro hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (flag_at_low G I L Δ k hk t ht b n B input d c β i).trans (decide_eq_true hi)⟩

theorem flagged_card {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    (flagged G I L Δ k t b n B input c β).card = (boundary G d.cover d.D d.R L Δ k hk t b n β).card := by
  rw [flagged_image G I L Δ k hk t ht b n B input d c β, Finset.card_image_of_injective _
    (GeneralCoveringTaskPartitionMarks.lowEmbedding d.D _).injective]

/-- Generic accepted pullback image theorem specialized to this SAME random P. -/
theorem public_boundary_image (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k)
    (t b n : ℕ) (β : V → Coins Δ k b n) :
    let Q := GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
    let J := graph G C D R L Q
    let e := GeneralCoveringTaskPartitionMarks.lowEmbedding D Q
    (boundary G C D R L Δ k hk t b n β).image e = BoundaryOwners.vertices (PublicEmbedding.graph J e)
      (GeneralCoveringTaskPartitionMarks.activeImage e)
      (GeneralCoveringTaskRandomPhysicalMarks.publicPartition J e Δ k hk t b n β).parts := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
  let J := graph G C D R L Q
  let e := GeneralCoveringTaskPartitionMarks.lowEmbedding D Q
  exact GeneralCoveringPhysicalBoundaryBound.boundary_image J e (GeneralCoveringTaskPartitionMarks.activeImage e) k
    (GeneralCoveringTaskPartitionMarks.activeImage_iff e)
    (GeneralCoveringTaskRandomPhysicalMarks.publicPartition J e Δ k hk t b n β)

theorem public_boundary_card (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k)
    (t b n : ℕ) (β : V → Coins Δ k b n) :
    let Q := GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
    let J := graph G C D R L Q
    let e := GeneralCoveringTaskPartitionMarks.lowEmbedding D Q
    (boundary G C D R L Δ k hk t b n β).card = (BoundaryOwners.vertices (PublicEmbedding.graph J e)
      (GeneralCoveringTaskPartitionMarks.activeImage e)
      (GeneralCoveringTaskRandomPhysicalMarks.publicPartition J e Δ k hk t b n β).parts).card := by
  let Q := GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
  let J := graph G C D R L Q
  let e := GeneralCoveringTaskPartitionMarks.lowEmbedding D Q
  exact GeneralCoveringPhysicalBoundaryBound.boundary_card J e (GeneralCoveringTaskPartitionMarks.activeImage e) k
    (GeneralCoveringTaskPartitionMarks.activeImage_iff e)
    (GeneralCoveringTaskRandomPhysicalMarks.publicPartition J e Δ k hk t b n β)

theorem boundary_empty_low (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k) (t b n : ℕ)
    [IsEmpty (Low D (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ))] (β : V → Coins Δ k b n) :
    boundary G C D R L Δ k hk t b n β = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (fun i => isEmptyElim i)

theorem boundary_empty_centers (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k) (t b n : ℕ)
    (hD : D = ∅) (β : V → Coins Δ k b n) : boundary G C D R L Δ k hk t b n β = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i _
  exact Finset.notMem_empty _ ((congrArg (fun S : Finset V => (i.val : V) ∈ S) hD).mp i.val.property)

theorem boundary_empty_physical [IsEmpty V] (C : V → Finset V) (D R : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) (β : V → Coins Δ k b n) : boundary G C D R L Δ k hk t b n β = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (fun i => isEmptyElim i.val.val)

theorem flagged_empty_low {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input)
    [IsEmpty (Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))]
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) : flagged G I L Δ k t b n B input c β = ∅ := by
  simpa only [boundary_empty_low, Finset.image_empty] using flagged_image G I L Δ k hk t ht b n B input d c β

theorem flagged_empty_centers {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input) (hD : d.D = ∅)
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) : flagged G I L Δ k t b n B input c β = ∅ := by
  simpa only [boundary_empty_centers G d.cover d.D d.R L Δ k hk t b n hD β, Finset.image_empty] using
    flagged_image G I L Δ k hk t ht b n B input d c β

theorem flagged_empty_physical [IsEmpty V] {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    flagged G I L Δ k t b n B input c β = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun v => isEmptyElim v)

section Expectation
-- Preserve the native vertex/Low equality decisions. Finite-source
-- enumeration is transported explicitly at the accepted theorem boundary.

noncomputable def meanBoundary (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k) (t b n : ℕ) : ℝ :=
  (∑ β : V → Coins Δ k b n, ((boundary G C D R L Δ k hk t b n β).card : ℝ)) / Fintype.card (V → Coins Δ k b n)
noncomputable def meanFlags {ids : ℕ} (I : BitCode V ids) (L Δ k t b n B : ℕ)
    (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) : ℝ :=
  (∑ β : V → Coins Δ k b n, ((flagged G I L Δ k t b n B input c β).card : ℝ)) / Fintype.card (V → Coins Δ k b n)

theorem native_sum_eq {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input) (c : V → Fin (B + 1)) :
    (∑ β : V → Coins Δ k b n, ((flagged G I L Δ k t b n B input c β).card : ℝ)) =
      ∑ β : V → Coins Δ k b n, ((boundary G d.cover d.D d.R L Δ k hk t b n β).card : ℝ) :=
  Finset.sum_congr rfl (fun β _ => congrArg (fun m : ℕ => (m : ℝ))
    (flagged_card G I L Δ k hk t ht b n B input d c β))

theorem native_mean_eq {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input) (c : V → Fin (B + 1)) :
    meanFlags G I L Δ k t b n B input c = meanBoundary G d.cover d.D d.R L Δ k hk t b n :=
  congrArg (fun s : ℝ => s / Fintype.card (V → Coins Δ k b n)) (native_sum_eq G I L Δ k hk t ht b n B input d c)

theorem means_empty_low {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input)
    [IsEmpty (Low d.D (GeneralCoveringOwnerVirtualPrepare.high G d.cover d.D d.R L Δ))] (c : V → Fin (B + 1)) :
    meanBoundary G d.cover d.D d.R L Δ k hk t b n = 0 ∧ meanFlags G I L Δ k t b n B input c = 0 := by
  simp only [meanBoundary, meanFlags, boundary_empty_low, flagged_empty_low G I L Δ k hk t ht b n B input d c,
    Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, zero_div, and_self]

theorem means_empty_centers {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n B : ℕ) (input : V → GeneralCoveringOwners.Input V)
    (d : GeneralCoveringTaskRandomPhysicalMarks.Original G input) (hD : d.D = ∅) (c : V → Fin (B + 1)) :
    meanBoundary G d.cover d.D d.R L Δ k hk t b n = 0 ∧ meanFlags G I L Δ k t b n B input c = 0 := by
  simp only [meanBoundary, meanFlags, boundary_empty_centers G d.cover d.D d.R L Δ k hk t b n hD,
    flagged_empty_centers G I L Δ k hk t ht b n B input d hD c,
    Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, zero_div, and_self]

theorem means_empty_physical [IsEmpty V] {ids : ℕ} (I : BitCode V ids) (L Δ k : ℕ) (hk : 0 < k)
    (t b n B : ℕ) (C : V → Finset V) (D R : Finset V) (input : V → GeneralCoveringOwners.Input V) (c : V → Fin (B + 1)) :
    meanBoundary G C D R L Δ k hk t b n = 0 ∧ meanFlags G I L Δ k t b n B input c = 0 := by
  simp only [meanBoundary, meanFlags, boundary_empty_physical, flagged_empty_physical,
    Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, zero_div, and_self]

/-- Only enumeration of the SAME finite Boolean source changes. No vertex
or Low equality instance is overridden. -/
private theorem source_sum_bound {A : Type} [K : Fintype A] (F : Fintype A)
    (f : A → ℝ) (z c : ℝ)
    (h : (@Finset.univ A F).sum f ≤ z * (@Fintype.card A F : ℝ) * c) :
    (∑ x : A, f x) ≤ z * (Fintype.card A : ℝ) * c := by
  have he : F = K := Subsingleton.elim _ _
  cases he
  exact h

/-- All witnesses, including the separator integer, precede graph/IDs/private
input. beta stays on PUBLIC V throughout both exact sums and means. -/
theorem parameters (a : ℝ) (ha : 0 ≤ a) (L : ℕ) (hL : 1 ≤ L) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {W : Type} [Fintype W] [LinearOrder W] (H : SimpleGraph W) [DecidableRel H.Adj],
        MinorDensity.Bound H a → ∀ (C : W → Finset W) (D R : Finset W),
        (∀ r ∈ R, C r ⊆ closed H r) → ∀ {ids : ℕ} (I : BitCode W ids),
        let Q := GeneralCoveringOwnerVirtualPrepare.high H C D R L Δ
        (∑ β : W → Coins Δ k b n, ((boundary H C D R L Δ k hk t b n β).card : ℝ)) ≤
          2 * η * Fintype.card (W → Coins Δ k b n) * Fintype.card (Low D Q) ∧
        (∑ β : W → Coins Δ k b n, ((boundary H C D R L Δ k hk t b n β).card : ℝ)) ≤
          2 * η * Fintype.card (W → Coins Δ k b n) * D.card ∧
        meanBoundary H C D R L Δ k hk t b n ≤ 2 * η * Fintype.card (Low D Q) ∧
        meanBoundary H C D R L Δ k hk t b n ≤ 2 * η * D.card := by
  obtain ⟨s, hs⟩ := exists_nat_gt (2 * a + 1)
  have hC : 0 ≤ GeneralCoveringOwnerSeparator.constant a s L + 1 := by
    have hc := GeneralCoveringOwnerSeparator.constant_nonneg a s L
    linarith
  obtain ⟨t, k, b, n, ht, hk, hp⟩ := ActiveFiniteBitPartition.parameters
    (GeneralCoveringOwnerSeparator.constant a s L + 1) hC Δ η hη
  refine ⟨t, k, b, n, ht, hk, ?_⟩
  intro W _ _ H _ hden C D R hlocal ids I
  let Q := GeneralCoveringOwnerVirtualPrepare.high H C D R L Δ
  let J := graph H C D R L Q
  let e := GeneralCoveringTaskPartitionMarks.lowEmbedding D Q
  let S := GeneralCoveringTaskPartitionMarks.activeImage e
  have hprofile := GeneralCoveringPhysicalBoundaryBound.public_profile H C D R L hL Q hlocal hden ha s hs
  have hdeg := PublicEmbedding.degree_bound J e Δ (GeneralCoveringTaskPhysicalMarks.low_degree H C D R L Δ)
  have hpH := hp (PublicEmbedding.graph J e)
  have hde : Classical.decEq W = (fun x y : W => LinearOrder.toDecidableEq x y) := Subsingleton.elim _ _
  rw [hde] at hpH
  have hb0 := (hpH hprofile hdeg S I).2.1
  have hb : (∑ β : W → Coins Δ k b n,
      ((ActiveFiniteBitPartition.flagged (PublicEmbedding.graph J e) I Δ k t b n S β).card : ℝ)) ≤
      2 * η * Fintype.card (W → Coins Δ k b n) * S.card :=
    source_sum_bound _ (fun β : W → Coins Δ k b n =>
      ((ActiveFiniteBitPartition.flagged (PublicEmbedding.graph J e) I Δ k t b n S β).card : ℝ))
      (2 * η) (S.card : ℝ) hb0
  have heq (β : W → Coins Δ k b n) : (boundary H C D R L Δ k hk t b n β).card =
      (ActiveFiniteBitPartition.flagged (PublicEmbedding.graph J e) I Δ k t b n S β).card :=
    (public_boundary_card H C D R L Δ k hk t b n β).trans
      (congrArg Finset.card (ActiveFiniteBitPartition.flagged_eq (PublicEmbedding.graph J e) I Δ k hk t ht b n S β hdeg)).symm
  have hsum : (∑ β : W → Coins Δ k b n, ((boundary H C D R L Δ k hk t b n β).card : ℝ)) =
      ∑ β : W → Coins Δ k b n, ((ActiveFiniteBitPartition.flagged (PublicEmbedding.graph J e) I Δ k t b n S β).card : ℝ) :=
    Finset.sum_congr rfl (fun β _ => congrArg (fun m : ℕ => (m : ℝ)) (heq β))
  have hS : S.card = Fintype.card (Low D Q) := by
    dsimp only [S, GeneralCoveringTaskPartitionMarks.activeImage]
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ]
  have hlow : (∑ β : W → Coins Δ k b n, ((boundary H C D R L Δ k hk t b n β).card : ℝ)) ≤
      2 * η * Fintype.card (W → Coins Δ k b n) * Fintype.card (Low D Q) := by
    rw [hsum]
    simpa only [hS] using hb
  have hsize : (Fintype.card (Low D Q) : ℝ) ≤ D.card := by
    exact_mod_cast GeneralCoveringPhysicalBoundaryBound.low_card (V := W) D Q
  have hD := hlow.trans (mul_le_mul_of_nonneg_left hsize (by positivity :
    (0 : ℝ) ≤ 2 * η * Fintype.card (W → Coins Δ k b n)))
  have hposN : 0 < Fintype.card (W → Coins Δ k b n) := Fintype.card_pos_iff.mpr ⟨fun _ _ _ => false⟩
  have hpos : (0 : ℝ) < Fintype.card (W → Coins Δ k b n) := by exact_mod_cast hposN
  refine ⟨hlow, hD, (div_le_iff₀ hpos).mpr ?_, (div_le_iff₀ hpos).mpr ?_⟩
  · calc
      _ ≤ 2 * η * Fintype.card (W → Coins Δ k b n) * Fintype.card (Low D Q) := hlow
      _ = _ := by ring
  · calc
      _ ≤ 2 * η * Fintype.card (W → Coins Δ k b n) * D.card := hD
      _ = _ := by ring

/-- The SAME witnesses bound actual returned physical flags, for original
private semantics and the SAME public beta. No distribution conversion. -/
theorem native_parameters (a : ℝ) (ha : 0 ≤ a) (L : ℕ) (hL : 1 ≤ L) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {W : Type} [Fintype W] [LinearOrder W] (H : SimpleGraph W) [DecidableRel H.Adj],
        MinorDensity.Bound H a → ∀ {ids : ℕ} (I : BitCode W ids) (B : ℕ)
        (input : W → GeneralCoveringOwners.Input W) (d : GeneralCoveringTaskRandomPhysicalMarks.Original H input)
        (c : W → Fin (B + 1)),
        let Q := GeneralCoveringOwnerVirtualPrepare.high H d.cover d.D d.R L Δ
        (∑ β : W → Coins Δ k b n, ((flagged H I L Δ k t b n B input c β).card : ℝ)) ≤
          2 * η * Fintype.card (W → Coins Δ k b n) * Fintype.card (Low d.D Q) ∧
        (∑ β : W → Coins Δ k b n, ((flagged H I L Δ k t b n B input c β).card : ℝ)) ≤
          2 * η * Fintype.card (W → Coins Δ k b n) * d.D.card ∧
        meanFlags H I L Δ k t b n B input c ≤ 2 * η * Fintype.card (Low d.D Q) ∧
        meanFlags H I L Δ k t b n B input c ≤ 2 * η * d.D.card := by
  obtain ⟨t, k, b, n, ht, hk, hp⟩ := parameters a ha L hL Δ η hη
  refine ⟨t, k, b, n, ht, hk, ?_⟩
  intro W _ _ H _ hden ids I B input d c
  have hb := hp H hden d.cover d.D d.R d.local_rows I
  simpa only [native_sum_eq H I L Δ k hk t ht b n B input d c,
    native_mean_eq H I L Δ k hk t ht b n B input d c] using hb
end Expectation

end Paper.GeneralCoveringRandomBoundaryBound

#print axioms Paper.GeneralCoveringRandomBoundaryBound.preparation_independent
#print axioms Paper.GeneralCoveringRandomBoundaryBound.flag_at_low
#print axioms Paper.GeneralCoveringRandomBoundaryBound.flagged_image
#print axioms Paper.GeneralCoveringRandomBoundaryBound.flagged_card
#print axioms Paper.GeneralCoveringRandomBoundaryBound.public_boundary_image
#print axioms Paper.GeneralCoveringRandomBoundaryBound.public_boundary_card
#print axioms Paper.GeneralCoveringRandomBoundaryBound.boundary_empty_low
#print axioms Paper.GeneralCoveringRandomBoundaryBound.boundary_empty_centers
#print axioms Paper.GeneralCoveringRandomBoundaryBound.boundary_empty_physical
#print axioms Paper.GeneralCoveringRandomBoundaryBound.flagged_empty_low
#print axioms Paper.GeneralCoveringRandomBoundaryBound.flagged_empty_centers
#print axioms Paper.GeneralCoveringRandomBoundaryBound.flagged_empty_physical
#print axioms Paper.GeneralCoveringRandomBoundaryBound.native_sum_eq
#print axioms Paper.GeneralCoveringRandomBoundaryBound.native_mean_eq
#print axioms Paper.GeneralCoveringRandomBoundaryBound.means_empty_low
#print axioms Paper.GeneralCoveringRandomBoundaryBound.means_empty_centers
#print axioms Paper.GeneralCoveringRandomBoundaryBound.means_empty_physical
#print axioms Paper.GeneralCoveringRandomBoundaryBound.parameters
#print axioms Paper.GeneralCoveringRandomBoundaryBound.native_parameters
