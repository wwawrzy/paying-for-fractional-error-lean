import Paper.Partitions.Separators.SeparatorSplit

/-! Convert the usual two-thirds separator profile to the half-balanced
profile used by the implemented partition routine. Two rounds of separators
suffice, with a factor two in the constant. -/
namespace Paper.SeparatorBalance
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Bound (C beta : ℝ) : Prop :=
  ∀ I : Finset V, ∃ X : Finset ↥(I : Set V), (X.card : ℝ) ≤ C * Real.sqrt I.card ∧
    ∀ D : (DeletionComponents.deleted (G.induce (I : Set V)) X).ConnectedComponent,
      ((DeletionComponents.physical (G.induce (I : Set V)) X D).card : ℝ) ≤ beta * I.card

structure Data (S : Finset V) (C beta : ℝ) where
  cut : Finset V
  parts : Finset (Finset V)
  cut_subset : cut ⊆ S
  cut_size : (cut.card : ℝ) ≤ C * Real.sqrt S.card
  part_subset : ∀ U ∈ parts, U ⊆ S \ cut
  part_nonempty : ∀ U ∈ parts, U.Nonempty
  disjoint : (parts : Set (Finset V)).Pairwise Disjoint
  balanced : ∀ U ∈ parts, (U.card : ℝ) ≤ beta * S.card
  contains : ∀ T : Finset V, T ⊆ S \ cut → (G.induce (T : Set V)).Connected →
    ∃ U ∈ parts, T ⊆ U

noncomputable def component (S : Finset V) (Z : Finset ↥(S : Set V))
    (D : (DeletionComponents.deleted (G.induce (S : Set V)) Z).ConnectedComponent) : Finset V :=
  InducedSubsets.physical S (DeletionComponents.physical (G.induce (S : Set V)) Z D)

theorem component_disjoint (S : Finset V) (Z : Finset ↥(S : Set V))
    (D E : (DeletionComponents.deleted (G.induce (S : Set V)) Z).ConnectedComponent) (hne : D ≠ E) :
    Disjoint (component G S Z D) (component G S Z E) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hv
  obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hw
  have he : x = y := Subtype.ext (hxe.trans hye.symm)
  exact Finset.disjoint_left.mp (DeletionComponents.disjoint _ Z D E hne) hx (he ▸ hy)

set_option maxHeartbeats 2000000 in
theorem exists_data {C beta : ℝ} (hprofile : Bound G C beta) (S : Finset V) :
    Nonempty (Data G S C beta) := by
  classical
  obtain ⟨Z, hZ, hbal⟩ := hprofile S
  let J := G.induce (S : Set V)
  letI := Fintype.ofFinite (DeletionComponents.deleted J Z).ConnectedComponent
  let cut := InducedSubsets.physical S Z
  let parts := Finset.univ.image (component G S Z)
  have hsub : ∀ D, component G S Z D ⊆ S \ cut := by
    intro D v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_sdiff.mpr ⟨x.property, ?_⟩
    intro hcut
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hcut
    have hyx : y = x := Subtype.ext he
    exact Finset.disjoint_left.mp (DeletionComponents.avoids J Z D) hx (hyx ▸ hy)
  refine ⟨{
    cut := cut
    parts := parts
    cut_subset := InducedSubsets.physical_subset S Z
    cut_size := ?_
    part_subset := ?_
    part_nonempty := ?_
    disjoint := ?_
    balanced := ?_
    contains := ?_ }⟩
  · simpa only [cut, InducedSubsets.physical_card] using hZ
  · intro U hU
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hU
    exact hsub D
  · intro U hU
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨v, hv⟩ := DeletionComponents.nonempty J Z D
    exact ⟨v.val, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  · intro U hU W hW hne
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨E, _, rfl⟩ := Finset.mem_image.mp hW
    exact component_disjoint G S Z D E (fun he => hne (congrArg _ he))
  · intro U hU
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hU
    simpa only [component, InducedSubsets.physical_card] using hbal D
  · intro T hT hconn
    have hTS : T ⊆ S := fun _ hv => (Finset.mem_sdiff.mp (hT hv)).1
    let T' := InducedSubsets.lift S T
    have hc : (J.induce (T' : Set ↥(S : Set V))).Connected := InducedSubsets.lift_connected G S T hTS hconn
    have hd : Disjoint T' Z := by
      apply Finset.disjoint_left.mpr
      intro x hx hz
      have hxT : x.val ∈ T := Finset.mem_subtype.mp hx
      exact (Finset.mem_sdiff.mp (hT hxT)).2 (Finset.mem_image.mpr ⟨x, hz, rfl⟩)
    obtain ⟨x⟩ := hc.nonempty
    have hxZ : x.val ∉ Z := fun hz => Finset.disjoint_left.mp hd x.property hz
    let D := (DeletionComponents.deleted J Z).connectedComponentMk ⟨x.val, hxZ⟩
    have hxD : x.val ∈ DeletionComponents.physical J Z D := DeletionComponents.covers J Z hxZ
    have hcontain := ComponentContainment.subset J Z D T' hc hd
      ⟨x.val, Finset.mem_inter.mpr ⟨x.property, hxD⟩⟩
    refine ⟨component G S Z D, Finset.mem_image.mpr ⟨D, Finset.mem_univ _, rfl⟩, ?_⟩
    intro v hv
    let y : ↥(S : Set V) := ⟨v, hTS hv⟩
    have hy : y ∈ T' := Finset.mem_subtype.mpr hv
    exact Finset.mem_image.mpr ⟨y, hcontain hy, rfl⟩

/-- A two-thirds separator followed only in the unique large component. -/
theorem half_region {C : ℝ} (hC : 0 ≤ C) (hprofile : Bound G C (2/3)) (S : Finset V) :
    ∃ D : Finset V, D ⊆ S ∧ (D.card : ℝ) ≤ (2*C)*Real.sqrt S.card ∧
      ∀ T : Finset V, T ⊆ S \ D → (G.induce (T : Set V)).Connected →
        (T.card : ℝ) ≤ (S.card : ℝ)/2 := by
  classical
  obtain ⟨F⟩ := exists_data G hprofile S
  let large := F.parts.filter (fun U => S.card < 2*U.card)
  have hlarge : large.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro U hU W hW
    by_contra hne
    have hUF := (Finset.mem_filter.mp hU).1
    have hWF := (Finset.mem_filter.mp hW).1
    have hu := (Finset.mem_filter.mp hU).2
    have hw := (Finset.mem_filter.mp hW).2
    have hs : U ∪ W ⊆ S := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_sdiff.mp (F.part_subset U hUF hv)).1
      · exact (Finset.mem_sdiff.mp (F.part_subset W hWF hv)).1
    have hh := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint (F.disjoint hUF hWF hne)] at hh
    omega
  let next (U : Finset V) : Data G U C (2/3) := Classical.choice (exists_data G hprofile U)
  let D := F.cut ∪ large.biUnion (fun U => (next U).cut)
  have hD : D ⊆ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact F.cut_subset hv
    · obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_sdiff.mp (F.part_subset U (Finset.mem_filter.mp hU).1
        ((next U).cut_subset hv))).1
  refine ⟨D, hD, ?_, ?_⟩
  · have hcard : D.card ≤ F.cut.card+∑ U ∈ large, (next U).cut.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have hcard' : (D.card : ℝ) ≤ F.cut.card+∑ U ∈ large, ((next U).cut.card : ℝ) := by exact_mod_cast hcard
    have hsum : (∑ U ∈ large, ((next U).cut.card : ℝ)) ≤ Real.sqrt S.card*C := by
      calc
        _ ≤ ∑ _U ∈ large, C*Real.sqrt S.card := by
          apply Finset.sum_le_sum
          intro U hU
          have hsub : U ⊆ S := fun v hv => (Finset.mem_sdiff.mp
            (F.part_subset U (Finset.mem_filter.mp hU).1 hv)).1
          exact (next U).cut_size.trans (mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (by exact_mod_cast Finset.card_le_card hsub)) hC)
        _ = large.card*(C*Real.sqrt S.card) := by simp [mul_comm]
        _ ≤ 1*(C*Real.sqrt S.card) := mul_le_mul_of_nonneg_right (by exact_mod_cast hlarge) (by positivity)
        _ = _ := by ring
    linarith [F.cut_size]
  · intro T hT hc
    have hTcut : T ⊆ S \ F.cut := by
      intro v hv
      have hh := Finset.mem_sdiff.mp (hT hv)
      exact Finset.mem_sdiff.mpr ⟨hh.1, fun hx => hh.2 (Finset.mem_union_left _ hx)⟩
    obtain ⟨U, hUF, hTU⟩ := F.contains T hTcut hc
    by_cases hU : S.card < 2*U.card
    · have hUl : U ∈ large := Finset.mem_filter.mpr ⟨hUF, hU⟩
      have hTnext : T ⊆ U \ (next U).cut := by
        intro v hv
        refine Finset.mem_sdiff.mpr ⟨hTU hv, ?_⟩
        intro hx
        exact (Finset.mem_sdiff.mp (hT hv)).2
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨U, hUl, hx⟩))
      obtain ⟨W, hW, hTW⟩ := (next U).contains T hTnext hc
      have htcard : (T.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hTW
      have hWcard := (next U).balanced W hW
      have hUcard := F.balanced U hUF
      nlinarith [show (0 : ℝ) ≤ S.card by positivity]
    · have htcard : T.card ≤ U.card := Finset.card_le_card hTU
      have hnat : 2*T.card ≤ S.card := by omega
      have hh : 2*(T.card : ℝ) ≤ S.card := by exact_mod_cast hnat
      linarith

/-- Exact bridge to the half-balanced profile used by the proved implementation. -/
theorem half_profile {C : ℝ} (hC : 0 ≤ C) (hprofile : Bound G C (2/3)) :
    SeparatorProfile.Bound G (2*C) := by
  intro S
  obtain ⟨D, hDS, hcost, hgood⟩ := half_region G hC hprofile S
  let Z := InducedSubsets.lift S D
  refine ⟨Z, ?_, ?_⟩
  · simpa only [Z, InducedSubsets.lift_card S D hDS] using hcost
  · intro K
    let A := DeletionComponents.physical (G.induce (S : Set V)) Z K
    let T := InducedSubsets.physical S A
    have hc : (G.induce (T : Set V)).Connected :=
      InducedSubsets.physical_connected G S A (DeletionComponents.connected _ Z K)
    have hT : T ⊆ S \ D := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_sdiff.mpr ⟨u.property, ?_⟩
      intro hd
      have hz : u ∈ Z := Finset.mem_subtype.mpr hd
      exact Finset.disjoint_left.mp (DeletionComponents.avoids _ Z K) hu hz
    have hh := hgood T hT hc
    simpa only [T, InducedSubsets.physical_card] using hh

end Paper.SeparatorBalance
