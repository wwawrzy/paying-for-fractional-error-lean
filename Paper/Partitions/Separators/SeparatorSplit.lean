import Paper.Partitions.Separators.SeparatorProfile
import Paper.Preliminaries.InducedSubsets
import Paper.Preliminaries.ComponentContainment

/-! A proved separator yields a genuine finite disjoint family of physical
components. Every connected surviving set lies in one of these components. -/
namespace Paper.SeparatorSplit
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Data (S : Finset V) (C : ℝ) where
  cut : Finset V
  parts : Finset (Finset V)
  cut_subset : cut ⊆ S
  cut_size : (cut.card : ℝ) ≤ C * Real.sqrt S.card
  part_subset : ∀ U ∈ parts, U ⊆ S \ cut
  part_nonempty : ∀ U ∈ parts, U.Nonempty
  disjoint : (parts : Set (Finset V)).Pairwise Disjoint
  balanced : ∀ U ∈ parts, (U.card : ℝ) ≤ (S.card : ℝ) / 2
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
theorem exists_data {C : ℝ} (hprofile : SeparatorProfile.Bound G C) (S : Finset V) :
    Nonempty (Data G S C) := by
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

theorem sum_card_le {S : Finset V} {C : ℝ} (F : Data G S C) :
    ∑ U ∈ F.parts, U.card ≤ S.card := by
  have hd : ∀ U ∈ F.parts, ∀ W ∈ F.parts, U ≠ W → Disjoint U W :=
    fun U hU W hW hne => F.disjoint hU hW hne
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_sdiff.mp (F.part_subset U hU hv)).1
end Paper.SeparatorSplit
