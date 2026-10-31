import Paper.Owners.Construction.HeavyRepair

/-! Actual support after the first repair and the two owner interaction
graphs. All actual candidate support lists have at most L labels. -/
namespace Paper.OwnerInteraction
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyRepair
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def remaining (D R : Finset V) (L : ℕ) : Finset V :=
  R \ covered G (heavy G D R L)

noncomputable def actualSupport (D R : Finset V) (L : ℕ) (v : V) : Finset V :=
  ((closed G v) ∩ remaining G D R L).image (owner G D)

theorem actual_subset (D R : Finset V) (L : ℕ) (v : V) :
    actualSupport G D R L v ⊆ support G D R v := by
  intro d hd
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hd
  have hm := Finset.mem_inter.mp hr
  exact Finset.mem_image.mpr ⟨r, Finset.mem_inter.mpr
    ⟨hm.1, Finset.mem_union_left _ (Finset.mem_sdiff.mp hm.2).1⟩, rfl⟩

theorem heavy_empty (D R : Finset V) (L : ℕ) {v : V} (hv : v ∈ heavy G D R L) :
    actualSupport G D R L v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨r, hr, _⟩ := Finset.mem_image.mp hd
  have hm := Finset.mem_inter.mp hr
  have hrem := Finset.mem_sdiff.mp hm.2
  exact hrem.2 (Finset.mem_biUnion.mpr ⟨v, hv, hm.1⟩)

theorem support_bound (D R : Finset V) (L : ℕ) (v : V) : (actualSupport G D R L v).card ≤ L := by
  by_cases hv : v ∈ heavy G D R L
  · rw [heavy_empty G D R L hv, Finset.card_empty]
    omega
  · have hn : ¬ L < (support G D R v).card := fun hh => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    exact (Finset.card_le_card (actual_subset G D R L v)).trans (by omega)

theorem actual_labels (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (v : V) :
    actualSupport G D R L v ⊆ D := (actual_subset G D R L v).trans (support_labels G D R hcover v)

def interaction (D : Finset V) (S : V → Finset V) : SimpleGraph D where
  Adj i j := i ≠ j ∧ ∃ v, i.val ∈ S v ∧ j.val ∈ S v
  symm := by rintro i j ⟨hne, v, hi, hj⟩; exact ⟨hne.symm, v, hj, hi⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def lightSupport (D R : Finset V) (L : ℕ) (v : V) : Finset V :=
  if v ∈ heavy G D R L then ∅ else support G D R v

noncomputable def graph (D R : Finset V) (L : ℕ) : SimpleGraph D := interaction D (actualSupport G D R L)
noncomputable def augmentedGraph (D R : Finset V) (L : ℕ) : SimpleGraph D := interaction D (lightSupport G D R L)

theorem graph_le_augmented (D R : Finset V) (L : ℕ) : graph G D R L ≤ augmentedGraph G D R L := by
  rintro i j ⟨hne, v, hi, hj⟩
  have hv : v ∉ heavy G D R L := by
    intro hv
    rw [heavy_empty G D R L hv] at hi
    exact Finset.notMem_empty _ hi
  exact ⟨hne, v, by simpa [lightSupport, hv] using actual_subset G D R L v hi,
    by simpa [lightSupport, hv] using actual_subset G D R L v hj⟩
end Paper.OwnerInteraction
