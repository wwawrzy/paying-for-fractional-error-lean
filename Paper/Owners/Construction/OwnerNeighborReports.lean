import Paper.Owners.Construction.OwnerInteraction
import Paper.Preliminaries.PrefixSet

/-! Exact physical hosted reports for virtual owner neighborhoods. This
proves the route identity needed before implementing bounded discovery;
the supplied cover is a graph fact from actual initialization. -/
namespace Paper.OwnerNeighborReports
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def report (D R : Finset V) (L : ℕ) (r : V) : Finset V :=
  ((closed G r).biUnion (OwnerInteraction.actualSupport G D R L)).erase (OwnerSupport.owner G D r)

noncomputable def owned (D R : Finset V) (L : ℕ) (i : V) : Finset V :=
  (closed G i ∩ OwnerInteraction.remaining G D R L).filter (fun r => OwnerSupport.owner G D r = i)

noncomputable def rootUnion (D R : Finset V) (L : ℕ) (i : V) : Finset V :=
  (owned G D R L i).biUnion (report G D R L)

noncomputable def neighbors (D R : Finset V) (L : ℕ) (i : V) : Finset V :=
  Finset.univ.filter (fun j => i ≠ j ∧ ∃ v, i ∈ OwnerInteraction.actualSupport G D R L v ∧
    j ∈ OwnerInteraction.actualSupport G D R L v)

theorem rootUnion_eq (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (i : V) :
    rootUnion G D R L i = neighbors G D R L i := by
  ext j
  constructor
  · intro hj
    obtain ⟨r, hr, hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hrBase, hri⟩ := Finset.mem_filter.mp hr
    have hrR := (Finset.mem_inter.mp hrBase).2
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    obtain ⟨v, hv, hjv⟩ := Finset.mem_biUnion.mp hj
    have hiv : i ∈ OwnerInteraction.actualSupport G D R L v :=
      Finset.mem_image.mpr ⟨r, Finset.mem_inter.mpr ⟨(closed_symm G r v).mpr hv, hrR⟩, hri⟩
    rw [hri] at hne
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne.symm, v, hiv, hjv⟩
  · intro hj
    obtain ⟨hne, v, hiv, hjv⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨r, hr, hri⟩ := Finset.mem_image.mp hiv
    have hrR := (Finset.mem_inter.mp hr).2
    have hr0 : r ∈ R := (Finset.mem_sdiff.mp hrR).1
    have howned := (OwnerSupport.owner_of_covered G D (hcover hr0)).2
    have hstar : r ∈ closed G i := by
      rw [← hri]
      exact (mem_closed G r _).mpr (howned.elim (fun he => Or.inl he.symm) Or.inr)
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hstar, hrR⟩, hri⟩, ?_⟩
    apply Finset.mem_erase.mpr
    refine ⟨fun he => hne (hri.symm.trans he.symm), ?_⟩
    exact Finset.mem_biUnion.mpr ⟨v, (closed_symm G r v).mp (Finset.mem_inter.mp hr).1, hjv⟩

theorem neighbors_eq_image (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (i : D) :
    neighbors G D R L i.val = ((OwnerInteraction.graph G D R L).neighborFinset i).image Subtype.val := by
  ext j
  constructor
  · intro hj
    obtain ⟨hne, v, hiv, hjv⟩ := (Finset.mem_filter.mp hj).2
    have hjD := OwnerInteraction.actual_labels G D R hcover L v hjv
    refine Finset.mem_image.mpr ⟨⟨j, hjD⟩, ?_, rfl⟩
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    exact ⟨fun he => hne (congrArg Subtype.val he), v, hiv, hjv⟩
  · intro hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hne, v, hiv, huv⟩ := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun he => hne (Subtype.ext he)), v, hiv, huv⟩

theorem card_rootUnion (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) (i : D) :
    (rootUnion G D R L i.val).card = (OwnerInteraction.graph G D R L).degree i := by
  rw [rootUnion_eq G D R hcover L, neighbors_eq_image G D R hcover L,
    Finset.card_image_of_injective _ Subtype.val_injective]
  rfl
end Paper.OwnerNeighborReports
