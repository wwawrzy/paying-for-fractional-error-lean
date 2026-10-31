import Paper.Preliminaries.HavenBoundary

/-! Replace one branch by its genuine extended deletion component. The
score drops by at least twice the old branch's intersection with X. -/
namespace Paper.HavenReplace
attribute [local instance] Classical.propDecidable
open WeightedHaven Covey HavenConfig HavenExtension
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 3000000 in
theorem replace {h r : ℕ} (H : Haven G (h * r)) {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) (hless : C.card < h) (Z : Finset V) (hZ : Z.card ≤ r)
    (hZsub : Z ⊆ H.region X) (S : Finset V) (hS : S ∈ C) (T : Finset V) (hST : S ⊆ T)
    (hconn : (G.induce (T : Set V)).Connected)
    (hTF : Disjoint T (H.region (X ∪ Z) ∪ vertices (C.erase S)))
    (hclosed : ∀ u ∈ T, ∀ v, v ∉ H.region (X ∪ Z) ∪ vertices (C.erase S) → G.Adj u v → v ∈ T)
    (hcontact : ¬ Contacts G S (H.region (X ∪ Z))) :
    Good h r H (insert T (C.erase S)) (replacementX X S Z T) ∧
      score H (insert T (C.erase S)) (replacementX X S Z T) + 2 * (X ∩ S).card ≤ score H C X := by
  classical
  let X' := replacementX X S Z T
  have hb := HavenBoundary.avoids_extended H good hless Z hZ hZsub S hS T hST hTF hclosed hcontact
  have hBsub : H.region X' ⊆ H.region X := by
    intro v hv
    by_contra hn
    exact Finset.disjoint_left.mp hb hv (Finset.mem_union_right T
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩))
  have hBT : Disjoint (H.region X') T := by
    apply Finset.disjoint_left.mpr
    intro v hvB hvT
    exact Finset.disjoint_left.mp hb hvB (Finset.mem_union_left _ hvT)
  have hTO : ∀ U ∈ C.erase S, Disjoint T U := by
    intro U hU
    apply Finset.disjoint_left.mpr
    intro v hvT hvU
    exact Finset.disjoint_left.mp hTF hvT (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨U, hU, hvU⟩))
  have hcovey : IsCovey G (insert T (C.erase S)) := by
    apply Covey.insert G (Covey.erase G good.covey S) T hconn hTO
    intro U hU
    have hh := Finset.mem_erase.mp hU
    exact contacts_mono G (good.covey.contact S hS U hh.2 (Ne.symm hh.1)) hST (fun _ h => h)
  have hTn : T.Nonempty := by obtain ⟨v⟩ := hconn.nonempty; exact ⟨v.val, v.property⟩
  have hnot : T ∉ C.erase S := by
    intro hT
    obtain ⟨v, hv⟩ := hTn
    exact Finset.disjoint_left.mp (hTO T hT) hv hv
  have hCc : (insert T (C.erase S)).card = C.card := by
    rw [Finset.card_insert_of_notMem hnot]
    exact Finset.card_erase_add_one hS
  have hOld : Disjoint (X \ S) T := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvT
    have hh := Finset.mem_sdiff.mp hvX
    obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp (good.cover hh.1)
    have hUS : U ≠ S := fun he => hh.2 (he ▸ hvU)
    exact Finset.disjoint_left.mp (hTO U (Finset.mem_erase.mpr ⟨hUS, hU⟩)) hvT hvU
  have hgood : Good h r H (insert T (C.erase S)) X' := by
    refine ⟨hcovey, by omega, ?_, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_union.mp hv with hvZT | hvXS
      · exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_insert_self _ _, (Finset.mem_inter.mp hvZT).2⟩
      · have hh := Finset.mem_sdiff.mp hvXS
        obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp (good.cover hh.1)
        have hUS : U ≠ S := fun he => hh.2 (he ▸ hvU)
        exact Finset.mem_biUnion.mpr ⟨U, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hUS, hU⟩), hvU⟩
    · intro U hU
      rcases Finset.mem_insert.mp hU with hUT | hUO
      · subst U
        have hs : X' ∩ T ⊆ Z := by
          intro v hv
          have hh := Finset.mem_inter.mp hv
          rcases Finset.mem_union.mp hh.1 with hvZT | hvXS
          · exact (Finset.mem_inter.mp hvZT).1
          · exact False.elim (Finset.disjoint_left.mp hOld hvXS hh.2)
        exact (Finset.card_le_card hs).trans hZ
      · have hUC := Finset.mem_of_mem_erase hUO
        have hs : X' ∩ U ⊆ X ∩ U := by
          intro v hv
          have hh := Finset.mem_inter.mp hv
          rcases Finset.mem_union.mp hh.1 with hvZT | hvXS
          · exact False.elim (Finset.disjoint_left.mp (good.separate U hUC) hh.2
              (hZsub (Finset.mem_inter.mp hvZT).1))
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hvXS).1, hh.2⟩
        exact (Finset.card_le_card hs).trans (good.overlap U hUC)
    · intro U hU
      rcases Finset.mem_insert.mp hU with hUT | hUO
      · subst U; exact hBT.symm
      · apply Finset.disjoint_left.mpr
        intro v hvU hvB
        exact Finset.disjoint_left.mp (good.separate U (Finset.mem_of_mem_erase hUO)) hvU (hBsub hvB)
  have hUnion : X' ∪ H.region X' ⊆ (X ∪ H.region X) \ (X ∩ S) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvX | hvB
    · rcases Finset.mem_union.mp hvX with hvZT | hvXS
      · have hh := Finset.mem_inter.mp hvZT
        have hvB := hZsub hh.1
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hvB, ?_⟩
        intro hvI
        exact Finset.disjoint_left.mp (H.avoids X good.sizeX) hvB (Finset.mem_inter.mp hvI).1
      · have hh := Finset.mem_sdiff.mp hvXS
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hh.1, fun h => hh.2 (Finset.mem_inter.mp h).2⟩
    · refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (hBsub hvB), ?_⟩
      intro hvI
      exact Finset.disjoint_left.mp hBT hvB (hST (Finset.mem_inter.mp hvI).2)
  have hCunion := Finset.card_le_card hUnion
  have hI : X ∩ S ⊆ X ∪ H.region X := Finset.inter_subset_left.trans Finset.subset_union_left
  have hDiff := Finset.card_sdiff_add_card_eq_card hI
  have hBcard := Finset.card_le_card hBsub
  refine ⟨hgood, ?_⟩
  change (insert T (C.erase S)).card + 2 * ((H.region X').card + (X' ∪ H.region X').card) +
    2 * (X ∩ S).card ≤ C.card + 2 * ((H.region X).card + (X ∪ H.region X).card)
  rw [hCc]
  omega
end Paper.HavenReplace
