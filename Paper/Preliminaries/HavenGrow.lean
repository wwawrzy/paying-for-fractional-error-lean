import Paper.Preliminaries.HavenConfig

/-! Adding a small connecting branch inside the haven strictly decreases
the actual finite potential. This is the first configuration exchange. -/
namespace Paper.HavenGrow
attribute [local instance] Classical.propDecidable
open WeightedHaven Covey HavenConfig
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem cover_bound {h r : ℕ} {H : Haven G (h * r)} {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) : X.card ≤ C.card * r := by
  classical
  have hs : X ⊆ C.biUnion (fun S => X ∩ S) := by
    intro v hv
    obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp (good.cover hv)
    exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_inter.mpr ⟨hv, hvS⟩⟩
  calc
    _ ≤ (C.biUnion (fun S => X ∩ S)).card := Finset.card_le_card hs
    _ ≤ ∑ S ∈ C, (X ∩ S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ C, r := Finset.sum_le_sum good.overlap
    _ = C.card * r := by simp

set_option maxHeartbeats 2000000 in
theorem grow {h r : ℕ} (H : Haven G (h * r)) {C : Finset (Finset V)} {X : Finset V}
    (good : Good h r H C X) (hless : C.card < h) (T : Finset V)
    (hsub : T ⊆ H.region X) (hcard : T.card ≤ r) (hconn : (G.induce (T : Set V)).Connected)
    (hcontact : ∀ S ∈ C, Contacts G T S) :
    Good h r H (insert T C) (X ∪ T) ∧ score H (insert T C) (X ∪ T) < score H C X := by
  classical
  have hTn : T.Nonempty := by obtain ⟨v⟩ := hconn.nonempty; exact ⟨v.val, v.property⟩
  have hTS : ∀ S ∈ C, Disjoint T S := by
    intro S hS
    apply Finset.disjoint_left.mpr
    intro v hvT hvS
    exact Finset.disjoint_left.mp (good.separate S hS) hvS (hsub hvT)
  have hnot : T ∉ C := by
    intro hT
    obtain ⟨v, hv⟩ := hTn
    exact Finset.disjoint_left.mp (hTS T hT) hv hv
  have hCc : (insert T C).card = C.card + 1 := Finset.card_insert_of_notMem hnot
  have hXnew : (X ∪ T).card ≤ h * r := by
    have hc := Finset.card_union_le X T
    have hx := cover_bound good
    have hm := Nat.mul_le_mul_right r (show C.card + 1 ≤ h by omega)
    nlinarith
  have hregion := H.monotone X (X ∪ T) good.sizeX hXnew Finset.subset_union_left
  have hTnew : Disjoint T (H.region (X ∪ T)) := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvR
    exact Finset.disjoint_left.mp (H.avoids (X ∪ T) hXnew) hvR (Finset.mem_union_right X hvT)
  have hgood : Good h r H (insert T C) (X ∪ T) := by
    refine ⟨Covey.insert G good.covey T hconn hTS hcontact, by omega, ?_, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_union.mp hv with hx | ht
      · obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp (good.cover hx)
        exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_insert_of_mem hS, hvS⟩
      · exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_insert_self _ _, ht⟩
    · intro S hS
      rcases Finset.mem_insert.mp hS with hST | hSC
      · subst S
        rw [Finset.inter_eq_right.mpr (Finset.subset_union_right)]
        exact hcard
      · have he : (X ∪ T) ∩ S = X ∩ S := by
          ext v
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hx | ht, hs⟩
            · exact ⟨hx, hs⟩
            · exact False.elim (Finset.disjoint_left.mp (hTS S hSC) ht hs)
          · rintro ⟨hx, hs⟩
            exact ⟨Or.inl hx, hs⟩
        rw [he]
        exact good.overlap S hSC
    · intro S hS
      rcases Finset.mem_insert.mp hS with hST | hSC
      · subst S; exact hTnew
      · apply Finset.disjoint_left.mpr
        intro v hvS hvR
        exact Finset.disjoint_left.mp (good.separate S hSC) hvS (hregion hvR)
  have hne : H.region (X ∪ T) ≠ H.region X := by
    intro he
    obtain ⟨v, hv⟩ := hTn
    exact Finset.disjoint_left.mp hTnew hv (he.symm ▸ hsub hv)
  have hrlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hregion, hne⟩)
  have hu : (X ∪ T) ∪ H.region (X ∪ T) ⊆ X ∪ H.region X := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hx | ht
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_right _ (hsub ht)
    · exact Finset.mem_union_right _ (hregion hv)
  have huc := Finset.card_le_card hu
  refine ⟨hgood, ?_⟩
  dsimp only [score]
  rw [hCc]
  omega
end Paper.HavenGrow
