import Paper.Partitions.Separators.SeparatorSplit
import Paper.Partitions.Separators.SeparatorPotential

/-! Actual finite recursive separator deletion. Every connected surviving
set has size at most k; the deleted set costs at most 4 C n / sqrt(k). -/
namespace Paper.RecursiveDeletion
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Good (S D : Finset V) (k : ℕ) : Prop := D ⊆ S ∧
  ∀ T : Finset V, T ⊆ S \ D → (G.induce (T : Set V)).Connected → T.card ≤ k

set_option maxHeartbeats 3000000 in
theorem strong {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (k : ℕ) (hk : 0 < k) (S : Finset V) (hlarge : k < S.card) :
    ∃ D : Finset V, Good G S D k ∧
      (D.card : ℝ) ≤ 4 * C / Real.sqrt k * S.card - 3 * C * Real.sqrt S.card := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    obtain ⟨F⟩ := SeparatorSplit.exists_data G hprofile S
    let large := F.parts.filter (fun U => k < U.card)
    have hex : ∀ U ∈ large, ∃ D : Finset V, Good G U D k ∧
        (D.card : ℝ) ≤ 4 * C / Real.sqrt k * U.card - 3 * C * Real.sqrt U.card := by
      intro U hU
      have hUF := (Finset.mem_filter.mp hU).1
      have hUk := (Finset.mem_filter.mp hU).2
      have hb := F.balanced U hUF
      have hnpos : 0 < S.card := hk.trans hlarge
      have hsmall : U.card < n := by
        have hr : (U.card : ℝ) < S.card := by
          have hp : (0 : ℝ) < S.card := by exact_mod_cast hnpos
          linarith
        have hnat : U.card < S.card := by exact_mod_cast hr
        omega
      exact ih U.card hsmall U hUk rfl
    let d (U : Finset V) : Finset V := if hU : U ∈ large then Classical.choose (hex U hU) else ∅
    have hd : ∀ U (hU : U ∈ large), Good G U (d U) k ∧
        ((d U).card : ℝ) ≤ 4 * C / Real.sqrt k * U.card - 3 * C * Real.sqrt U.card := by
      intro U hU
      simpa only [d, dif_pos hU] using Classical.choose_spec (hex U hU)
    let D := F.cut ∪ large.biUnion d
    refine ⟨D, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact F.cut_subset hv
      · obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
        exact (Finset.mem_sdiff.mp (F.part_subset U (Finset.mem_filter.mp hU).1 ((hd U hU).1.1 hv))).1
    · intro T hT hc
      have hTcut : T ⊆ S \ F.cut := by
        intro v hv
        have hh := Finset.mem_sdiff.mp (hT hv)
        exact Finset.mem_sdiff.mpr ⟨hh.1, fun hx => hh.2 (Finset.mem_union_left _ hx)⟩
      obtain ⟨U, hUF, hTU⟩ := F.contains T hTcut hc
      by_cases hU : k < U.card
      · have hUl : U ∈ large := Finset.mem_filter.mpr ⟨hUF, hU⟩
        apply (hd U hUl).1.2 T _ hc
        intro v hv
        refine Finset.mem_sdiff.mpr ⟨hTU hv, ?_⟩
        intro hvd
        exact (Finset.mem_sdiff.mp (hT hv)).2
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨U, hUl, hvd⟩))
      · exact (Finset.card_le_card hTU).trans (Nat.le_of_not_gt hU)
    · have hcard : D.card ≤ F.cut.card + ∑ U ∈ large, (d U).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
      have hreal : (D.card : ℝ) ≤ F.cut.card + ∑ U ∈ large, ((d U).card : ℝ) := by exact_mod_cast hcard
      have hcost := Finset.sum_le_sum (fun U hU => (hd U hU).2)
      have hsumNat : ∑ U ∈ large, U.card ≤ S.card :=
        (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans (SeparatorSplit.sum_card_le G F)
      have hsum : ∑ U ∈ large, (U.card : ℝ) ≤ S.card := by exact_mod_cast hsumNat
      have hpotential := SeparatorPotential.combine large (fun U => (U.card : ℝ)) (k := (k : ℝ)) hC
        (by exact_mod_cast hk) (by exact_mod_cast (Nat.le_of_lt hlarge))
        (fun U _ => Nat.cast_nonneg _) (fun U hU => F.balanced U (Finset.mem_filter.mp hU).1) hsum
      rw [← hn]
      linarith [F.cut_size]

theorem exists_cut {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (k : ℕ) (hk : 0 < k) (S : Finset V) :
    ∃ D : Finset V, Good G S D k ∧ (D.card : ℝ) ≤ 4 * C / Real.sqrt k * S.card := by
  by_cases hlarge : k < S.card
  · obtain ⟨D, hD, hb⟩ := strong G hC hprofile k hk S hlarge
    refine ⟨D, hD, ?_⟩
    have hp : 0 ≤ 3 * C * Real.sqrt S.card := by positivity
    linarith
  · refine ⟨∅, ⟨Finset.empty_subset _, ?_⟩, ?_⟩
    · intro T hT _
      exact (Finset.card_le_card (fun _ hv => (Finset.mem_sdiff.mp (hT hv)).1)).trans (Nat.le_of_not_gt hlarge)
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
end Paper.RecursiveDeletion
