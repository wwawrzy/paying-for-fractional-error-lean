import Paper.Preliminaries.CorePacking

/-! Graph-level sunflower-core hitting bound from the actual radius-one
incidence minor. Paper label: lem:cores. -/
namespace Paper.CoreHitting
attribute [local instance] Classical.propDecidable
open SevenFoundation CoreIncidence CoreHierarchy
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
theorem exists_core_cover (H : Finset (Finset V)) (O : Finset V) (j q : ℕ) (hq : 2 ≤ q)
    (hrank : ∀ s ∈ H, s.card ≤ j) (hO : ∀ s ∈ H, (s ∩ O).Nonempty)
    {a : ℝ} (hden : DepthOne.Bound (graph H) a) (hqa : a < q) :
    ∃ D : Finset V, (∀ C ∈ cores H q, (C ∩ D).Nonempty) ∧
      (D.card : ℝ) ≤ (1 + ((j - 1 : ℕ) : ℝ) * a / ((q : ℝ) - a)) * O.card := by
  classical
  let K := (cores H q).filter (fun C => Disjoint C O)
  obtain ⟨P, hPK, hpack, hmax⟩ := Sunflower.maximal_packing K
  have hP : P ⊆ cores H q := hPK.trans (Finset.filter_subset _ _)
  have hPO : ∀ C ∈ P, Disjoint C O := fun C hC => (Finset.mem_filter.mp (hPK hC)).2
  let U := P.biUnion id
  let D := O ∪ U
  have hcover : ∀ C ∈ cores H q, (C ∩ D).Nonempty := by
    intro C hC
    by_cases hCO : Disjoint C O
    · have hCK : C ∈ K := Finset.mem_filter.mpr ⟨hC, hCO⟩
      obtain ⟨v, hv⟩ := hmax C hCK ((mem_cores H q C).mp hC).1
      exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
        Finset.mem_union_right _ (Finset.mem_inter.mp hv).2⟩⟩
    · obtain ⟨v, hvC, hvO⟩ := Finset.not_disjoint_iff.mp hCO
      exact ⟨v, Finset.mem_inter.mpr ⟨hvC, Finset.mem_union_left _ hvO⟩⟩
  have hU : U.card ≤ (j - 1) * P.card := by
    calc
      _ ≤ ∑ C ∈ P, C.card := Finset.card_biUnion_le
      _ ≤ ∑ _C ∈ P, (j - 1) := Finset.sum_le_sum
        (fun C hC => core_rank_le H q hq j hrank C (hP hC))
      _ = _ := by simp [mul_comm]
  have hcount := CorePacking.packing_bound H P O q hq hP hpack hPO hO hden
  have hpos : 0 < (q : ℝ) - a := sub_pos.mpr hqa
  have hPdiv : (P.card : ℝ) ≤ (a * O.card) / ((q : ℝ) - a) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hcount)
  have hcard : D.card ≤ O.card + (j - 1) * P.card :=
    (Finset.card_union_le O U).trans (Nat.add_le_add_left hU _)
  have hcard' : (D.card : ℝ) ≤ O.card + ((j - 1 : ℕ) : ℝ) * P.card := by exact_mod_cast hcard
  refine ⟨D, hcover, ?_⟩
  calc
    _ ≤ _ := hcard'
    _ ≤ O.card + ((j - 1 : ℕ) : ℝ) * ((a * O.card) / ((q : ℝ) - a)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hPdiv (Nat.cast_nonneg _))
    _ = _ := by ring
end Paper.CoreHitting
