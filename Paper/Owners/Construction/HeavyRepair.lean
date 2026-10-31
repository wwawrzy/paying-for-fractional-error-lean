import Paper.Owners.Construction.HeavyDegrees
import Paper.Preliminaries.StarCounting

/-! The first owner repair is small by a genuine retained-heavy star minor.
Both heavy owners and heavy nonowners are included in the degree count. -/
namespace Paper.HeavyRepair
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyMinor HeavyDegrees
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def heavy (D R : Finset V) (L : ℕ) : Finset V :=
  Finset.univ.filter (fun v => L < (support G D R v).card)

theorem degree_lower (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ) {v : V}
    (hv : v ∈ heavy G D R L) :
    L + (if v ∈ D then 0 else 1) ≤
      (StarMap.graph G (contract G D R (heavy G D R L)) (D ∪ heavy G D R L)).degree
        ⟨v, Finset.mem_union_right D hv⟩ := by
  have hm := (Finset.mem_filter.mp hv).2
  by_cases hvD : v ∈ D
  · rw [if_pos hvD, add_zero]
    have he := support_erase_le_degree G D R (heavy G D R L) hcover hv
    have hlose : (support G D R v).card ≤ ((support G D R v).erase v).card + 1 := by
      by_cases hs : v ∈ support G D R v
      · have hh := Finset.card_erase_add_one hs
        omega
      · rw [Finset.erase_eq_of_notMem hs]
        omega
    omega
  · rw [if_neg hvD]
    have he := support_le_degree G D R (heavy G D R L) hcover hv hvD
    omega

set_option maxHeartbeats 2000000 in
theorem count (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ)
    {a : ℝ} (ha : 1 ≤ a) (hL : 4 * a ≤ L) (hden : MinorDensity.Bound G a) :
    (L : ℝ) * (heavy G D R L).card ≤ 2 * a * D.card := by
  classical
  let P := heavy G D R L
  let K := StarMap.graph G (contract G D R P) (D ∪ P)
  let P' := P.subtype (fun v => v ∈ D ∪ P)
  have hPc : P'.card = P.card := StarCounting.subtype_card _ _ Finset.subset_union_right
  have hOut : (P'.filter (fun v => v.val ∉ D)).card = (P \ D).card := by
    have he : P'.filter (fun v => v.val ∉ D) = (P \ D).subtype (fun v => v ∈ D ∪ P) := by
      ext v
      simp only [P', Finset.mem_filter, Finset.mem_subtype, Finset.mem_sdiff]
    rw [he]
    exact StarCounting.subtype_card _ _ (Finset.sdiff_subset.trans Finset.subset_union_right)
  have hKc : Fintype.card ↥(D ∪ P) = D.card + (P \ D).card := by
    rw [Fintype.card_coe]
    have hu := Finset.card_union_add_card_inter D P
    have hs := Finset.card_sdiff_add_card_inter P D
    rw [Finset.inter_comm P D] at hs
    omega
  have hlo : L * P.card + (P \ D).card ≤ (K.interedges P' Finset.univ).card := by
    rw [Incidence.card_interedges_eq_sum]
    have he : (∑ v ∈ P', (L + if v.val ∈ D then 0 else 1)) = L * P.card + (P \ D).card := by
      rw [Finset.sum_add_distrib]
      have ht : (∑ v ∈ P', if v.val ∈ D then 0 else 1) = (P'.filter (fun v => v.val ∉ D)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hD : v.val ∈ D <;> simp [hD]
      rw [ht, hOut]
      simp [hPc, mul_comm]
    rw [← he]
    apply Finset.sum_le_sum
    intro v hv
    have hmem : v.val ∈ P := Finset.mem_subtype.mp hv
    have hh := degree_lower G D R hcover L hmem
    have hvEq : (⟨v.val, Finset.mem_union_right D hmem⟩ : ↥(D ∪ P)) = v := Subtype.ext rfl
    rw [hvEq] at hh
    simpa only [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] using hh
  have hup := Incidence.card_interedges_le K P' Finset.univ
  rw [Finset.union_eq_right.mpr (Finset.subset_univ P'),
    Finset.inter_eq_left.mpr (Finset.subset_univ P')] at hup
  have hdensity := MinorDensity.minor_induced_bound G K hden ⟨(model G D R P hcover).toMinorModel⟩
  have hwhole := hdensity Finset.univ
  have hpart := hdensity P'
  have hc : (L : ℝ) * P.card + (P \ D).card ≤
      a * (D.card + (P \ D).card) + a * P.card := by
    have hr : (L : ℝ) * P.card + (P \ D).card ≤
        (K.inducedEdgeCount Finset.univ : ℝ) + K.inducedEdgeCount P' := by exact_mod_cast hlo.trans hup
    rw [Finset.card_univ, hKc] at hwhole
    rw [hPc] at hpart
    push_cast at hwhole
    linarith
  have hs : ((P \ D).card : ℝ) ≤ P.card := by
    have hh : (P \ D).card ≤ P.card := Finset.card_le_card Finset.sdiff_subset
    exact_mod_cast hh
  have hn := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hs)
  have hp : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hl := mul_nonneg (sub_nonneg.mpr hL) hp
  nlinarith

theorem count_div (D R : Finset V) (hcover : R ⊆ covered G D) (L : ℕ)
    {a : ℝ} (ha : 1 ≤ a) (hL : 4 * a ≤ L) (hden : MinorDensity.Bound G a) :
    ((heavy G D R L).card : ℝ) ≤ 2 * a * D.card / L := by
  have hLp : (0 : ℝ) < L := by linarith
  apply (le_div_iff₀ hLp).mpr
  simpa only [mul_comm] using count G D R hcover L ha hL hden
end Paper.HeavyRepair
