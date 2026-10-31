import Paper.Endpoints.Girth.HighGirthOutput
import Paper.Preliminaries.Incidence
set_option maxHeartbeats 200000
namespace Paper.HighGirthDensityExcess

theorem density_excess_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (a : Real) (hden : Paper.Incidence.InducedDensityBound G a) :
    ((Paper.HighGirthRounding.high G x).card : Real) ≤ Paper.HighGirthRounding.excess G x ∧
      Paper.HighGirthRounding.excess G x ≤
        (2 * a - 2) * (Paper.HighGirthRounding.high G x).card +
          a * (Paper.HighGirthRounding.middle G x).card -
            (a + 1) * (Paper.HighGirthRounding.outside G x).card := by
  classical
    let H := Paper.HighGirthRounding.high G x
    let R := Paper.HighGirthRounding.residual G x
    let L := Paper.HighGirthRounding.middle G x
    let B := R ∩ Paper.SevenFoundation.covered G H
    constructor
    · change (H.card : Real) ≤ ∑ v ∈ H, ((Paper.HighGirthRounding.hits G x v : Real) - 3)
      calc
        (H.card : Real) = ∑ _v ∈ H, (1 : Real) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro v hv
          have hn := (Finset.mem_filter.mp hv).2
          have hr : (4 : Real) ≤ (Paper.HighGirthRounding.hits G x v : Real) := by exact_mod_cast hn
          linarith
    · have hinc := Paper.Incidence.closed_incidence_le_of_density G hden H B
      have hsum : (∑ v ∈ H, ((Paper.SevenFoundation.closed G v ∩ B).card : Real)) =
          ∑ v ∈ H, (Paper.HighGirthRounding.hits G x v : Real) := by
        apply Finset.sum_congr rfl
        intro v hv
        have heq : Paper.SevenFoundation.closed G v ∩ B = Paper.SevenFoundation.closed G v ∩ R := by
          ext u
          constructor
          · intro hu
            obtain ⟨huv, huB⟩ := Finset.mem_inter.mp hu
            exact Finset.mem_inter.mpr ⟨huv, (Finset.mem_inter.mp huB).1⟩
          · intro hu
            obtain ⟨huv, huR⟩ := Finset.mem_inter.mp hu
            exact Finset.mem_inter.mpr ⟨huv, Finset.mem_inter.mpr ⟨huR, Finset.mem_biUnion.mpr ⟨v, hv, huv⟩⟩⟩
        rw [heq]
        rfl
      have hinter : H ∩ B = H ∩ R := by
        ext v
        constructor
        · rintro hv
          obtain ⟨hvH, hvB⟩ := Finset.mem_inter.mp hv
          exact Finset.mem_inter.mpr ⟨hvH, (Finset.mem_inter.mp hvB).1⟩
        · intro hv
          obtain ⟨hvH, hvR⟩ := Finset.mem_inter.mp hv
          exact Finset.mem_inter.mpr ⟨hvH, Finset.mem_inter.mpr ⟨hvR, Paper.SevenFoundation.subset_covered G H hvH⟩⟩
      have hunion : H ∪ B = H ∪ L := by
        ext v
        simp only [B, L, H, R, Paper.HighGirthRounding.middle, Paper.HighGirthRounding.last,
          Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have hdisjoint : Disjoint H L := by
        apply Finset.disjoint_left.mpr
        intro v hvH hvL
        exact (Finset.mem_sdiff.mp hvL).2 (Finset.mem_union_left _ hvH)
      rw [hsum, hinter, hunion, Finset.card_union_of_disjoint hdisjoint] at hinc
      push_cast at hinc
      have hcard : (H.card : Real) = (H ∩ R).card + (Paper.HighGirthRounding.outside G x).card := by
        have hn := Finset.card_sdiff_add_card_inter H R
        change (Paper.HighGirthRounding.outside G x).card + (H ∩ R).card = H.card at hn
        exact_mod_cast (show H.card = (H ∩ R).card + (Paper.HighGirthRounding.outside G x).card by omega)
      have he : Paper.HighGirthRounding.excess G x =
          (∑ v ∈ H, (Paper.HighGirthRounding.hits G x v : Real)) - 3 * (H.card : Real) := by
        simp [Paper.HighGirthRounding.excess, Finset.sum_sub_distrib, H, mul_comm]
      change Paper.HighGirthRounding.excess G x ≤ (2 * a - 2) * (H.card : Real) + a * (L.card : Real) -
        (a + 1) * ((Paper.HighGirthRounding.outside G x).card : Real)
      rw [hcard] at hinc he ⊢
      nlinarith only [hinc, he]

end Paper.HighGirthDensityExcess

#print axioms Paper.HighGirthDensityExcess.density_excess_bounds
