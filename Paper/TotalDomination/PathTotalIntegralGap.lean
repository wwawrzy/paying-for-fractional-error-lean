import Paper.TotalDomination.PathTotalIntegral
import Paper.TotalDomination.PathPowerGap

namespace Paper.TotalDomination.PathTotalIntegralGap
open SevenFoundation PathPowerTreewidth LocalCyclesRamseyReservoir

theorem window_lower_bound (r : ℕ) (c : ℝ) (hc : 0 ≤ c) (hct : c < 2) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ F : PathPowerRamsey.Rule r,
      ∃ ids : Fin n → ℕ, Function.Injective ids ∧
        (∀ i, 1 ≤ ids i ∧ ids i ≤ n) ∧
        ∀ out : Fin n → Bool, PathPowerRamsey.Agrees F ids out →
          dominates (graph n 1) (Finset.univ.filter (fun v => out v = true)) →
          c*((graph n 1).totalDominationNumber:ℝ) <
            (Finset.univ.filter (fun v => out v = true)).card := by
  let s := 2*r+1
  have hden : 0 < (2:ℝ)-c := by linarith
  obtain ⟨L,hL⟩ := exists_nat_gt (max (2*r+3:ℝ) (2*s/((2:ℝ)-c)))
  have hLnat : 2*r+2*1+1 ≤ L := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hL))
  have hs : s ≤ L := by dsimp [s];omega
  have hdiv := (le_max_right (2*r+3:ℝ) (2*s/((2:ℝ)-c))).trans_lt hL
  have hmul := (div_lt_iff₀ hden).mp hdiv
  have hgap : c*L < (2:ℝ)*(L-s:ℕ) := by rw [Nat.cast_sub hs];nlinarith
  obtain ⟨N,hN,hmargin⟩ := PathPowerGap.finite_margin 2 L s (ramseyBound 2 (2*r) L) 3
    (by decide) hs c hc hgap
  have hn : 2 ≤ 2*N := by omega
  refine ⟨2*N,hn,?_⟩
  intro F
  obtain ⟨ids,hinj,hIDs,hpack⟩ := PathPowerRamsey.packing (2*N) 1 r L hLnat F
  refine ⟨ids,hinj,hIDs,?_⟩
  intro out hagree hdom
  obtain ⟨b,rest,he,hr,hd⟩ := hpack out hagree hdom
  have hh := hmargin b rest _ he hr hd
  have hnum := PathTotalIntegral.number_bound (2*N) hn
  have heq : ((2*N:ℕ):ℝ)/2 = (N:ℝ) := by push_cast;ring
  rw [heq] at hnum
  have hcost := mul_le_mul_of_nonneg_left hnum hc
  push_cast at hh
  exact hcost.trans_lt hh

end Paper.TotalDomination.PathTotalIntegralGap
#print axioms Paper.TotalDomination.PathTotalIntegralGap.window_lower_bound
