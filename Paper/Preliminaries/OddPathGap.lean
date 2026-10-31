import Paper.Preliminaries.OddPathGeometry
import Paper.TotalDomination.PathPowerGap
namespace Paper.OddPathPower
open SevenFoundation LocalCyclesRamseyReservoir
open TotalDomination
/-- A finite witness size precedes the arbitrary ID-sensitive window rule.
The benchmark is the actual open-neighborhood fractional total optimum. -/
theorem window_lower_bound (r : ℕ) (c : ℝ) (hc : 0 ≤ c) (hct : c < 4) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ F : PathPowerRamsey.Rule r,
      ∃ ids : Fin n → ℕ, Function.Injective ids ∧
        (∀ i, 1 ≤ ids i ∧ ids i ≤ n) ∧
        ∀ out : Fin n → Bool, PathPowerRamsey.Agrees F ids out →
          dominates (graph n 3) (Finset.univ.filter (fun v => out v = true)) →
          c*FractionalSolver.fractionalNumber (graph n 3) <
            (Finset.univ.filter (fun v => out v = true)).card := by
  let w := 4
  let s := 2*r+1
  have hw : 1 ≤ w := by norm_num [w]
  have hden : 0 < (w:ℝ)-c := by dsimp [w];push_cast;linarith
  obtain ⟨L,hL⟩ := exists_nat_gt (max (2*r+7:ℝ) ((w:ℝ)*s/((w:ℝ)-c)))
  have hLnat : 2*r+7 ≤ L := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hL))
  have hs : s ≤ L := by dsimp [s];omega
  have hdiv := (le_max_right (2*r+7:ℝ) ((w:ℝ)*s/((w:ℝ)-c))).trans_lt hL
  have hmul := (div_lt_iff₀ hden).mp hdiv
  have hgap : c*L < (w:ℝ)*(L-s:ℕ) := by rw [Nat.cast_sub hs];nlinarith
  obtain ⟨N,hN,hmargin⟩ := TotalDomination.PathPowerGap.finite_margin w L s (ramseyBound 2 (2*r) L) 6 hw hs c hc hgap
  have hn : 2 ≤ w*N := by
    calc
      2 = 2*1 := rfl
      _ ≤ w*N := Nat.mul_le_mul (by norm_num [w]) (by omega)
  refine ⟨w*N,hn,?_⟩
  intro F
  obtain ⟨ids,hinj,hIDs,hpack⟩ := PathPowerRamsey.packing (w*N) 3 r L hLnat F
  refine ⟨ids,hinj,hIDs,?_⟩
  intro out hagree hdom
  have hdom' : dominates (PathPowerTreewidth.graph (w*N) 3) (Finset.univ.filter (fun v => out v=true)) := by
    intro r
    obtain ⟨v,hv,hvr⟩ := Finset.mem_biUnion.mp (hdom r)
    refine Finset.mem_biUnion.mpr ⟨v,hv,?_⟩
    rcases (mem_closed (graph (w*N) 3) r v).mp hvr with he | ha
    · exact (mem_closed _ r v).mpr (Or.inl he)
    · exact (mem_closed _ r v).mpr (Or.inr ha.1)
  obtain ⟨b,rest,he,hr,hd⟩ := hpack out hagree hdom' 
  have hh := hmargin b rest _ he hr hd
  have hfrac := total_fractional_bound (w*N) hn
  have heq : ((w*N:ℕ):ℝ)/4=(N:ℝ) := by dsimp [w];push_cast;ring
  rw [heq] at hfrac
  have hcost := mul_le_mul_of_nonneg_left hfrac hc
  push_cast at hh
  exact hcost.trans_lt hh


end Paper.OddPathPower
#print axioms Paper.OddPathPower.window_lower_bound
