import Paper.TotalDomination.PathPowerFractional
import Paper.Preliminaries.PathPowerGap

namespace Paper.TotalDomination.PathPowerGap
open SevenFoundation PathPowerTreewidth LocalCyclesRamseyReservoir

/-- The finite Ramsey loss and the additive optimum-bound loss both fit
inside the strict approximation gap. -/
theorem finite_margin (w L s R e : ℕ) (hw : 1 ≤ w) (hs : s ≤ L)
    (c : ℝ) (hc : 0 ≤ c) (hgap : c*L < (w:ℝ)*(L-s:ℕ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ b rest out : ℕ,
      w*N = b*L+rest → rest < R → b*(L-s) ≤ out → c*((N:ℝ)+e) < out := by
  let δ : ℝ := (w:ℝ)*(L-s:ℕ)-c*L
  have hδ : 0 < δ := sub_pos.mpr hgap
  obtain ⟨K,hK⟩ := exists_nat_gt ((c*R+(w:ℝ)*c*e)/δ)
  have hKR : c*R+(w:ℝ)*c*e < δ*K := by
    have hh := (div_lt_iff₀ hδ).mp hK
    nlinarith
  let N := (K+1)*L+R+1
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro b rest out he hr hd
  have hb : K < b := by
    by_contra h
    have hm := Nat.mul_le_mul_right L (Nat.le_of_not_gt h)
    have hn := Nat.le_mul_of_pos_left N hw
    dsimp [N] at hn he
    nlinarith
  have he' : (w:ℝ)*N = b*L+rest := by exact_mod_cast he
  have hr' : (rest:ℝ) ≤ R := by exact_mod_cast hr.le
  have hd' : (b:ℝ)*(L-s:ℕ) ≤ out := by exact_mod_cast hd
  have hb' : (K:ℝ) ≤ b := by exact_mod_cast hb.le
  have hprod := mul_le_mul_of_nonneg_left hb' hδ.le
  have hrest := mul_le_mul_of_nonneg_left hr' hc
  have hw' : (0:ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hout := mul_le_mul_of_nonneg_left hd' hw'.le
  dsimp [δ] at hprod hKR
  rw [Nat.cast_sub hs] at hout hprod hKR
  have hec := congrArg (fun z : ℝ => c*z) he'
  have hscaled : (w:ℝ)*(c*((N:ℝ)+e)) < (w:ℝ)*out := by nlinarith only [hout,hprod,hKR,hrest,hec]
  exact (mul_lt_mul_iff_right₀ hw').mp hscaled

/-- A finite witness size precedes the arbitrary ID-sensitive window rule.
The benchmark is the actual open-neighborhood fractional total optimum. -/
theorem window_lower_bound (t r : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 ≤ c) (hct : c < 2*t) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ F : PathPowerRamsey.Rule r,
      ∃ ids : Fin n → ℕ, Function.Injective ids ∧
        (∀ i, 1 ≤ ids i ∧ ids i ≤ n) ∧
        ∀ out : Fin n → Bool, PathPowerRamsey.Agrees F ids out →
          dominates (graph n t) (Finset.univ.filter (fun v => out v = true)) →
          c*FractionalSolver.fractionalNumber (graph n t) <
            (Finset.univ.filter (fun v => out v = true)).card := by
  let w := 2*t
  let s := 2*r+1
  have hw : 1 ≤ w := by dsimp [w];omega
  have hden : 0 < (w:ℝ)-c := by dsimp [w];push_cast;linarith
  obtain ⟨L,hL⟩ := exists_nat_gt (max (2*r+2*t+1:ℝ) ((w:ℝ)*s/((w:ℝ)-c)))
  have hLnat : 2*r+2*t+1 ≤ L := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hL))
  have hs : s ≤ L := by dsimp [s];omega
  have hdiv := (le_max_right (2*r+2*t+1:ℝ) ((w:ℝ)*s/((w:ℝ)-c))).trans_lt hL
  have hmul := (div_lt_iff₀ hden).mp hdiv
  have hgap : c*L < (w:ℝ)*(L-s:ℕ) := by rw [Nat.cast_sub hs];nlinarith
  obtain ⟨N,hN,hmargin⟩ := finite_margin w L s (ramseyBound 2 (2*r) L) (2*t) hw hs c hc hgap
  have hn : 2 ≤ w*N := by
    calc
      2 = 2*1 := rfl
      _ ≤ w*N := Nat.mul_le_mul (by dsimp [w];omega) (by omega)
  refine ⟨w*N,hn,?_⟩
  intro F
  obtain ⟨ids,hinj,hIDs,hpack⟩ := PathPowerRamsey.packing (w*N) t r L hLnat F
  refine ⟨ids,hinj,hIDs,?_⟩
  intro out hagree hdom
  obtain ⟨b,rest,he,hr,hd⟩ := hpack out hagree hdom
  have hh := hmargin b rest _ he hr hd
  have hfrac := PathPowerFractional.number_bound (w*N) t hn ht
  have heq : ((w*N:ℕ):ℝ)/(2*(t:ℝ)) = (N:ℝ) := by
    have htR : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    dsimp [w]
    push_cast
    field_simp
  rw [heq] at hfrac
  have hcost := mul_le_mul_of_nonneg_left hfrac hc
  push_cast at hh
  exact hcost.trans_lt hh

end Paper.TotalDomination.PathPowerGap
#print axioms Paper.TotalDomination.PathPowerGap.window_lower_bound
