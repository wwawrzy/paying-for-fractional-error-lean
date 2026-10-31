import Paper.Endpoints.Girth.NoncriticalGirth
import Paper.TotalDomination.GainParameters

namespace Paper.TotalDomination.PlanarGainArithmetic
open Noninteger

def target (g : ℕ) : ℚ := match g with
  | 7 => 2/15 | 8 => 1/6 | 9 => 5/21 | 10 => 1/4
  | 11 => 5/18 | 12 => 3/10 | 13 => 69/220 | _ => 0

def witness (g : ℕ) : ℚ := match g with
  | 7 => 7/50 | 8 => 9/50 | 9 => 1/4 | 10 => 13/50
  | 11 => 7/25 | 12 => 31/100 | 13 => 63/200 | _ => 0

def coefficient (g : ℕ) : ℚ := match g with
  | 7 => 8/3 | 8 => 5/2 | 9 => 7/3 | 10 => 9/4
  | 11 => 13/6 | 12 => 21/10 | 13 => 41/20 | _ => 0

theorem gap_ge_seven (g : ℕ) (hg : 7 ≤ g) :
    gap (NoncriticalGirth.density g) = 4/((g:ℝ)-2) := by
  have hgR : (7:ℝ) ≤ g := by exact_mod_cast hg
  have hp : (0:ℝ) < (g:ℝ)-2 := by linarith
  have hdelta : 0 < 4/((g:ℝ)-2) := div_pos (by norm_num) hp
  have hsmall : 4/((g:ℝ)-2) < 1 := (div_lt_iff₀ hp).mpr (by linarith)
  have htwo : 2*(NoncriticalGirth.density g:ℝ) = 2+4/((g:ℝ)-2) := by
    rw [NoncriticalGirth.density_cast]
    field_simp
    ring
  have hf : Nat.floor (2*(NoncriticalGirth.density g:ℝ)) = 2 :=
    (Nat.floor_eq_iff (by linarith : 0 ≤ 2*(NoncriticalGirth.density g:ℝ))).mpr
      ⟨by norm_num;linarith,by norm_num;linarith⟩
  simp only [gap,hf,Nat.cast_ofNat]
  linarith

theorem muMax_eq_theta (theta : ℝ) (hzero : 0 < theta) (hone : theta < 1)
    (hthird : theta ≤ 1/3) : muMax theta = theta := by
  apply le_antisymm (muMax_le_theta theta)
  apply (admissible_iff_le_muMax theta theta hzero hone hzero).mp
  refine ⟨le_rfl,?_⟩
  nlinarith

theorem finite_targets (g : ℕ) (hg : 7 ≤ g) (hhi : g ≤ 13) :
    (0:ℝ) < target g ∧ (target g:ℝ) < muMax (gap (NoncriticalGirth.density g)) ∧
      2*NoncriticalGirth.density g-target g = coefficient g := by
  have hg3 : 3 ≤ g := by omega
  have hnon := NoncriticalGirth.density_noninteger g (by omega) (by omega)
  obtain ⟨hzero,hone⟩ := gap_bounds (NoncriticalGirth.density g)
    (NoncriticalGirth.density_bounds g hg3).1
    (noninteger_real_of_rat _ hnon)
  have hrows : (0:ℝ) < target g ∧ (target g:ℝ) < witness g ∧
      (witness g:ℝ) ≤ gap (NoncriticalGirth.density g) ∧
      (1+(witness g:ℝ))*(1+(witness g:ℝ)-gap (NoncriticalGirth.density g)) ≤
        2*(1-gap (NoncriticalGirth.density g)) ∧
      2*NoncriticalGirth.density g-target g = coefficient g := by
    rw [gap_ge_seven g hg]
    interval_cases g <;> norm_num [target,witness,coefficient,NoncriticalGirth.density]
  have hm := (admissible_iff_le_muMax _ (witness g) hzero hone (hrows.1.trans hrows.2.1)).mp
    ⟨hrows.2.2.1,hrows.2.2.2.1⟩
  exact ⟨hrows.1,hrows.2.1.trans_le hm,hrows.2.2.2.2⟩

theorem five_max : 2*(NoncriticalGirth.density 5:ℝ)-muMax (gap (NoncriticalGirth.density 5)) = 3 := by
  have hg : gap (NoncriticalGirth.density 5) = 1/3 := by
    norm_num [gap,NoncriticalGirth.density]
  rw [hg,muMax_eq_theta (1/3) (by norm_num) (by norm_num) le_rfl]
  norm_num [NoncriticalGirth.density]

theorem large_max (g : ℕ) (hg : 14 ≤ g) :
    2*(NoncriticalGirth.density g:ℝ)-muMax (gap (NoncriticalGirth.density g)) = 2 := by
  have hg7 : 7 ≤ g := by omega
  have hgR : (14:ℝ) ≤ g := by exact_mod_cast hg
  have hp : (0:ℝ) < (g:ℝ)-2 := by linarith
  have hthird : 4/((g:ℝ)-2) ≤ 1/3 := (div_le_iff₀ hp).mpr (by linarith)
  have hzero : 0 < 4/((g:ℝ)-2) := div_pos (by norm_num) hp
  rw [gap_ge_seven g hg7,muMax_eq_theta _ hzero (by linarith) hthird,NoncriticalGirth.density_cast]
  field_simp
  ring

end Paper.TotalDomination.PlanarGainArithmetic
#print axioms Paper.TotalDomination.PlanarGainArithmetic.finite_targets
#print axioms Paper.TotalDomination.PlanarGainArithmetic.large_max
