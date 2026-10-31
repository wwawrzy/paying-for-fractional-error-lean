import Paper.Optimality.LowerBounds.PathPowerRamsey

namespace Paper.PathPowerGap
open PathPowerTreewidth SevenFoundation
open LocalCyclesRamseyReservoir

/-- All finite losses, including the Ramsey remainder, fit into a strict gap. -/
theorem finite_margin (w L s R : ℕ) (hw : 1 ≤ w) (hs : s ≤ L)
    (c : ℝ) (hc : 0 ≤ c) (hgap : c * L < (w : ℝ) * ((L - s : ℕ) : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ b rest d : ℕ,
      w * N = b * L + rest → rest < R → b * (L - s) ≤ d → c * N < d := by
  let δ : ℝ := (w : ℝ) * ((L-s : ℕ) : ℝ) - c * L
  have hδ : 0 < δ := sub_pos.mpr hgap
  obtain ⟨K, hK⟩ := exists_nat_gt (c * R / δ)
  have hKR : c * R < δ * K := by
    have hh := (div_lt_iff₀ hδ).mp hK
    nlinarith
  let N := (K+1)*L+R+1
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro b rest d he hr hd
  have hb : K < b := by
    by_contra h
    have hm := Nat.mul_le_mul_right L (Nat.le_of_not_gt h)
    have hn := Nat.le_mul_of_pos_left N hw
    dsimp [N] at hn he
    nlinarith
  have he' : (w : ℝ) * N = b * L + rest := by exact_mod_cast he
  have hr' : (rest : ℝ) ≤ R := by exact_mod_cast hr.le
  have hd' : (b : ℝ) * ((L-s : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
  have hb' : (K : ℝ) ≤ b := by exact_mod_cast hb.le
  have hprod := mul_le_mul_of_nonneg_left hb' hδ.le
  have hrest := mul_le_mul_of_nonneg_left hr' hc
  dsimp [δ] at hprod hKR
  have hw' : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  rw [Nat.cast_sub hs] at hd' hprod hKR
  nlinarith

/-- The witness size is chosen before the identifier-sensitive rule at that size.
This result concerns window rules; the execution/locality bridge is separate. -/
theorem window_lower_bound (t r : ℕ) (c : ℝ) (hc : 0 ≤ c) (hct : c < 2*t+1) :
    ∃ n : ℕ, 0 < n ∧ ∀ F : PathPowerRamsey.Rule r,
      ∃ ids : Fin n → ℕ, Function.Injective ids ∧
        (∀ i, 1 ≤ ids i ∧ ids i ≤ n) ∧
        ∀ out : Fin n → Bool, PathPowerRamsey.Agrees F ids out →
          dominates (graph n t) (Finset.univ.filter (fun v => out v = true)) →
          c * (graph n t).dominationNumber < (Finset.univ.filter (fun v => out v = true)).card := by
  let w := 2*t+1
  let s := 2*r+1
  have hden : 0 < (w : ℝ)-c := by dsimp [w]; push_cast; linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (max (2*r+2*t+1 : ℝ) ((w : ℝ)*s/((w : ℝ)-c)))
  have hLnat : 2*r+2*t+1 ≤ L := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hL))
  have hs : s ≤ L := by dsimp [s]; omega
  have hdiv := (le_max_right (2*r+2*t+1 : ℝ) ((w : ℝ)*s/((w : ℝ)-c))).trans_lt hL
  have hmul := (div_lt_iff₀ hden).mp hdiv
  have hsub : ((L-s : ℕ) : ℝ) = (L : ℝ)-s := Nat.cast_sub hs
  have hgap : c*L < (w : ℝ)*(L-s : ℕ) := by rw [hsub]; nlinarith
  obtain ⟨N, hN, hmargin⟩ := finite_margin w L s (ramseyBound 2 (2*r) L)
    (by dsimp [w]; omega) hs c hc hgap
  refine ⟨w*N, Nat.mul_pos (by dsimp [w]; omega) hN, ?_⟩
  intro F
  obtain ⟨ids, hinj, hIDs, hpack⟩ := PathPowerRamsey.packing (w*N) t r L hLnat F
  refine ⟨ids, hinj, hIDs, ?_⟩
  intro out hagree hdom
  obtain ⟨b, rest, he, hr, hd⟩ := hpack out hagree hdom
  have hh := hmargin b rest _ he hr hd
  have hw : 0 < w := by dsimp [w]; omega
  have heq : (graph (w*N) t).dominationNumber = N := by
    rw [PathPowerDomination.dominationNumber_eq]
    change (w*N) ⌈/⌉ w = N
    apply Nat.le_antisymm
    · exact (ceilDiv_le_iff_le_mul hw).mpr le_rfl
    · have hbound : w*N ≤ w*((w*N) ⌈/⌉ w) := (ceilDiv_le_iff_le_mul hw).mp le_rfl
      exact Nat.le_of_mul_le_mul_left hbound hw
  simpa only [heq] using hh

end Paper.PathPowerGap
