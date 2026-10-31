import Paper.Optimality.LowerBounds.CycleForcedDomination
import Paper.Optimality.LowerBounds.PathPowerRamsey
import Paper.Optimality.LowerBounds.CycleRamseyLogStar

/-! Exact-order Ramsey obstruction for cycle domination. The rule is allowed
to depend on N and its radius is not fixed as N varies. All identifiers are
distinct members of 1,...,N. -/
namespace Paper.CycleRamseyCount

open SimpleGraph SevenFoundation PathPowerRamsey LocalCyclesRamseyReservoir
  DeterministicColorReductionLogStar

def selected {N : ℕ} (out : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun v => out v = true)

def addEnds {N : ℕ} (out : Fin N → Bool) (v : Fin N) : Bool :=
  if v.val = 0 ∨ v.val + 1 = N then true else out v

theorem addEnds_card (n : ℕ) (out : Fin (n + 3) → Bool) :
    (selected (addEnds out)).card ≤ (selected out).card + 2 := by
  have hs : selected (addEnds out) ⊆ selected out ∪
      {(⟨0, by omega⟩ : Fin (n + 3)), ⟨n + 2, by omega⟩} := by
    intro v hv
    have hh := (Finset.mem_filter.mp hv).2
    by_cases he : v.val = 0 ∨ v.val + 1 = n + 3
    · apply Finset.mem_union_right
      rcases he with he | he
      · exact Finset.mem_insert.mpr (Or.inl (Fin.ext he))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext (by
          dsimp only
          omega))))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa only [addEnds, if_neg he] using hh⟩)
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_two _))

theorem addEnds_agrees {N r : ℕ} (F : Rule r) (ids : Fin N → ℕ)
    (out : Fin N → Bool) (hr : 1 ≤ r) (h : Agrees F ids out) :
    Agrees F ids (addEnds out) := by
  intro v hl hu
  have he : ¬ (v.val = 0 ∨ v.val + 1 = N) := by omega
  simpa only [addEnds, if_neg he] using h v hl hu

theorem addEnds_dominates (n : ℕ) (out : Fin (n + 3) → Bool)
    (hd : dominates (cycleGraph (n + 3)) (selected out)) :
    dominates (PathPowerTreewidth.graph (n + 3) 1) (selected (addEnds out)) := by
  intro v
  by_cases he : v.val = 0 ∨ v.val + 1 = n + 3
  · exact subset_covered _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp only [addEnds, if_pos he]⟩)
  · obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp (hd v)
    refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hh := (Finset.mem_filter.mp hw).2
      unfold addEnds
      split_ifs
      · rfl
      · exact hh
    · apply (PathPowerCounting.mem_closed_iff _ _ _ _).mpr
      rcases (mem_closed _ _ _).mp hvw with hself | hadj
      · have hh := congrArg (fun z : Fin (n + 3) => z.val) hself
        omega
      · have hn : w ∈ (cycleGraph (n + 3)).neighborFinset v :=
          ((cycleGraph (n + 3)).mem_neighborFinset v w).mpr hadj.symm
        rw [cycleGraph_neighborFinset] at hn
        rcases Finset.mem_insert.mp hn with hp | hp
        · have hz : v ≠ 0 := by
            intro h
            apply he
            exact Or.inl (by simpa only [h, Fin.val_zero])
          rw [hp, Fin.val_sub_one_of_ne_zero hz]
          omega
        · have hp := Finset.mem_singleton.mp hp
          rw [hp, Fin.val_add_one_of_lt' (show v.val + 1 < n + 3 by omega)]
          omega

/-- The actual packing ledger forces a contradiction below ratio 5/4 once
N is four times the finite reservoir plus a fixed boundary allowance. -/
theorem ledger_contradiction (N r b rest d γ : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hq : ε < 1 / 4)
    (hlarge : 4 * ramseyBound 2 (2 * r) (8 * r + 8) + 32 ≤ N)
    (hcount : N = b * (8 * r + 8) + rest)
    (hrest : rest < ramseyBound 2 (2 * r) (8 * r + 8))
    (hsel : b * ((8 * r + 8) - (2 * r + 1)) ≤ d + 2)
    (hγ : (γ : ℝ) ≤ ((N : ℝ) + 2) / 3)
    (happrox : (d : ℝ) ≤ (1 + ε) * γ) : False := by
  have hlen : (8 * r + 8) - (2 * r + 1) = 6 * r + 7 := by omega
  rw [hlen] at hsel
  have hN : 32 ≤ N := by omega
  have hrestN : 4 * rest < N := by omega
  have hledger : 9 * N < 16 * (d + 2) := by
    nlinarith only [hcount, hrestN, hsel, Nat.zero_le b]
  have hledgerR : 9 * (N : ℝ) < 16 * ((d : ℝ) + 2) := by exact_mod_cast hledger
  have hNR : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hγnonneg : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
  have hupper : (d : ℝ) ≤ (5 / 4) * (((N : ℝ) + 2) / 3) := by
    calc
      _ ≤ (1 + ε) * γ := happrox
      _ ≤ (5 / 4) * γ := mul_le_mul_of_nonneg_right (by linarith) hγnonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hγ (by norm_num)
  linarith

theorem exact_order_obstruction (n r : ℕ) (hr : 1 ≤ r) (F : Rule r)
    (output : (Fin (n + 3) → ℕ) → Fin (n + 3) → Bool)
    (ε : ℝ) (hε : 0 < ε) (hq : ε < 1 / 4)
    (hguarantee : ∀ ids, Function.Injective ids →
      (∀ i, 1 ≤ ids i ∧ ids i ≤ n + 3) →
      Agrees F ids (output ids) ∧
      dominates (cycleGraph (n + 3)) (selected (output ids)) ∧
      ((selected (output ids)).card : ℝ) ≤
        (1 + ε) * (cycleGraph (n + 3)).dominationNumber) :
    n + 3 < 4 * ramseyBound 2 (2 * r) (8 * r + 8) + 32 := by
  by_contra hn
  obtain ⟨ids, hinj, hids, hpacking⟩ := packing (n + 3) 1 r (8 * r + 8) (by omega) F
  obtain ⟨ha, hd, hc⟩ := hguarantee ids hinj hids
  obtain ⟨b, rest, hncount, hrest, hsel⟩ := hpacking (addEnds (output ids))
    (addEnds_agrees F ids _ hr ha) (addEnds_dominates n _ hd)
  exact ledger_contradiction (n + 3) r b rest (selected (output ids)).card
    (cycleGraph (n + 3)).dominationNumber ε hε hq (by omega) hncount hrest
    (hsel.trans (addEnds_card n _))
    (CycleForcedDomination.cycle_dominationNumber_real_upper (n + 3)) hc

end Paper.CycleRamseyCount

#print axioms Paper.CycleRamseyCount.addEnds_dominates
#print axioms Paper.CycleRamseyCount.ledger_contradiction
#print axioms Paper.CycleRamseyCount.exact_order_obstruction
