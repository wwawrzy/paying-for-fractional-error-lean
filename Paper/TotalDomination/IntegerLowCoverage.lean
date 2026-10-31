import Paper.TotalDomination.IntegerLinkedPenalty

namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem selected_hits_zero {v : V} (hv : v ∈ F G d) : hits G (I G d x identifier hfree) v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hrR := (Finset.mem_inter.mp hr).2
  have hrD := (Finset.mem_sdiff.mp hrR).1
  have hrZ := (Finset.mem_sdiff.mp hrD).1
  have hrN : r ∈ neighbors G (F G d) := (mem_neighbors G).mpr
    ⟨v,hv,((G.mem_neighborFinset v r).mp (Finset.mem_inter.mp hr).1).symm⟩
  exact (Finset.mem_sdiff.mp hrD).2 (Finset.mem_inter.mpr ⟨hrZ,hrN⟩)

theorem equal_cost_positive_linked {v : V}
    (hv : v ∈ other G (I G d x identifier hfree))
    (heq : c G d v = hits G (I G d x identifier hfree) v)
    (hp : 0 < hits G (I G d x identifier hfree) v) : v ∈ linked G d := by
  have hlt := other_hits_lt G d x identifier hfree hv
  have hc := InitialSelection.cost_identity G d v
  have hpos : 0 < InitialSelection.hits G d v := by change c G d v + InitialSelection.hits G d v = d at hc;omega
  obtain ⟨f,hf⟩ := Finset.card_pos.mp hpos
  have hn : v ∈ neighbors G (F G d) := (mem_neighbors G).mpr
    ⟨f,(Finset.mem_inter.mp hf).2,(G.mem_neighborFinset v f).mp (Finset.mem_inter.mp hf).1⟩
  have hnF : v ∉ F G d := by
    intro hF
    have hz := selected_hits_zero G d x identifier hfree hF
    omega
  exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnF⟩,hn⟩

theorem pointwise_low (hd : 0 < d) (hx : ∀ v, 0 ≤ x v) (hcap : ∀ v, x v ≤ 1)
    {v : V} (hv : v ∈ other G (I G d x identifier hfree)) :
    (hits G (I G d x identifier hfree) v : ℝ)*x v ≤
      ((d:ℝ)-1)*((c G d v : ℝ)-(hits G (I G d x identifier hfree) v : ℝ))*x v +
      (if v ∈ linked G d then (d:ℝ)-1 else 0) := by
  classical
  have hle := other_cost_bound G d x identifier hfree hv
  have hlt := other_hits_lt G d x identifier hfree hv
  have hltR : (hits G (I G d x identifier hfree) v : ℝ) ≤ (d:ℝ)-1 := by
    have h : hits G (I G d x identifier hfree) v + 1 ≤ d := hlt
    have h' : (hits G (I G d x identifier hfree) v : ℝ)+1 ≤ d := by exact_mod_cast h
    linarith
  have hdR : 0 ≤ (d:ℝ)-1 := by
    have h : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  by_cases heq : c G d v = hits G (I G d x identifier hfree) v
  · rw [heq,sub_self,mul_zero,zero_mul,zero_add]
    by_cases hp : 0 < hits G (I G d x identifier hfree) v
    · rw [if_pos (equal_cost_positive_linked G d x identifier hfree hv heq hp)]
      exact (mul_le_mul_of_nonneg_right hltR (hx v)).trans (mul_le_of_le_one_right hdR (hcap v))
    · have hz : hits G (I G d x identifier hfree) v = 0 := Nat.eq_zero_of_not_pos hp
      simp only [hz,Nat.cast_zero,zero_mul]
      split_ifs <;> positivity
  · have hgap : 1 ≤ (c G d v : ℝ)-(hits G (I G d x identifier hfree) v : ℝ) := by
      have h : hits G (I G d x identifier hfree) v + 1 ≤ c G d v := by omega
      have h' : (hits G (I G d x identifier hfree) v : ℝ)+1 ≤ c G d v := by exact_mod_cast h
      linarith
    have hcoef := mul_le_mul_of_nonneg_left hgap hdR
    have hprod := mul_le_mul_of_nonneg_right (hltR.trans (by simpa only [mul_one] using hcoef)) (hx v)
    split_ifs <;> nlinarith only [hprod,hdR]

theorem low_coverage_bound (hd : 0 < d)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) :
    (∑ v ∈ other G (I G d x identifier hfree), (hits G (I G d x identifier hfree) v : ℝ)*x v) ≤
      2*((d:ℝ)-1)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
  classical
  let O := other G (I G d x identifier hfree)
  let D : ℝ := (d:ℝ)-1
  have hD : 0 ≤ D := by
    have h : (1:ℝ) ≤ d := by exact_mod_cast hd
    dsimp [D];linarith
  have hsum := Finset.sum_le_sum (fun v hv => pointwise_low G d x identifier hfree hd hx.1 hcap hv)
  change (∑ v ∈ O, (hits G (I G d x identifier hfree) v : ℝ)*x v) ≤
    ∑ v ∈ O, (D*((c G d v : ℝ)-(hits G (I G d x identifier hfree) v : ℝ))*x v +
      (if v ∈ linked G d then D else 0)) at hsum
  rw [Finset.sum_add_distrib] at hsum
  have heq : (∑ v ∈ O, D*((c G d v : ℝ)-(hits G (I G d x identifier hfree) v : ℝ))*x v) =
      D*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
    rw [penalty,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [I,input]
    ring
  rw [heq] at hsum
  have hind : (∑ v ∈ O, if v ∈ linked G d then D else 0) ≤ D*(linked G d).card := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hsub : O.filter (fun v => v ∈ linked G d) ⊆ linked G d := by
      intro v hv;exact (Finset.mem_filter.mp hv).2
    have hc : ((O.filter (fun v => v ∈ linked G d)).card : ℝ) ≤ (linked G d).card := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith only [mul_le_mul_of_nonneg_left hc hD]
  have hp := mul_le_mul_of_nonneg_left (linked_penalty_bound G d x identifier hfree hd hx) hD
  change (∑ v ∈ O, (hits G (I G d x identifier hfree) v : ℝ)*x v) ≤
    2*D*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ))
  nlinarith only [hsum,hind,hp]

theorem last_neighbors_other (hd : 0 < d) {r v : V}
    (hr : r ∈ last G (I G d x identifier hfree)) (ha : G.Adj r v) :
    v ∈ other G (I G d x identifier hfree) := by
  have hrR := (Finset.mem_sdiff.mp hr).1
  have hrZ := residual_subset_remaining G d x identifier hfree hrR
  have hK := InitialSelection.remaining_neighbors_candidates G d hd hrZ ha
  have hnW : v ∉ first G (I G d x identifier hfree) := by
    intro hw
    exact (Finset.mem_sdiff.mp hrR).2 ((mem_neighbors G).mpr ⟨v,hw,ha⟩)
  have hnH : v ∉ high G (I G d x identifier hfree) := by
    intro hh
    exact (Finset.mem_sdiff.mp hr).2 (Finset.mem_inter.mpr
      ⟨hrR,(mem_neighbors G).mpr ⟨v,hh,ha⟩⟩)
  exact Finset.mem_sdiff.mpr ⟨hK,fun h => (Finset.mem_union.mp h).elim hnW hnH⟩

theorem last_mass_bound (hd : 0 < d)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x) :
    ((last G (I G d x identifier hfree)).card : ℝ) ≤
      ∑ v ∈ other G (I G d x identifier hfree), (hits G (I G d x identifier hfree) v : ℝ)*x v := by
  classical
  let U := last G (I G d x identifier hfree)
  let O := other G (I G d x identifier hfree)
  have hsub : U ⊆ residual G (I G d x identifier hfree) := Finset.sdiff_subset
  have hcov : (U.card : ℝ) ≤ ∑ v, ((G.neighborFinset v ∩ U).card : ℝ)*x v := by
    rw [← InitialSelection.open_incidence_sum]
    calc
      _ = ∑ _r ∈ U, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun r hr =>
        hx.2 r (residual_subset_remaining G d x identifier hfree (hsub hr))
  have heq : (∑ v ∈ O, ((G.neighborFinset v ∩ U).card : ℝ)*x v) =
      ∑ v, ((G.neighborFinset v ∩ U).card : ℝ)*x v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hn
    have he : G.neighborFinset v ∩ U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hn (last_neighbors_other G d x identifier hfree hd (Finset.mem_inter.mp hr).2
        (((G.mem_neighborFinset v r).mp (Finset.mem_inter.mp hr).1).symm))
    simp only [he,Finset.card_empty,Nat.cast_zero,zero_mul]
  rw [← heq] at hcov
  apply hcov.trans
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (hx.1 v)
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hsub)

theorem last_penalty_bound (hd : 0 < d)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) :
    ((last G (I G d x identifier hfree)).card : ℝ) ≤
      2*((d:ℝ)-1)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) :=
  (last_mass_bound G d x identifier hfree hd hx).trans (low_coverage_bound G d x identifier hfree hd hx hcap)

/-- Full fv:total:setup for the actual integer-branch input, with no supplied R1--R3 premises. -/
theorem setup (hd : 0 < d)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) :
    (∀ v ∈ first G (I G d x identifier hfree) ∪ high G (I G d x identifier hfree), c G d v = d) ∧
    (∀ v ∈ other G (I G d x identifier hfree), hits G (I G d x identifier hfree) v ≤ c G d v) ∧
    (∀ v ∈ high G (I G d x identifier hfree), d < hits G (I G d x identifier hfree) v → x v ≤ 3/(2*(d:ℝ))) ∧
    covered G (WeightedBudget.defects G d) ⊆ demands G d ∧
    high G (I G d x identifier hfree) ⊆ demands G d ∧
    ((linked G d).card : ℝ) ≤ penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) ∧
    (∑ v ∈ other G (I G d x identifier hfree), (hits G (I G d x identifier hfree) v : ℝ)*x v) ≤
      2*((d:ℝ)-1)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) ∧
    ((last G (I G d x identifier hfree)).card : ℝ) ≤
      2*((d:ℝ)-1)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
  have hc := local_conditions G d x identifier hfree
  exact ⟨hc.1,hc.2.1,hc.2.2,near_defect_demands G d,high_subset_demands G d x identifier hfree,
    linked_penalty_bound G d x identifier hfree hd hx,low_coverage_bound G d x identifier hfree hd hx hcap,
    last_penalty_bound G d x identifier hfree hd hx hcap⟩

end Paper.TotalDomination.IntegerSetup

#print axioms Paper.TotalDomination.IntegerSetup.low_coverage_bound
#print axioms Paper.TotalDomination.IntegerSetup.last_penalty_bound

#print axioms Paper.TotalDomination.IntegerSetup.setup
