import Paper.TotalDomination.IntegerCountGeometry
import Paper.TotalDomination.OversupplyMass

namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem outside_zero_mass
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x) :
    (∑ v ∈ outsideZero G d x identifier hfree, x v) ≤
      (first G (I G d x identifier hfree)).card+oversupply G (I G d x identifier hfree) := by
  have h := mass_le_card_add_oversupply G (I G d x identifier hfree)
    (first G (I G d x identifier hfree) ∩ residual G (I G d x identifier hfree))
    (outsideZero G d x identifier hfree) Finset.inter_subset_right Finset.inter_subset_right hx.1
    (fun r hr => hx.2 r (Finset.mem_sdiff.mp hr).1)
  have hc : ((first G (I G d x identifier hfree) ∩ residual G (I G d x identifier hfree)).card : ℝ) ≤
      (first G (I G d x identifier hfree)).card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  change (∑ v ∈ outsideZero G d x identifier hfree, x v) ≤ _ at h
  linarith

theorem outside_mass
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) :
    (∑ v ∈ outside G d x identifier hfree, x v) ≤
      (first G (I G d x identifier hfree)).card+oversupply G (I G d x identifier hfree)+
      (outsideOne G d x identifier hfree).card := by
  have hpart := Finset.sum_sdiff (s₁ := outsideZero G d x identifier hfree)
    (s₂ := outside G d x identifier hfree) (f := x) Finset.inter_subset_left
  have hc : (∑ v ∈ outsideOne G d x identifier hfree, x v) ≤ (outsideOne G d x identifier hfree).card := by
    calc
      _ ≤ ∑ _v ∈ outsideOne G d x identifier hfree, (1:ℝ) := Finset.sum_le_sum fun v _ => hcap v
      _ = _ := by simp
  have hz := outside_zero_mass G d x identifier hfree hx
  change (∑ v ∈ outsideOne G d x identifier hfree, x v)+(∑ v ∈ outsideZero G d x identifier hfree, x v) = _ at hpart
  linarith

theorem high_partial_weight (hd : 0 < d) (S : Finset V)
    (hS : S ⊆ high G (I G d x identifier hfree)) :
    (∑ v ∈ S, (hits G (I G d x identifier hfree) v : ℝ)*x v) ≤
      (d:ℝ)*(∑ v ∈ S, x v)+(3/(2*(d:ℝ)))*excess G (I G d x identifier hfree) ((d:ℝ)/2) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have ht : 0 ≤ 3/(2*(d:ℝ)) := by positivity
  have hp (v : V) (hv : v ∈ high G (I G d x identifier hfree)) :
      0 ≤ (hits G (I G d x identifier hfree) v : ℝ)-(d:ℝ) := by
    have hh := (Finset.mem_filter.mp hv).2
    change d ≤ hits G (I G d x identifier hfree) v at hh
    exact sub_nonneg.mpr (by exact_mod_cast hh)
  have hterm (v : V) (hv : v ∈ S) :
      (hits G (I G d x identifier hfree) v : ℝ)*x v ≤
      (d:ℝ)*x v+(3/(2*(d:ℝ)))*((hits G (I G d x identifier hfree) v : ℝ)-(d:ℝ)) := by
    by_cases he : d < hits G (I G d x identifier hfree) v
    · have hh := positive_excess_small G d x identifier hfree (hS hv) he
      have hh' := mul_le_mul_of_nonneg_left hh (hp v (hS hv))
      nlinarith only [hh']
    · have hh := (Finset.mem_filter.mp (hS hv)).2
      change d ≤ hits G (I G d x identifier hfree) v at hh
      have heq : hits G (I G d x identifier hfree) v = d := by omega
      simp only [heq,sub_self,mul_zero,add_zero]
      exact le_rfl
  have hsum := Finset.sum_le_sum hterm
  have he : (∑ v ∈ S, ((hits G (I G d x identifier hfree) v : ℝ)-(d:ℝ))) ≤
      excess G (I G d x identifier hfree) ((d:ℝ)/2) := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hS (fun v hv _ => hp v hv)
    simpa only [excess,show 2*((d:ℝ)/2) = d by ring] using hh
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left he ht
  linarith

theorem outside_weight (hd : 0 < d)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) :
    (∑ v ∈ outside G d x identifier hfree, (hits G (I G d x identifier hfree) v : ℝ)*x v) ≤
      (d:ℝ)*((first G (I G d x identifier hfree)).card+oversupply G (I G d x identifier hfree)+
        (outsideOne G d x identifier hfree).card)+
      (3/(2*(d:ℝ)))*excess G (I G d x identifier hfree) ((d:ℝ)/2) := by
  have h := high_partial_weight G d x identifier hfree hd (outside G d x identifier hfree) Finset.sdiff_subset
  have hm := mul_le_mul_of_nonneg_left (outside_mass G d x identifier hfree hx hcap) (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  linarith

theorem candidate_sum (f : V → ℝ) :
    (∑ v ∈ K G d, f v) = (∑ v ∈ first G (I G d x identifier hfree), f v)+
      (∑ v ∈ high G (I G d x identifier hfree), f v)+(∑ v ∈ other G (I G d x identifier hfree), f v) := by
  classical
  have hsub : first G (I G d x identifier hfree) ∪ high G (I G d x identifier hfree) ⊆ K G d := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.filter_subset _ _ (Finset.mem_filter.mp hv).1
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hh := Finset.sum_sdiff (s₁ := first G (I G d x identifier hfree) ∪ high G (I G d x identifier hfree))
    (s₂ := K G d) (f := f) hsub
  rw [Finset.sum_union (high_disjoint_first G (I G d x identifier hfree)).symm] at hh
  change (∑ v ∈ other G (I G d x identifier hfree), f v)+_ = _ at hh
  linarith

theorem served_low_mass (hd : 0 < d)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) :
    ((servedLow G d x identifier hfree).card : ℝ) ≤
      (G.interedges (core G d x identifier hfree) (servedLow G d x identifier hfree)).card +
      (∑ v ∈ outside G d x identifier hfree, (hits G (I G d x identifier hfree) v : ℝ)*x v)+
      (∑ v ∈ other G (I G d x identifier hfree), (hits G (I G d x identifier hfree) v : ℝ)*x v) := by
  classical
  let L := servedLow G d x identifier hfree
  let f : V → ℝ := fun v => ((G.neighborFinset v ∩ L).card : ℝ)*x v
  have hL : L ⊆ residual G (I G d x identifier hfree) := fun v hv =>
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
  have hcov : (L.card : ℝ) ≤ ∑ v, f v := by
    rw [show (∑ v, f v) = ∑ r ∈ L, ∑ v ∈ G.neighborFinset r, x v from
      (InitialSelection.open_incidence_sum G L x).symm]
    calc
      _ = ∑ _r ∈ L, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun r hr =>
        hx.2 r (residual_subset_remaining G d x identifier hfree (hL hr))
  have hfk : (∑ v ∈ K G d, f v) = ∑ v, f v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hn
    have he : G.neighborFinset v ∩ L = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hn (InitialSelection.remaining_neighbors_candidates G d hd
        (residual_subset_remaining G d x identifier hfree (hL (Finset.mem_inter.mp hr).2))
        (((G.mem_neighborFinset v r).mp (Finset.mem_inter.mp hr).1).symm))
    simp only [f,he,Finset.card_empty,Nat.cast_zero,zero_mul]
  have hfw : (∑ v ∈ first G (I G d x identifier hfree), f v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hc := Finset.card_le_card (Finset.inter_subset_inter_left hL (s := G.neighborFinset v))
    have hz := first_hits_zero G (I G d x identifier hfree) hv
    have he : (G.neighborFinset v ∩ L).card = 0 := by change _ ≤ hits G (I G d x identifier hfree) v at hc;omega
    simp only [f,he,Nat.cast_zero,zero_mul]
  have hp := candidate_sum G d x identifier hfree f
  have hH : (∑ v ∈ high G (I G d x identifier hfree), f v) =
      (∑ v ∈ core G d x identifier hfree, f v)+(∑ v ∈ outside G d x identifier hfree, f v) := by
    rw [← core_outside_union G d x identifier hfree]
    exact Finset.sum_union (block_disjoint G d x identifier hfree).1
  have hQ : (∑ v ∈ core G d x identifier hfree, f v) ≤
      (G.interedges (core G d x identifier hfree) L).card := by
    have hs : (∑ v ∈ core G d x identifier hfree, ((G.neighborFinset v ∩ L).card : ℝ)) =
        (G.interedges (core G d x identifier hfree) L).card := by
      rw [Incidence.card_interedges_eq_sum, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro v _
      congr 2
      ext r
      simp only [Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [← hs]
    exact Finset.sum_le_sum fun v _ => mul_le_of_le_one_right (Nat.cast_nonneg _) (hcap v)
  have hterm (v : V) : f v ≤ (hits G (I G d x identifier hfree) v : ℝ)*x v := by
    apply mul_le_mul_of_nonneg_right _ (hx.1 v)
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hL (s := G.neighborFinset v))
  have hA := Finset.sum_le_sum (s := outside G d x identifier hfree) (fun v _ => hterm v)
  have hO := Finset.sum_le_sum (s := other G (I G d x identifier hfree)) (fun v _ => hterm v)
  rw [hfw,hH,zero_add,hfk] at hp
  change (L.card : ℝ) ≤ _
  linarith

/-- Exact displayed oversupply inequality fv:total:oversupply. -/
theorem oversupply_bound (hd : 2 ≤ d)
    (hden : Incidence.InducedDensityBound G ((d:ℝ)/2))
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) :
    ((servedLow G d x identifier hfree).card : ℝ) ≤
      (d:ℝ)*((d:ℝ)+2)/2*(first G (I G d x identifier hfree)).card +
      (d:ℝ)^2/2*surplus G (I G d x identifier hfree) +
      ((d:ℝ)-1)*((d:ℝ)^2+2)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) +
      (d:ℝ)*oversupply G (I G d x identifier hfree) := by
  have hd0 : 0 < d := by omega
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  have hL := served_low_mass G d x identifier hfree hd0 hx hcap
  have hA := outside_weight G d x identifier hfree hd0 hx hcap
  have hO := low_coverage_bound G d x identifier hfree hd0 hx hcap
  have he := edge_budget_surplus G d x identifier hfree hden
  have hE : 0 ≤ excess G (I G d x identifier hfree) ((d:ℝ)/2) :=
    excess_nonneg G (I G d x identifier hfree) _ (by change 2*((d:ℝ)/2) ≤ (d:ℝ);linarith)
  have ht : 3/(2*(d:ℝ)) ≤ (d:ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))).mpr
    nlinarith
  have hq := mul_nonneg (show 0 ≤ (d:ℝ)/2-1 by linarith)
    (Nat.cast_nonneg (G.interedges (core G d x identifier hfree) (servedLow G d x identifier hfree)).card : (0:ℝ) ≤ _)
  have hε := mul_nonneg (sub_nonneg.mpr ht) hE
  have he' := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (d:ℝ)/2 by positivity)
  have hcombined : ((servedLow G d x identifier hfree).card : ℝ) ≤
      (d:ℝ)^2/2*(surplus G (I G d x identifier hfree)+(overlap G d x identifier hfree).card+
        (first G (I G d x identifier hfree)).card) +
      (d:ℝ)*((first G (I G d x identifier hfree)).card+oversupply G (I G d x identifier hfree))+
      2*((d:ℝ)-1)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
    nlinarith only [hL,hA,hO,he',hq,hε]
  have hI : ((overlap G d x identifier hfree).card : ℝ) ≤
      2*((d:ℝ)-1)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
    have hh : ((overlap G d x identifier hfree).card : ℝ) ≤ (last G (I G d x identifier hfree)).card := by
      exact_mod_cast overlap_le_last G d x identifier hfree
    exact hh.trans (last_penalty_bound G d x identifier hfree hd0 hx hcap)
  have hIp := mul_le_mul_of_nonneg_left hI (show (0:ℝ) ≤ (d:ℝ)^2/2 by positivity)
  nlinarith only [hcombined,hIp]

end Paper.TotalDomination.IntegerSetup

#print axioms Paper.TotalDomination.IntegerSetup.oversupply_bound
