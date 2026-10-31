import Paper.TotalDomination.IntegerSetup

namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def linkedHits (v : V) : ℕ := (G.neighborFinset v ∩ linked G d).card

theorem residual_linked_disjoint : Disjoint (residual G (I G d x identifier hfree)) (linked G d) := by
  apply Finset.disjoint_left.mpr
  intro v hv hl
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hl

theorem linked_neighbor_degree {v : V}
    (hv : (G.neighborFinset v ∩ linked G d).Nonempty) : G.degree v = d := by
  obtain ⟨r,hr⟩ := hv
  have hrL := (Finset.mem_inter.mp hr).2
  obtain ⟨f,hf,ha⟩ := (mem_neighbors G).mp (Finset.mem_inter.mp hrL).2
  have hrc : r ∈ covered G (F G d) :=
    Finset.mem_biUnion.mpr ⟨f,hf,(mem_closed G r f).mpr (Or.inr ha.symm)⟩
  apply InitialSelection.distance_two_degree G d
  exact Finset.mem_biUnion.mpr ⟨r,hrc,(mem_closed G v r).mpr
    (Or.inr (((G.mem_neighborFinset v r).mp (Finset.mem_inter.mp hr).1).symm))⟩

theorem hits_plus_linked_le_cost {v : V} (hv : G.degree v = d) :
    hits G (I G d x identifier hfree) v + linkedHits G d v ≤ c G d v := by
  rw [cost_eq_remaining G d hv]
  have hd : Disjoint (G.neighborFinset v ∩ residual G (I G d x identifier hfree))
      (G.neighborFinset v ∩ linked G d) := by
    exact (residual_linked_disjoint G d x identifier hfree).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hs : (G.neighborFinset v ∩ residual G (I G d x identifier hfree)) ∪
      (G.neighborFinset v ∩ linked G d) ⊆ G.neighborFinset v ∩ Z G d := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hr).1,
        residual_subset_remaining G d x identifier hfree (Finset.mem_inter.mp hr).2⟩
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hr).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hr).2).1⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd] at hc
  exact hc

theorem linked_neighbors_other (hd : 0 < d) {v : V}
    (hv : (G.neighborFinset v ∩ linked G d).Nonempty) : v ∈ other G (I G d x identifier hfree) := by
  have hdeg := linked_neighbor_degree G d hv
  obtain ⟨r,hr⟩ := hv
  have hrZ := (Finset.mem_inter.mp (Finset.mem_inter.mp hr).2).1
  have hK := InitialSelection.remaining_neighbors_candidates G d hd hrZ
    (((G.mem_neighborFinset v r).mp (Finset.mem_inter.mp hr).1).symm)
  have hnW : v ∉ first G (I G d x identifier hfree) := by
    intro hw
    have hde := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
    omega
  have hlp : 0 < linkedHits G d v := Finset.card_pos.mpr ⟨r,hr⟩
  have hh := hits_plus_linked_le_cost G d x identifier hfree hdeg
  have hc : c G d v ≤ d := Nat.sub_le _ _
  have hnH : v ∉ high G (I G d x identifier hfree) := by
    intro hH
    have hcut := (Finset.mem_filter.mp hH).2
    change d ≤ hits G (I G d x identifier hfree) v at hcut
    omega
  exact Finset.mem_sdiff.mpr ⟨hK,fun h => (Finset.mem_union.mp h).elim hnW hnH⟩

theorem linked_penalty_bound (hd : 0 < d)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x) :
    ((linked G d).card : ℝ) ≤ penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
  classical
  have hcov : ((linked G d).card : ℝ) ≤ ∑ v, (linkedHits G d v : ℝ)*x v := by
    change ((linked G d).card : ℝ) ≤ ∑ v, ((G.neighborFinset v ∩ linked G d).card : ℝ)*x v
    rw [← InitialSelection.open_incidence_sum]
    calc
      _ = ∑ _r ∈ linked G d, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun r hr => hx.2 r (Finset.mem_inter.mp hr).1
  have heq : (∑ v ∈ other G (I G d x identifier hfree), (linkedHits G d v : ℝ)*x v) =
      ∑ v, (linkedHits G d v : ℝ)*x v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hz : linkedHits G d v = 0 := by
      by_contra hn
      have hp : (G.neighborFinset v ∩ linked G d).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
      exact hv (linked_neighbors_other G d x identifier hfree hd hp)
    simp only [hz,Nat.cast_zero,zero_mul]
  rw [← heq] at hcov
  apply hcov.trans
  apply Finset.sum_le_sum
  intro v hv
  by_cases hz : linkedHits G d v = 0
  · simp only [hz,Nat.cast_zero,zero_mul]
    apply mul_nonneg _ (hx.1 v)
    have hh := other_cost_bound G d x identifier hfree hv
    exact sub_nonneg.mpr (by exact_mod_cast hh)
  · have hp : (G.neighborFinset v ∩ linked G d).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
    have hh := hits_plus_linked_le_cost G d x identifier hfree (linked_neighbor_degree G d hp)
    have hhR : (hits G (I G d x identifier hfree) v : ℝ)+(linkedHits G d v : ℝ) ≤ c G d v := by
      exact_mod_cast hh
    exact mul_le_mul_of_nonneg_right (by linarith) (hx.1 v)

end Paper.TotalDomination.IntegerSetup

#print axioms Paper.TotalDomination.IntegerSetup.linked_penalty_bound
