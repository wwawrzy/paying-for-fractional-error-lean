import Paper.TotalDomination.InitialSelection

namespace Paper.TotalDomination.InitialSelection
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

def hits (v : V) : ℕ := (G.neighborFinset v ∩ selected G d).card
def boundaryCost (v : V) : ℕ := d - hits G d v
def candidates : Finset V := Finset.univ.filter (fun v => 0 < boundaryCost G d v)

theorem touches_degree {v : V} (hv : (G.neighborFinset v ∩ selected G d).Nonempty) :
    G.degree v = d := by
  obtain ⟨u,hu⟩ := hv
  have hvc : v ∈ covered G (selected G d) := Finset.mem_biUnion.mpr
    ⟨u,(Finset.mem_inter.mp hu).2,(mem_closed G v u).mpr
      (Or.inr (((G.mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1).symm))⟩
  exact distance_two_degree G d (subset_covered G _ hvc)

theorem hits_le (v : V) : hits G d v ≤ d := by
  by_cases hz : hits G d v = 0
  · omega
  have hh := touches_degree G d (Finset.card_pos.mp (Nat.pos_of_ne_zero hz))
  have hs := Finset.card_le_card (Finset.inter_subset_left (s₂ := selected G d) (s₁ := G.neighborFinset v))
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,hh] using hs

theorem cost_identity (v : V) : boundaryCost G d v + hits G d v = d :=
  Nat.sub_add_cancel (hits_le G d v)

theorem candidate_bounds {v : V} (hv : v ∈ candidates G d) :
    1 ≤ boundaryCost G d v ∧ boundaryCost G d v ≤ d := by
  exact ⟨(Finset.mem_filter.mp hv).2,Nat.sub_le _ _⟩

theorem remaining_neighbors_candidates (hd : 0 < d) {r v : V}
    (hr : r ∈ remaining G d) (hv : G.Adj r v) : v ∈ candidates G d := by
  have hc : 0 < boundaryCost G d v := by
    by_contra hn
    have hz : boundaryCost G d v = 0 := Nat.eq_zero_of_not_pos hn
    have hh : hits G d v = d := by have h := cost_identity G d v;omega
    have hdeg := touches_degree G d (Finset.card_pos.mp (by change 0 < hits G d v;omega))
    have heq : G.neighborFinset v ∩ selected G d = G.neighborFinset v := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      simpa only [SimpleGraph.card_neighborFinset_eq_degree,hdeg] using hh.ge
    have hrF : r ∈ selected G d := (Finset.mem_inter.mp (heq.symm ▸
      (G.mem_neighborFinset v r).mpr hv.symm)).2
    exact (Finset.mem_sdiff.mp hr).2 hrF
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩

theorem remaining_subset_candidates (hd : 0 < d)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) : remaining G d ⊆ candidates G d := by
  intro v hv
  obtain ⟨r,hr,ha⟩ := remaining_neighbor G d hfree hv
  exact remaining_neighbors_candidates G d hd hr ha.symm

theorem demand_rows (hd : 0 < d) {r : V} (hr : r ∈ remaining G d) :
    G.neighborFinset r ∩ candidates G d = G.neighborFinset r := by
  apply Finset.inter_eq_left.mpr
  intro v hv
  exact remaining_neighbors_candidates G d hd hr ((G.mem_neighborFinset r v).mp hv)

end Paper.TotalDomination.InitialSelection
#print axioms Paper.TotalDomination.InitialSelection.cost_identity
#print axioms Paper.TotalDomination.InitialSelection.remaining_neighbors_candidates
#print axioms Paper.TotalDomination.InitialSelection.remaining_subset_candidates
