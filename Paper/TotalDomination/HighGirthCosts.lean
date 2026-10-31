import Paper.TotalDomination.HighGirthSelection

namespace Paper.TotalDomination.HighGirthSelection
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] 

def hits (v : V) : ℕ := (G.neighborFinset v ∩ selected G).card
def boundaryCost (v : V) : ℕ := 2 - hits G v
def candidates : Finset V := Finset.univ.filter (fun v => 0 < boundaryCost G v)

theorem touches_degree {v : V} (hv : (G.neighborFinset v ∩ selected G).Nonempty) :
    G.degree v ≤ 2 := by
  obtain ⟨u,hu⟩ := hv
  have hvc : v ∈ covered G (selected G) := Finset.mem_biUnion.mpr
    ⟨u,(Finset.mem_inter.mp hu).2,(mem_closed G v u).mpr
      (Or.inr (((G.mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1).symm))⟩
  exact distance_two_degree G (subset_covered G _ hvc)

theorem hits_le (v : V) : hits G v ≤ 2 := by
  by_cases hz : hits G v = 0
  · omega
  have hh := touches_degree G (Finset.card_pos.mp (Nat.pos_of_ne_zero hz))
  have hs := Finset.card_le_card (Finset.inter_subset_left (s₂ := selected G) (s₁ := G.neighborFinset v))
  have hle : hits G v ≤ G.degree v := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hs
  exact hle.trans hh

theorem cost_identity (v : V) : boundaryCost G v + hits G v = 2 :=
  Nat.sub_add_cancel (hits_le G v)

theorem candidate_bounds {v : V} (hv : v ∈ candidates G) :
    1 ≤ boundaryCost G v ∧ boundaryCost G v ≤ 2 := by
  exact ⟨(Finset.mem_filter.mp hv).2,Nat.sub_le _ _⟩

theorem remaining_neighbors_candidates  {r v : V}
    (hr : r ∈ remaining G) (hv : G.Adj r v) : v ∈ candidates G := by
  have hc : 0 < boundaryCost G v := by
    by_contra hn
    have hz : boundaryCost G v = 0 := Nat.eq_zero_of_not_pos hn
    have hh : hits G v = 2 := by have h := cost_identity G v;omega
    have hdeg := touches_degree G (Finset.card_pos.mp (by change 0 < hits G v;omega))
    have heq : G.neighborFinset v ∩ selected G = G.neighborFinset v := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      have hcard : (G.neighborFinset v).card ≤ 2 := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg
      exact hcard.trans hh.ge
    have hrF : r ∈ selected G := (Finset.mem_inter.mp (heq.symm ▸
      (G.mem_neighborFinset v r).mpr hv.symm)).2
    exact (Finset.mem_sdiff.mp hr).2 hrF
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩

theorem remaining_subset_candidates 
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) : remaining G ⊆ candidates G := by
  intro v hv
  obtain ⟨r,hr,ha⟩ := remaining_neighbor G hfree hv
  exact remaining_neighbors_candidates G hr ha.symm

theorem demand_rows  {r : V} (hr : r ∈ remaining G) :
    G.neighborFinset r ∩ candidates G = G.neighborFinset r := by
  apply Finset.inter_eq_left.mpr
  intro v hv
  exact remaining_neighbors_candidates G hr ((G.mem_neighborFinset r v).mp hv)

theorem near_cost {v : V} (hv : v ∈ covered G (branch G)) :
    boundaryCost G v = 2 := by
  have he : G.neighborFinset v ∩ selected G = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact Finset.disjoint_left.mp (near_defect_disjoint G hv)
      ((mem_closed G u v).mpr (Or.inr ((G.mem_neighborFinset v u).mp
        (Finset.mem_inter.mp hu).1))) (Finset.mem_inter.mp hu).2
  simp [boundaryCost,hits,he]

end Paper.TotalDomination.HighGirthSelection
#print axioms Paper.TotalDomination.HighGirthSelection.cost_identity
#print axioms Paper.TotalDomination.HighGirthSelection.remaining_neighbors_candidates
#print axioms Paper.TotalDomination.HighGirthSelection.remaining_subset_candidates
