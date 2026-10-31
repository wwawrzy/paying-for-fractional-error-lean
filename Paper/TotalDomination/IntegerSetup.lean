import Paper.TotalDomination.InitialBudget
import Paper.TotalDomination.CostSaving

/-! The exact integer-branch input and local R1--R3 hypotheses. -/
namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

abbrev F := InitialSelection.selected G d
abbrev Z := InitialSelection.remaining G d
abbrev K := InitialSelection.candidates G d
abbrev c := InitialSelection.boundaryCost G d

def linked : Finset V := Z G d ∩ neighbors G (F G d)
def demands : Finset V := Z G d \ linked G d

def eligible : Finset V := (K G d).filter (fun v => d < G.degree v)

noncomputable def input (x : V → ℝ) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) : Input G where
  candidates := K G d
  demands := demands G d
  eligible := eligible G d
  eligible_subset := Finset.filter_subset _ _
  x := x
  threshold := 3/(2*(d:ℝ))
  cutoff := d
  identifier := identifier
  isolate_free := hfree

theorem neighbor_partition (v : V) :
    (G.neighborFinset v ∩ F G d).card + (G.neighborFinset v ∩ Z G d).card = G.degree v := by
  have heq : G.neighborFinset v ∩ Z G d = G.neighborFinset v \ F G d := by
    ext u
    simp [Z,InitialSelection.remaining]
  rw [heq,add_comm]
  exact Finset.card_sdiff_add_card_inter _ _

theorem cost_eq_remaining {v : V} (hv : G.degree v = d) :
    c G d v = (G.neighborFinset v ∩ Z G d).card := by
  have h := neighbor_partition G d v
  rw [hv] at h
  have hc := InitialSelection.cost_identity G d v
  change c G d v + (G.neighborFinset v ∩ F G d).card = d at hc
  omega

theorem near_defect_demands : covered G (WeightedBudget.defects G d) ⊆ demands G d := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨InitialSelection.near_defect_remaining G d hv,?_⟩
  intro hl
  obtain ⟨f,hf,ha⟩ := (mem_neighbors G).mp (Finset.mem_inter.mp hl).2
  exact Finset.disjoint_left.mp (InitialSelection.near_defect_disjoint G d hv)
    ((mem_closed G f v).mpr (Or.inr ha)) hf

variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable abbrev I := input G d x identifier hfree

theorem residual_subset_remaining : residual G (I G d x identifier hfree) ⊆ Z G d :=
  (Finset.sdiff_subset).trans Finset.sdiff_subset

theorem hits_le_remaining (v : V) : hits G (I G d x identifier hfree) v ≤
    (G.neighborFinset v ∩ Z G d).card :=
  Finset.card_le_card (Finset.inter_subset_inter_left (residual_subset_remaining G d x identifier hfree))

theorem high_no_selected_neighbors {v : V} (hv : v ∈ high G (I G d x identifier hfree)) :
    G.neighborFinset v ∩ F G d = ∅ := by
  by_contra hn
  have hne : (G.neighborFinset v ∩ F G d).Nonempty := Finset.nonempty_iff_ne_empty.mpr hn
  have hdeg := InitialSelection.touches_degree G d hne
  have hp := Finset.card_pos.mpr hne
  have hpart := neighbor_partition G d v
  have hhit := hits_le_remaining G d x identifier hfree v
  have hhigh := (Finset.mem_filter.mp hv).2
  change d ≤ hits G (I G d x identifier hfree) v at hhigh
  rw [hdeg] at hpart
  omega

theorem high_full_cost {v : V} (hv : v ∈ high G (I G d x identifier hfree)) : c G d v = d := by
  have he := high_no_selected_neighbors G d x identifier hfree hv
  simp only [c,InitialSelection.boundaryCost,InitialSelection.hits,he,Finset.card_empty,Nat.sub_zero]

theorem high_subset_demands : high G (I G d x identifier hfree) ⊆ demands G d := by
  intro v hv
  have he := high_no_selected_neighbors G d x identifier hfree hv
  have hnot : v ∉ neighbors G (F G d) := by
    intro hn
    obtain ⟨f,hf,ha⟩ := (mem_neighbors G).mp hn
    have hm : f ∈ G.neighborFinset v ∩ F G d :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v f).mpr ha,hf⟩
    simpa only [he,Finset.notMem_empty] using hm
  have hnF : v ∉ F G d := by
    intro hf
    obtain ⟨u,hu,ha⟩ := InitialSelection.selected_neighbor G d hf
    exact hnot ((mem_neighbors G).mpr ⟨u,hu,ha⟩)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnF⟩,
    fun hl => hnot (Finset.mem_inter.mp hl).2⟩

theorem first_full_cost {v : V} (hv : v ∈ first G (I G d x identifier hfree)) : c G d v = d := by
  have hel := (Finset.mem_filter.mp hv).1
  have hdeg := (Finset.mem_filter.mp hel).2
  have hempty : G.neighborFinset v ∩ F G d = ∅ := by
    by_contra hn
    have he := InitialSelection.touches_degree G d (Finset.nonempty_iff_ne_empty.mpr hn)
    omega
  simp only [c,InitialSelection.boundaryCost,InitialSelection.hits,hempty,Finset.card_empty,Nat.sub_zero]

theorem other_hits_lt {v : V} (hv : v ∈ other G (I G d x identifier hfree)) :
    hits G (I G d x identifier hfree) v < d := by
  have hK := (Finset.mem_sdiff.mp hv).1
  have hn := (Finset.mem_sdiff.mp hv).2
  have hnW : v ∉ first G (I G d x identifier hfree) := fun h => hn (Finset.mem_union_left _ h)
  have hnH : v ∉ high G (I G d x identifier hfree) := fun h => hn (Finset.mem_union_right _ h)
  by_contra hlt
  apply hnH
  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hK,hnW⟩,Nat.le_of_not_gt hlt⟩

theorem other_cost_bound {v : V} (hv : v ∈ other G (I G d x identifier hfree)) :
    hits G (I G d x identifier hfree) v ≤ c G d v := by
  by_cases hz : G.neighborFinset v ∩ F G d = ∅
  · have hc : c G d v = d := by
      simp only [c,InitialSelection.boundaryCost,InitialSelection.hits,hz,Finset.card_empty,Nat.sub_zero]
    rw [hc]
    exact (other_hits_lt G d x identifier hfree hv).le
  · have hdg := InitialSelection.touches_degree G d (Finset.nonempty_iff_ne_empty.mpr hz)
    rw [cost_eq_remaining G d hdg]
    exact hits_le_remaining G d x identifier hfree v

theorem positive_excess_small {v : V} (hv : v ∈ high G (I G d x identifier hfree))
    (he : d < hits G (I G d x identifier hfree) v) :
    x v ≤ 3/(2*(d:ℝ)) := by
  have hK := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hnW := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
  have hcard : hits G (I G d x identifier hfree) v ≤ G.degree v := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (G.card_neighborFinset_eq_degree v)
  have hel : v ∈ eligible G d := Finset.mem_filter.mpr ⟨hK,lt_of_lt_of_le he hcard⟩
  by_contra hlt
  apply hnW
  exact Finset.mem_filter.mpr ⟨hel,lt_of_not_ge hlt⟩

theorem local_conditions :
    (∀ v ∈ first G (I G d x identifier hfree) ∪ high G (I G d x identifier hfree), c G d v = d) ∧
    (∀ v ∈ other G (I G d x identifier hfree), hits G (I G d x identifier hfree) v ≤ c G d v) ∧
    (∀ v ∈ high G (I G d x identifier hfree), d < hits G (I G d x identifier hfree) v → x v ≤ 3/(2*(d:ℝ))) := by
  refine ⟨?_,fun _ hv => other_cost_bound G d x identifier hfree hv,
    fun _ hv he => positive_excess_small G d x identifier hfree hv he⟩
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact first_full_cost G d x identifier hfree hv
  · exact high_full_cost G d x identifier hfree hv

end Paper.TotalDomination.IntegerSetup
#print axioms Paper.TotalDomination.IntegerSetup.local_conditions
#print axioms Paper.TotalDomination.IntegerSetup.high_subset_demands
