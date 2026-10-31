import Mathlib.Combinatorics.SimpleGraph.Paths
import Paper.Endpoints.Rounding.WeightedBudget
import Paper.Certificates.Counting.CoveringOptimum

/-! The integer total-domination transformation: remove the isolated vertices
of the induced graph on the distance-two regular region. -/
namespace Paper.TotalDomination.InitialSelection
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

def selected : Finset V := (WeightedBudget.far G d).filter
  (fun v => (G.neighborFinset v ∩ WeightedBudget.far G d).Nonempty)
def remaining : Finset V := Finset.univ \ selected G d

theorem selected_subset_far : selected G d ⊆ WeightedBudget.far G d :=
  Finset.filter_subset _ _

theorem selected_neighbor {v : V} (hv : v ∈ selected G d) :
    ∃ u ∈ selected G d, G.Adj v u := by
  obtain ⟨hvfar,u,hu⟩ := Finset.mem_filter.mp hv
  have huv := (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1
  refine ⟨u,Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hu).2,?_⟩,huv⟩
  exact ⟨v,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv.symm,hvfar⟩⟩

theorem distance_two_degree {v : V}
    (hv : v ∈ covered G (covered G (selected G d))) : G.degree v = d := by
  by_contra hn
  have hvB : v ∈ WeightedBudget.defects G d := by simp [WeightedBudget.defects,hn]
  obtain ⟨u,hu,hvu⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨f,hf,huf⟩ := Finset.mem_biUnion.mp hu
  have huN : u ∈ covered G (WeightedBudget.defects G d) :=
    Finset.mem_biUnion.mpr ⟨v,hvB,(closed_symm G u v).mpr hvu⟩
  have hfzone : f ∈ WeightedBudget.zone G d :=
    Finset.mem_biUnion.mpr ⟨u,huN,(closed_symm G f u).mpr huf⟩
  exact (Finset.mem_sdiff.mp (selected_subset_far G d hf)).2 hfzone

theorem near_defect_disjoint {v : V} (hv : v ∈ covered G (WeightedBudget.defects G d)) :
    Disjoint (closed G v) (selected G d) :=
  (WeightedBudget.near_defect_no_far G d hv).mono_right (selected_subset_far G d)

theorem near_defect_remaining : covered G (WeightedBudget.defects G d) ⊆ remaining G d := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
  intro hf
  exact Finset.disjoint_left.mp (near_defect_disjoint G d hv) (self_mem_closed G v) hf

theorem remaining_neighbor (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    {v : V} (hv : v ∈ remaining G d) :
    ∃ u ∈ remaining G d, G.Adj v u := by
  by_cases hnear : v ∈ covered G (WeightedBudget.defects G d)
  · obtain ⟨u,hu⟩ := hfree v
    have hadj := (G.mem_neighborFinset v u).mp hu
    refine ⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,hadj⟩
    intro huf
    exact Finset.disjoint_left.mp (near_defect_disjoint G d hnear)
      ((mem_closed G u v).mpr (Or.inr hadj)) huf
  · by_cases hzone : v ∈ WeightedBudget.zone G d
    · obtain ⟨u,hu,hvu⟩ := Finset.mem_biUnion.mp hzone
      refine ⟨u,near_defect_remaining G d hu,?_⟩
      rcases (mem_closed G v u).mp hvu with heq | hadj
      · exact False.elim (hnear (heq ▸ hu))
      · exact hadj.symm
    · obtain ⟨u,hu⟩ := hfree v
      have hadj := (G.mem_neighborFinset v u).mp hu
      refine ⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,hadj⟩
      intro huf
      have hvfar : v ∈ WeightedBudget.far G d := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hzone⟩
      have hvsel : v ∈ selected G d := Finset.mem_filter.mpr
        ⟨hvfar,⟨u,Finset.mem_inter.mpr ⟨hu,selected_subset_far G d huf⟩⟩⟩
      exact (Finset.mem_sdiff.mp hv).2 hvsel

theorem defects_nonempty (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (hZ : (remaining G d).Nonempty) : (WeightedBudget.defects G d).Nonempty := by
  by_contra hn
  have he : WeightedBudget.defects G d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hfar : WeightedBudget.far G d = Finset.univ := by
    simp [WeightedBudget.far,WeightedBudget.zone,he,covered]
  obtain ⟨v,hv⟩ := hZ
  apply (Finset.mem_sdiff.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨by simp [hfar],?_⟩
  simpa only [hfar,Finset.inter_univ] using hfree v

theorem zone_subset_remaining : WeightedBudget.zone G d ⊆ remaining G d := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
  intro hs
  exact (Finset.mem_sdiff.mp (selected_subset_far G d hs)).2 hv

theorem near_walk {v : V} (hv : v ∈ covered G (WeightedBudget.defects G d)) :
    ∃ b ∈ WeightedBudget.defects G d, ∃ p : G.Walk v b,
      p.length ≤ 1 ∧ ∀ u ∈ p.support, u ∈ remaining G d := by
  obtain ⟨b,hb,hvb⟩ := Finset.mem_biUnion.mp hv
  rcases (mem_closed G v b).mp hvb with heq | hadj
  · subst v
    refine ⟨b,hb,.nil,by simp,?_⟩
    intro u hu
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hu
    subst u
    exact near_defect_remaining G d (subset_covered G _ hb)
  · refine ⟨b,hb,.cons hadj.symm .nil,by simp,?_⟩
    intro u hu
    simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
      List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    · exact near_defect_remaining G d hv
    · exact near_defect_remaining G d (subset_covered G _ hb)

theorem zone_walk {v : V} (hv : v ∈ WeightedBudget.zone G d) :
    ∃ b ∈ WeightedBudget.defects G d, ∃ p : G.Walk v b,
      p.length ≤ 2 ∧ ∀ u ∈ p.support, u ∈ remaining G d := by
  obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨b,hb,p,hp,hs⟩ := near_walk G d ha
  rcases (mem_closed G v a).mp hva with heq | hadj
  · subst v
    exact ⟨b,hb,p,by omega,hs⟩
  · refine ⟨b,hb,.cons hadj.symm p,?_,?_⟩
    · simp only [SimpleGraph.Walk.length_cons];omega
    · intro u hu
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact zone_subset_remaining G d (Finset.mem_biUnion.mpr ⟨a,ha,hva⟩)
      · exact hs u hu

theorem remaining_walk (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    {v : V} (hv : v ∈ remaining G d) :
    ∃ b ∈ WeightedBudget.defects G d, ∃ p : G.Walk v b,
      p.length ≤ 3 ∧ ∀ u ∈ p.support, u ∈ remaining G d := by
  by_cases hz : v ∈ WeightedBudget.zone G d
  · obtain ⟨b,hb,p,hp,hs⟩ := zone_walk G d hz
    exact ⟨b,hb,p,by omega,hs⟩
  · obtain ⟨u,hu⟩ := hfree v
    have ha := (G.mem_neighborFinset v u).mp hu
    have huz : u ∈ WeightedBudget.zone G d := by
      by_contra hun
      have hvfar : v ∈ WeightedBudget.far G d := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩
      have hufar : u ∈ WeightedBudget.far G d := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hun⟩
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr
        ⟨hvfar,⟨u,Finset.mem_inter.mpr ⟨hu,hufar⟩⟩⟩)
    obtain ⟨b,hb,p,hp,hs⟩ := zone_walk G d huz
    refine ⟨b,hb,.cons ha p,?_,?_⟩
    · simp only [SimpleGraph.Walk.length_cons];omega
    · intro u hu
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hv
      · exact hs u hu

theorem remaining_path (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    {v : V} (hv : v ∈ remaining G d) :
    ∃ b ∈ WeightedBudget.defects G d, ∃ p : G.Path v b,
      (p : G.Walk v b).length ≤ 3 ∧ ∀ u ∈ (p : G.Walk v b).support, u ∈ remaining G d := by
  obtain ⟨b,hb,p,hp,hs⟩ := remaining_walk G d hfree hv
  exact ⟨b,hb,p.toPath,(p.length_bypass_le).trans hp,
    fun u hu => hs u (p.support_toPath_subset hu)⟩

end Paper.TotalDomination.InitialSelection
#print axioms Paper.TotalDomination.InitialSelection.selected_neighbor
#print axioms Paper.TotalDomination.InitialSelection.distance_two_degree
#print axioms Paper.TotalDomination.InitialSelection.near_defect_remaining
