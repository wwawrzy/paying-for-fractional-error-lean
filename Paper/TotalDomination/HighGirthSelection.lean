import Mathlib.Combinatorics.SimpleGraph.Paths
import Paper.Endpoints.Rounding.WeightedBudget
import Paper.Certificates.Counting.CoveringOptimum

/-! The degree-at-most-two exterior in fv:hg:t-budget. -/
namespace Paper.TotalDomination.HighGirthSelection
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] 

def branch : Finset V := Finset.univ.filter (fun v => 3 ≤ G.degree v)
def zone : Finset V := covered G (covered G (branch G))
def far : Finset V := Finset.univ \ zone G

def selected : Finset V := (far G).filter
  (fun v => (G.neighborFinset v ∩ far G).Nonempty)
def remaining : Finset V := Finset.univ \ selected G

theorem selected_subset_far : selected G ⊆ far G :=
  Finset.filter_subset _ _

theorem selected_neighbor {v : V} (hv : v ∈ selected G) :
    ∃ u ∈ selected G, G.Adj v u := by
  obtain ⟨hvfar,u,hu⟩ := Finset.mem_filter.mp hv
  have huv := (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1
  refine ⟨u,Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hu).2,?_⟩,huv⟩
  exact ⟨v,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv.symm,hvfar⟩⟩

theorem distance_two_degree {v : V}
    (hv : v ∈ covered G (covered G (selected G))) : G.degree v ≤ 2 := by
  by_contra hn
  have hvB : v ∈ branch G := by simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  obtain ⟨u,hu,hvu⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨f,hf,huf⟩ := Finset.mem_biUnion.mp hu
  have huN : u ∈ covered G (branch G) :=
    Finset.mem_biUnion.mpr ⟨v,hvB,(closed_symm G u v).mpr hvu⟩
  have hfzone : f ∈ zone G :=
    Finset.mem_biUnion.mpr ⟨u,huN,(closed_symm G f u).mpr huf⟩
  exact (Finset.mem_sdiff.mp (selected_subset_far G hf)).2 hfzone

theorem near_defect_disjoint {v : V} (hv : v ∈ covered G (branch G)) :
    Disjoint (closed G v) (selected G) :=
  by
  apply Finset.disjoint_left.mpr
  intro u hu hs
  exact (Finset.mem_sdiff.mp (selected_subset_far G hs)).2
    (Finset.mem_biUnion.mpr ⟨v,hv,hu⟩)

theorem near_defect_remaining : covered G (branch G) ⊆ remaining G := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
  intro hf
  exact Finset.disjoint_left.mp (near_defect_disjoint G hv) (self_mem_closed G v) hf

theorem remaining_neighbor (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    {v : V} (hv : v ∈ remaining G) :
    ∃ u ∈ remaining G, G.Adj v u := by
  by_cases hnear : v ∈ covered G (branch G)
  · obtain ⟨u,hu⟩ := hfree v
    have hadj := (G.mem_neighborFinset v u).mp hu
    refine ⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,hadj⟩
    intro huf
    exact Finset.disjoint_left.mp (near_defect_disjoint G hnear)
      ((mem_closed G u v).mpr (Or.inr hadj)) huf
  · by_cases hzone : v ∈ zone G
    · obtain ⟨u,hu,hvu⟩ := Finset.mem_biUnion.mp hzone
      refine ⟨u,near_defect_remaining G hu,?_⟩
      rcases (mem_closed G v u).mp hvu with heq | hadj
      · exact False.elim (hnear (heq ▸ hu))
      · exact hadj.symm
    · obtain ⟨u,hu⟩ := hfree v
      have hadj := (G.mem_neighborFinset v u).mp hu
      refine ⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,hadj⟩
      intro huf
      have hvfar : v ∈ far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hzone⟩
      have hvsel : v ∈ selected G := Finset.mem_filter.mpr
        ⟨hvfar,⟨u,Finset.mem_inter.mpr ⟨hu,selected_subset_far G huf⟩⟩⟩
      exact (Finset.mem_sdiff.mp hv).2 hvsel

theorem defects_nonempty (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (hZ : (remaining G).Nonempty) : (branch G).Nonempty := by
  by_contra hn
  have he : branch G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hfar : far G = Finset.univ := by
    simp [far,zone,he,covered]
  obtain ⟨v,hv⟩ := hZ
  apply (Finset.mem_sdiff.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨by simp [hfar],?_⟩
  simpa only [hfar,Finset.inter_univ] using hfree v

theorem zone_subset_remaining : zone G ⊆ remaining G := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
  intro hs
  exact (Finset.mem_sdiff.mp (selected_subset_far G hs)).2 hv

theorem near_walk {v : V} (hv : v ∈ covered G (branch G)) :
    ∃ b ∈ branch G, ∃ p : G.Walk v b,
      p.length ≤ 1 ∧ ∀ u ∈ p.support, u ∈ remaining G := by
  obtain ⟨b,hb,hvb⟩ := Finset.mem_biUnion.mp hv
  rcases (mem_closed G v b).mp hvb with heq | hadj
  · subst v
    refine ⟨b,hb,.nil,by simp,?_⟩
    intro u hu
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hu
    subst u
    exact near_defect_remaining G (subset_covered G _ hb)
  · refine ⟨b,hb,.cons hadj.symm .nil,by simp,?_⟩
    intro u hu
    simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
      List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    · exact near_defect_remaining G hv
    · exact near_defect_remaining G (subset_covered G _ hb)

theorem zone_walk {v : V} (hv : v ∈ zone G) :
    ∃ b ∈ branch G, ∃ p : G.Walk v b,
      p.length ≤ 2 ∧ ∀ u ∈ p.support, u ∈ remaining G := by
  obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨b,hb,p,hp,hs⟩ := near_walk G ha
  rcases (mem_closed G v a).mp hva with heq | hadj
  · subst v
    exact ⟨b,hb,p,by omega,hs⟩
  · refine ⟨b,hb,.cons hadj.symm p,?_,?_⟩
    · simp only [SimpleGraph.Walk.length_cons];omega
    · intro u hu
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact zone_subset_remaining G (Finset.mem_biUnion.mpr ⟨a,ha,hva⟩)
      · exact hs u hu

theorem remaining_walk (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    {v : V} (hv : v ∈ remaining G) :
    ∃ b ∈ branch G, ∃ p : G.Walk v b,
      p.length ≤ 3 ∧ ∀ u ∈ p.support, u ∈ remaining G := by
  by_cases hz : v ∈ zone G
  · obtain ⟨b,hb,p,hp,hs⟩ := zone_walk G hz
    exact ⟨b,hb,p,by omega,hs⟩
  · obtain ⟨u,hu⟩ := hfree v
    have ha := (G.mem_neighborFinset v u).mp hu
    have huz : u ∈ zone G := by
      by_contra hun
      have hvfar : v ∈ far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩
      have hufar : u ∈ far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hun⟩
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr
        ⟨hvfar,⟨u,Finset.mem_inter.mpr ⟨hu,hufar⟩⟩⟩)
    obtain ⟨b,hb,p,hp,hs⟩ := zone_walk G huz
    refine ⟨b,hb,.cons ha p,?_,?_⟩
    · simp only [SimpleGraph.Walk.length_cons];omega
    · intro u hu
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hv
      · exact hs u hu

theorem remaining_path (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    {v : V} (hv : v ∈ remaining G) :
    ∃ b ∈ branch G, ∃ p : G.Path v b,
      (p : G.Walk v b).length ≤ 3 ∧ ∀ u ∈ (p : G.Walk v b).support, u ∈ remaining G := by
  obtain ⟨b,hb,p,hp,hs⟩ := remaining_walk G hfree hv
  exact ⟨b,hb,p.toPath,(p.length_bypass_le).trans hp,
    fun u hu => hs u (p.support_toPath_subset hu)⟩

theorem near_walk_zone {v : V} (hv : v ∈ covered G (branch G)) :
    ∃ b ∈ branch G, ∃ p : G.Walk v b,
      p.length ≤ 1 ∧ ∀ u ∈ p.support, u ∈ zone G := by
  obtain ⟨b,hb,hvb⟩ := Finset.mem_biUnion.mp hv
  rcases (mem_closed G v b).mp hvb with heq | hadj
  · subst v
    refine ⟨b,hb,.nil,by simp,?_⟩
    intro u hu
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hu
    subst u
    exact subset_covered G (covered G (branch G)) (subset_covered G _ hb)
  · refine ⟨b,hb,.cons hadj.symm .nil,by simp,?_⟩
    intro u hu
    simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
      List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    · exact subset_covered G (covered G (branch G)) hv
    · exact subset_covered G (covered G (branch G)) (subset_covered G _ hb)

theorem zone_walk_zone {v : V} (hv : v ∈ zone G) :
    ∃ b ∈ branch G, ∃ p : G.Walk v b,
      p.length ≤ 2 ∧ ∀ u ∈ p.support, u ∈ zone G := by
  obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨b,hb,p,hp,hs⟩ := near_walk_zone G ha
  rcases (mem_closed G v a).mp hva with heq | hadj
  · subst v
    exact ⟨b,hb,p,by omega,hs⟩
  · refine ⟨b,hb,.cons hadj.symm p,?_,?_⟩
    · simp only [SimpleGraph.Walk.length_cons];omega
    · intro u hu
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact Finset.mem_biUnion.mpr ⟨a,ha,hva⟩
      · exact hs u hu

theorem remaining_path_zone (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    {v : V} (hv : v ∈ remaining G) :
    ∃ b ∈ branch G, ∃ p : G.Path v b,
      (p : G.Walk v b).length ≤ 3 ∧
      ∀ u ∈ (p : G.Walk v b).support, u ≠ v → u ∈ zone G := by
  have hw : ∃ b ∈ branch G, ∃ p : G.Walk v b,
      p.length ≤ 3 ∧ ∀ u ∈ p.support, u = v ∨ u ∈ zone G := by
    by_cases hz : v ∈ zone G
    · obtain ⟨b,hb,p,hp,hs⟩ := zone_walk_zone G hz
      exact ⟨b,hb,p,by omega,fun u hu => Or.inr (hs u hu)⟩
    · obtain ⟨u,hu⟩ := hfree v
      have ha := (G.mem_neighborFinset v u).mp hu
      have huz : u ∈ zone G := by
        by_contra hun
        have hvfar : v ∈ far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩
        have hufar : u ∈ far G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hun⟩
        exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr
          ⟨hvfar,⟨u,Finset.mem_inter.mpr ⟨hu,hufar⟩⟩⟩)
      obtain ⟨b,hb,p,hp,hs⟩ := zone_walk_zone G huz
      refine ⟨b,hb,.cons ha p,?_,?_⟩
      · simp only [SimpleGraph.Walk.length_cons]; omega
      · intro u hu
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact Or.inl rfl
        · exact Or.inr (hs u hu)
  obtain ⟨b,hb,p,hp,hs⟩ := hw
  refine ⟨b,hb,p.toPath,(p.length_bypass_le).trans hp,?_⟩
  intro u hu hne
  exact (hs u (p.support_toPath_subset hu)).resolve_left hne

end Paper.TotalDomination.HighGirthSelection
#print axioms Paper.TotalDomination.HighGirthSelection.selected_neighbor
#print axioms Paper.TotalDomination.HighGirthSelection.distance_two_degree
#print axioms Paper.TotalDomination.HighGirthSelection.near_defect_remaining
