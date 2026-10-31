import Mathlib

/-! Two different cross edges between disjoint paths produce a genuine short
cycle, including the case where one of the paths has length zero. -/
namespace Paper.HighGirthDisjointPaths
variable {V : Type} {G : SimpleGraph V} {x₁ x₂ y₁ y₂ : V}

theorem cross_cycle (p : G.Walk x₁ x₂) (q : G.Walk y₂ y₁)
    (hp : p.IsPath) (hq : q.IsPath) (hdisj : List.Disjoint p.support q.support)
    (ha : G.Adj y₁ x₁) (hb : G.Adj x₂ y₂)
    (hne : s(y₁,x₁) ≠ s(x₂,y₂)) :
    ∃ w : G.Walk y₁ y₁, w.IsCycle ∧ w.length = p.length + q.length + 2 := by
  classical
  let path := p.append (q.cons hb)
  have hpath : path.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp only [path, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
      List.tail_cons]
    refine List.nodup_append.mpr ⟨hp.support_nodup,hq.support_nodup,?_⟩
    intro a ha b hb heq
    subst b
    exact hdisj ha hb
  have hnotp : s(y₁,x₁) ∉ p.edges := by
    intro he
    exact hdisj (p.fst_mem_support_of_mem_edges he) q.end_mem_support
  have hnotq : s(y₁,x₁) ∉ q.edges := by
    intro he
    exact hdisj p.start_mem_support (q.snd_mem_support_of_mem_edges he)
  have hnot : s(y₁,x₁) ∉ path.edges := by
    simp only [path, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
      List.mem_append, List.mem_cons]
    tauto
  refine ⟨path.cons ha, (SimpleGraph.Walk.cons_isCycle_iff path ha).mpr ⟨hpath,hnot⟩, ?_⟩
  simp only [path, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append]
  omega

end Paper.HighGirthDisjointPaths
#print axioms Paper.HighGirthDisjointPaths.cross_cycle
