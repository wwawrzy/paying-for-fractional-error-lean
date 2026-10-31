import Paper.Endpoints.Girth.HighGirthTwoBranchAttachments
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option maxHeartbeats 200000
namespace Paper.HighGirthMetricAccess

theorem free_component_metric_access
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hfree : Paper.HighGirthFreePaths.free G x K) (u : K) :
    (∃ v : K, v.val.val ∈ Paper.HighGirthTransformation.branches G ∧ K.toSimpleGraph.dist u v ≤ 2) ∨
    (∃ v : K, v.val.val ∈ Paper.HighGirthAttachments.vertices G x ∧ K.toSimpleGraph.dist u v ≤ 1) := by
  classical
  have huK : u.val.val ∈ Paper.HighGirthFreePaths.members G x K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,u.val.property,u.property⟩
  rcases Paper.HighGirthFreeAccess.free_short_access G x K hfree u.val.val huK with
    ⟨v,hv,hvU,huU,q,hq,hlen,hs⟩ | ⟨v,hv,hvU,huU,q,hq,hlen,hs⟩
  ·
    have hs' : ∀ z ∈ q.support, z ∈ K.supp := by
      intro z hz
      obtain ⟨hzU,hzC⟩ := (Finset.mem_filter.mp (hs z hz)).2
      exact hzC
    let r := q.induce K.supp hs'
    let v' : K := ⟨⟨v,hvU⟩,hs' _ q.end_mem_support⟩
    have hstart : (⟨⟨u.val.val,huU⟩,hs' _ q.start_mem_support⟩ : K) = u :=
      Subtype.ext (Subtype.ext rfl)
    let r' : K.toSimpleGraph.Walk u v' := r.copy hstart rfl
    have hrlen : r.length = q.length := by
      simpa only [SimpleGraph.Walk.length_map] using
        congrArg (fun w => w.length) (SimpleGraph.Walk.map_induce q hs')
    have hd : K.toSimpleGraph.dist u v' ≤ q.length := by
      have he : r'.length = q.length := (SimpleGraph.Walk.length_copy r hstart rfl).trans hrlen
      exact he ▸ SimpleGraph.dist_le r'
    exact Or.inl ⟨v',(Finset.mem_inter.mp hv).1,hd.trans hlen⟩
  ·
    have hs' : ∀ z ∈ q.support, z ∈ K.supp := by
      intro z hz
      obtain ⟨hzU,hzC⟩ := (Finset.mem_filter.mp (hs z hz)).2
      exact hzC
    let r := q.induce K.supp hs'
    let v' : K := ⟨⟨v,hvU⟩,hs' _ q.end_mem_support⟩
    have hstart : (⟨⟨u.val.val,huU⟩,hs' _ q.start_mem_support⟩ : K) = u :=
      Subtype.ext (Subtype.ext rfl)
    let r' : K.toSimpleGraph.Walk u v' := r.copy hstart rfl
    have hrlen : r.length = q.length := by
      simpa only [SimpleGraph.Walk.length_map] using
        congrArg (fun w => w.length) (SimpleGraph.Walk.map_induce q hs')
    have hd : K.toSimpleGraph.dist u v' ≤ q.length := by
      have he : r'.length = q.length := (SimpleGraph.Walk.length_copy r hstart rfl).trans hrlen
      exact he ▸ SimpleGraph.dist_le r'
    exact Or.inr ⟨v',(Finset.mem_inter.mp hv).1,hd.trans hlen⟩

end Paper.HighGirthMetricAccess

#print axioms Paper.HighGirthMetricAccess.free_component_metric_access
