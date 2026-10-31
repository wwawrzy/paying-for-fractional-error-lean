import Paper.TotalDomination.HighGirthSingleton
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Paper.TotalDomination.HighGirthSetup

noncomputable def isPathComponent
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Prop :=
  ∃ (a b : C) (p : C.toSimpleGraph.Walk a b), p.IsPath ∧
    (∀ z : C, z ∈ p.support) ∧ C.toSimpleGraph = p.toSubgraph.spanningCoe

theorem free_component_metric_access
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree K) (u : K) :
    (∃ v : K, v.val.val ∈ B G ∧ K.toSimpleGraph.dist u v ≤ 3) ∨
    (∃ v : K, v.val.val ∈ attachments G x identifier hfree ∧ K.toSimpleGraph.dist u v ≤ 2) := by
  classical
  have huK : u.val.val ∈ componentMembers G x identifier hfree K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,u.val.property,u.property⟩
  rcases free_short_access G x identifier hfree K hC u.val.val huK with
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

theorem path_component_is_tree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hpath : isPathComponent G x identifier hfree K) :
    K.toSimpleGraph.IsTree := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨a,b,p,hp,hcover,hgraph⟩ := hpath
  have heSet : K.toSimpleGraph.edgeSet = p.toSubgraph.edgeSet :=
    (congrArg SimpleGraph.edgeSet hgraph).trans p.toSubgraph.edgeSet_spanningCoe
  have he : K.toSimpleGraph.edgeFinset = p.edges.toFinset := by
    ext e
    rw [SimpleGraph.mem_edgeFinset,List.mem_toFinset,heSet]
    exact p.mem_edges_toSubgraph
  have hEcard : K.toSimpleGraph.edgeFinset.card = p.length := by
    rw [he,List.toFinset_card_of_nodup hp.isTrail.edges_nodup,SimpleGraph.Walk.length_edges]
  have hs : p.support.toFinset = Finset.univ := by
    ext z
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact hcover z
  have hVcard : Fintype.card K = p.length + 1 := by
    have hh := congrArg Finset.card hs
    simpa only [List.toFinset_card_of_nodup hp.support_nodup,SimpleGraph.Walk.length_support,Finset.card_univ] using hh.symm
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨K.connected_toSimpleGraph,?_⟩
  rw [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet,hEcard,Nat.card_eq_fintype_card]
  exact hVcard.symm

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem path_length_eq_distance
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hpath : isPathComponent G x identifier hfree K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath) :
    p.length = K.toSimpleGraph.dist a b := by
  obtain ⟨q,hq,hqlen⟩ := K.connected_toSimpleGraph.exists_path_of_dist a b
  have ht := path_component_is_tree G x identifier hfree K hpath
  have he : p = q := congrArg Subtype.val (ht.isAcyclic.path_unique ⟨p,hp⟩ ⟨q,hq⟩)
  exact he ▸ hqlen

theorem ordered_index_distance
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hpath : isPathComponent G x identifier hfree K)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ p.length) :
    K.toSimpleGraph.dist (p.getVert i) (p.getVert j) = j - i := by
  have hplen := path_length_eq_distance G x identifier hfree K hpath a b p hp
  have hsub : ((p.drop i).take (j - i)).IsSubwalk p :=
    (SimpleGraph.Walk.isSubwalk_take (p.drop i) (j - i)).trans (SimpleGraph.Walk.isSubwalk_drop p i)
  have hh := SimpleGraph.length_eq_dist_of_subwalk hplen hsub
  have hlen : ((p.drop i).take (j - i)).length = j - i := by
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length]
    exact Nat.min_eq_left (by omega)
  have hend : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [SimpleGraph.Walk.drop_getVert]
    have he : i + (j - i) = j := by omega
    rw [he]
  rw [hlen] at hh
  simpa only [hend] using hh.symm

end Paper.TotalDomination.HighGirthSetup
