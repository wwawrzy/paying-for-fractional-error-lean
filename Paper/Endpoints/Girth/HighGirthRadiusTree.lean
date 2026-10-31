import Paper.Endpoints.Girth.HighGirthVoronoi
import Paper.Preliminaries.ParentForest

/-! A genuine breadth-first spanning tree, used to turn bounded cluster
radius into short cycles when an additional internal edge is present. -/
namespace Paper.HighGirthRadiusTree
variable {V : Type} [LinearOrder V]
variable (G : SimpleGraph V) (hconn : G.Connected) (root : V)

noncomputable def predecessor (v : V) (hv : v ≠ root) : V :=
  Classical.choose (HighGirthVoronoi.exists_step G hconn v root hv)

theorem predecessor_spec (v : V) (hv : v ≠ root) :
    G.Adj v (predecessor G hconn root v hv) ∧
      G.dist (predecessor G hconn root v hv) root + 1 = G.dist v root :=
  Classical.choose_spec (HighGirthVoronoi.exists_step G hconn v root hv)

noncomputable def parent (v : V) : Option V :=
  if hv : v = root then none else some (predecessor G hconn root v hv)

theorem decrease (u v : V) (hp : parent G hconn root u = some v) :
    G.dist v root < G.dist u root := by
  classical
  unfold parent at hp
  split at hp
  · contradiction
  · rename_i hu
    have heq := Option.some.inj hp
    have hh := (predecessor_spec G hconn root u hu).2
    rw [heq] at hh
    omega

noncomputable def tree : SimpleGraph V :=
  ParentForest.graph (parent G hconn root) (fun v => G.dist v root) (decrease G hconn root)

theorem acyclic : (tree G hconn root).IsAcyclic := ParentForest.isAcyclic _ _ _

theorem subgraph : tree G hconn root ≤ G := by
  intro u v huv
  have hp : ∀ a b, parent G hconn root a = some b → G.Adj a b := by
    intro a b hab
    unfold parent at hab
    split at hab
    · contradiction
    · rename_i ha
      have heq := Option.some.inj hab
      simpa only [heq] using (predecessor_spec G hconn root a ha).1
  rcases huv with huv | hvu
  · exact hp u v huv
  · exact (hp v u hvu).symm

theorem root_walk (v : V) :
    ∃ p : (tree G hconn root).Walk v root, p.length = G.dist v root := by
  generalize hn : G.dist v root = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v = root
    · subst v
      exact ⟨.nil, by simpa using hn⟩
    · let u := predecessor G hconn root v hv
      have hu := (predecessor_spec G hconn root v hv).2
      obtain ⟨p,hp⟩ := ih (G.dist u root) (by dsimp [u]; omega) u rfl
      have hadj : (tree G hconn root).Adj v u := by
        exact Or.inl (by simp only [parent, dif_neg hv]; rfl)
      refine ⟨p.cons hadj, ?_⟩
      simp only [SimpleGraph.Walk.length_cons, hp]
      dsimp [u]
      exact hu.trans hn

theorem connected : (tree G hconn root).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨root,?_⟩
  intro v
  obtain ⟨p,_⟩ := root_walk G hconn root v
  exact ⟨p.reverse⟩

theorem short_walk (R : Nat) (hrad : ∀ v, G.dist v root ≤ R) (u v : V) :
    ∃ p : (tree G hconn root).Walk u v, p.length ≤ 2*R := by
  obtain ⟨p,hp⟩ := root_walk G hconn root u
  obtain ⟨q,hq⟩ := root_walk G hconn root v
  refine ⟨p.append q.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hp, hq]
  have hu := hrad u
  have hv := hrad v
  omega

set_option backward.isDefEq.respectTransparency false in
theorem short_cycle_of_extra_edge (R : Nat) (hrad : ∀ v, G.dist v root ≤ R)
    (u v : V) (hadj : G.Adj u v) (hextra : ¬ (tree G hconn root).Adj u v) :
    ∃ p : G.Walk u u, p.IsCycle ∧ p.length ≤ 2*R+1 := by
  classical
  obtain ⟨q,hq⟩ := short_walk G hconn root R hrad v u
  let p : G.Walk v u := q.mapLe (subgraph G hconn root)
  have hp : p.length ≤ 2*R := by simpa [p, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map] using hq
  have hnot : s(u,v) ∉ p.edges := by
    intro he
    have hmem : s(u,v) ∈ q.edges := by simpa only [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact hextra (((tree G hconn root).mem_edgeSet).mp (q.edges_subset_edgeSet hmem))
  have hpathnot : s(u,v) ∉ (p.toPath : G.Walk v u).edges :=
    fun he => hnot (p.edges_toPath_subset he)
  refine ⟨(p.toPath : G.Walk v u).cons hadj, p.toPath.cons_isCycle hadj hpathnot, ?_⟩
  have hh : (p.toPath : G.Walk v u).length ≤ p.length := p.length_bypass_le
  simp only [SimpleGraph.Walk.length_cons]
  omega

include hconn in
theorem acyclic_of_radius_girth (R : Nat) (hrad : ∀ v, G.dist v root ≤ R)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 2*R+1 < p.length) :
    G.IsAcyclic := by
  have heq : G = tree G hconn root := by
    apply le_antisymm
    · intro u v hadj
      by_contra hextra
      obtain ⟨p,hp,hlen⟩ := short_cycle_of_extra_edge G hconn root R hrad u v hadj hextra
      have hh := hgirth u p hp
      omega
    · exact subgraph G hconn root
  rw [heq]
  exact acyclic G hconn root

end Paper.HighGirthRadiusTree
#print axioms Paper.HighGirthRadiusTree.acyclic
#print axioms Paper.HighGirthRadiusTree.subgraph
#print axioms Paper.HighGirthRadiusTree.root_walk
#print axioms Paper.HighGirthRadiusTree.connected
#print axioms Paper.HighGirthRadiusTree.short_walk

#print axioms Paper.HighGirthRadiusTree.short_cycle_of_extra_edge
#print axioms Paper.HighGirthRadiusTree.acyclic_of_radius_girth
