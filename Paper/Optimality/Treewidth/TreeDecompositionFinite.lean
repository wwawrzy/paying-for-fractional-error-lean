import Paper.Optimality.Treewidth.TreeDecompositionRoutes

/-! A finite graph with a possibly infinite decomposition tree has a
decomposition on a finite subtree, with the same width. Only finitely many
vertex/edge witness bags and the finite root paths to them are retained. -/
namespace Paper.TreeDecompositionFinite
open SimpleGraph
universe u
variable {V I : Type u} {G : SimpleGraph V} {T : SimpleGraph I}
variable (D : G.TreeDecomposition T)

theorem support [Fintype V] : ∃ S : Finset I,
    (T.induce (S : Set I)).IsTree ∧
      (∀ v : V, ∃ i : ↥(S : Set I), v ∈ D.bag i.val) ∧
      (∀ u v : V, G.Adj u v → ∃ i : ↥(S : Set I), u ∈ D.bag i.val ∧ v ∈ D.bag i.val) := by
  classical
  let root : I := D.isTree.connected.nonempty.some
  let vertexBag : V → I := fun v => (D.cover v).choose
  let edgeBag : V → V → I := fun u v => if h : G.Adj u v then (D.edge_mem h).choose else root
  let seeds : Finset I := Finset.univ.image vertexBag ∪
    Finset.univ.biUnion (fun u : V => Finset.univ.image (edgeBag u))
  let path := fun i => (D.isTree.existsUnique_path root i).choose
  let S := insert root (seeds.biUnion (fun i => (path i).support.toFinset))
  have hroot : root ∈ S := Finset.mem_insert_self _ _
  have hseeds : seeds ⊆ S := by
    intro i hi
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, hi,
      List.mem_toFinset.mpr (path i).end_mem_support⟩)
  have hconn : (T.induce (S : Set I)).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨root, hroot⟩, ?_⟩
    intro v
    rcases Finset.mem_insert.mp v.property with he | hv
    · have hveq : v = (⟨root, hroot⟩ : ↥(S : Set I)) := Subtype.ext he
      rw [hveq]
    · obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
      have hvpath := List.mem_toFinset.mp hvi
      let q := (path i).takeUntil v.val hvpath
      have hq : ∀ w ∈ q.support, w ∈ (S : Set I) := by
        intro w hw
        have hp : w ∈ (path i).support := (path i).support_takeUntil_subset hvpath hw
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, hi, List.mem_toFinset.mpr hp⟩)
      exact (q.induce (S : Set I) hq).reachable
  refine ⟨S, ⟨hconn, D.isTree.isAcyclic.induce _⟩, ?_, ?_⟩
  · intro v
    have hs : vertexBag v ∈ seeds := Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
    exact ⟨⟨vertexBag v, hseeds hs⟩, (D.cover v).choose_spec⟩
  · intro u v huv
    have hs : edgeBag u v ∈ seeds := Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨⟨edgeBag u v, hseeds hs⟩, ?_⟩
    dsimp only [edgeBag]
    rw [dif_pos huv]
    exact (D.edge_mem huv).choose_spec

def restrict (S : Finset I) (hT : (T.induce (S : Set I)).IsTree)
    (hcover : ∀ v : V, ∃ i : ↥(S : Set I), v ∈ D.bag i.val)
    (hedge : ∀ u v : V, G.Adj u v → ∃ i : ↥(S : Set I), u ∈ D.bag i.val ∧ v ∈ D.bag i.val) :
    G.TreeDecomposition (T.induce (S : Set I)) where
  bag i := D.bag i.val
  isTree := hT
  cover := hcover
  edge_mem u v huv := hedge u v huv
  bag_connected v _ _ p hp hi hj r hr := by
    let e : T.induce (S : Set I) →g T := (Embedding.induce (S : Set I)).toHom
    have hpath : (p.map e).IsPath := p.map_isPath_of_injective Subtype.val_injective hp
    apply D.bag_connected v (p.map e) hpath hi hj
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩

theorem exists_finite [Fintype V] (t : ℕ) (hD : D.IsWidthLE t) :
    ∃ (J : Type u), ∃ _ : Fintype J, ∃ (U : SimpleGraph J) (E : G.TreeDecomposition U), E.IsWidthLE t := by
  classical
  obtain ⟨S, hT, hcover, hedge⟩ := support D
  refine ⟨↥(S : Set I), inferInstance, T.induce (S : Set I), restrict D S hT hcover hedge, ?_⟩
  exact fun i => hD i.val

end Paper.TreeDecompositionFinite
