import Paper.TotalDomination.HighGirthComponentCount
import Paper.Endpoints.Girth.HighGirthInducedEdgeSets
namespace Paper.TotalDomination.HighGirthSetup
set_option maxHeartbeats 200000
theorem retained_path_is_tree_and_edge_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hpath : isPathComponent G x identifier hfree K) :
    (G.induce (↑(retainedParts G x identifier hfree K) : Set V)).IsTree ∧
    Nat.card (G.induce (↑(retainedParts G x identifier hfree K) : Set V)).edgeSet + 1 =
      (retainedParts G x identifier hfree K).card := by
  classical
  let S := retainedParts G x identifier hfree K
  have huniv : @Finset.univ (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
      (Fintype.ofFinite _) = (Finset.univ : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) := by
    ext; simp only [Finset.mem_univ]
  have hs := retainedParts_spec G x identifier hfree K
  have hu : ∀ u : {v // v ∈ S}, ∃ hv : u.val ∈ core G x identifier hfree,
      (G.induce (↑(core G x identifier hfree) : Set V)).connectedComponentMk ⟨u.val,hv⟩ = K := by
    intro u
    exact (Finset.mem_filter.mp (hs.2.1 u.property)).2
  let f : G.induce (↑S : Set V) →g K.toSimpleGraph :=
    ⟨fun u => ⟨⟨u.val,Classical.choose (hu u)⟩,Classical.choose_spec (hu u)⟩,
      by intro u v huv; exact huv⟩
  have hinj : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    exact congrArg (fun w : K => w.val.val) he
  have hacyc : (G.induce (↑S : Set V)).IsAcyclic :=
    SimpleGraph.IsAcyclic.comap f hinj (path_component_is_tree G x identifier hfree K hpath).isAcyclic
  have hc : (G.induce (↑S : Set V)).Connected := hs.2.2.1
  have ht : (G.induce (↑S : Set V)).IsTree := { connected := hc, isAcyclic := hacyc }
  constructor
  · exact ht
  · have he := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
    have hv : Nat.card {v // v ∈ S} = S.card := by
      rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    change Nat.card (G.induce (↑S : Set V)).edgeSet + 1 = Nat.card {v // v ∈ S} at he
    rw [hv] at he
    exact he
set_option maxHeartbeats 200000

theorem retained_nonpath_edge_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hnot : ¬ isPathComponent G x identifier hfree K) :
    Nat.card (G.induce (↑(retainedParts G x identifier hfree K) : Set V)).edgeSet =
      (retainedParts G x identifier hfree K).card := by
  classical
    letI : Fintype K := Fintype.ofFinite K
    letI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
    let S := retainedParts G x identifier hfree K
    have hs := retainedParts_spec G x identifier hfree K
    have hnf : ¬ isFreePathComponent G x identifier hfree K := fun hf => hnot hf.1
    have hS : S = componentMembers G x identifier hfree K := hs.2.2.2.2.1 hnf
    have hcycle := core_components_path_or_cycle G x identifier hfree K
    rcases hcycle with hp | hc
    · exact (hnot hp).elim
    obtain ⟨a, c, hc, hcover, hgraph⟩ := hc
    have hE := Paper.HighGirthSpanningCycleEdges.spanning_cycle_edges K.toSimpleGraph a c hc hcover hgraph
    let f : K → {v // v ∈ S} := fun z => ⟨z.val.val, by
      rw [hS]
      exact Finset.mem_filter.mpr ⟨(by simp only [Finset.mem_univ]), ⟨z.val.property, z.property⟩⟩⟩
    have hinj : Function.Injective f := by
      intro u v heq
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {v // v ∈ S} => z.val) heq
    have hsur : Function.Surjective f := by
      intro u
      have huK : u.val ∈ componentMembers G x identifier hfree K := by
        rw [← hS]
        exact u.property
      obtain ⟨hu, hK⟩ := (Finset.mem_filter.mp huK).2
      refine ⟨⟨⟨u.val, hu⟩, hK⟩, ?_⟩
      rfl
    let e : K.toSimpleGraph ≃g G.induce (↑S : Set V) :=
      { toEquiv := Equiv.ofBijective f ⟨hinj, hsur⟩
        map_rel_iff' := by
          intro u v
          rfl }
    have he := e.card_edgeFinset_eq
    have hv := Fintype.card_congr e.toEquiv
    change Fintype.card K = Fintype.card {v // v ∈ S} at hv
    have hv' : Fintype.card K = S.card := by
      simpa only [Fintype.card_coe] using hv
    change Nat.card (G.induce (↑S : Set V)).edgeSet = S.card
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, ← he, hE, hv']


set_option maxHeartbeats 400000
theorem retained_set_partition
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    retainedVertices G x identifier hfree ⊆ core G x identifier hfree ∧
    attachments G x identifier hfree ⊆ retainedVertices G x identifier hfree ∧
    (∀ K, retainedVertices G x identifier hfree ∩ componentMembers G x identifier hfree K =
      retainedParts G x identifier hfree K) ∧
    (retainedVertices G x identifier hfree).card =
      ∑ K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent,
        (retainedParts G x identifier hfree K).card := by
  classical
  have huniv : @Finset.univ (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
      (Fintype.ofFinite _) = (Finset.univ : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) := by
    ext; simp only [Finset.mem_univ]
  have hs := retainedParts_spec G x identifier hfree
  have huniq : ∀ K J (u : V), u ∈ componentMembers G x identifier hfree K →
      u ∈ componentMembers G x identifier hfree J → K = J := by
    intro K J u huK huJ
    obtain ⟨hu,hK⟩ := (Finset.mem_filter.mp huK).2
    obtain ⟨hu',hJ⟩ := (Finset.mem_filter.mp huJ).2
    exact hK.symm.trans hJ
  constructor
  · intro u hu
    obtain ⟨K,_,huK⟩ := Finset.mem_biUnion.mp hu
    have hh := (hs K).2.1 huK
    obtain ⟨huU,_⟩ := (Finset.mem_filter.mp hh).2
    exact huU
  constructor
  · intro u huA
    have huU : u ∈ core G x identifier hfree := Finset.mem_inter.mp huA |>.1
    let K := (G.induce (↑(core G x identifier hfree) : Set V)).connectedComponentMk ⟨u,huU⟩
    have huK : u ∈ componentMembers G x identifier hfree K :=
      Finset.mem_filter.mpr ⟨(by simp only [Finset.mem_univ]),⟨huU,rfl⟩⟩
    exact Finset.mem_biUnion.mpr ⟨K,(by simp only [Finset.mem_univ]),(hs K).2.2.2.1 u huK huA⟩
  constructor
  · intro K
    ext u
    constructor
    · intro hu
      obtain ⟨huU,huK⟩ := Finset.mem_inter.mp hu
      obtain ⟨J,_,huJ⟩ := Finset.mem_biUnion.mp huU
      have he := huniq J K u ((hs J).2.1 huJ) huK
      simpa only [he] using huJ
    · intro hu
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨K,(by simp only [Finset.mem_univ]),hu⟩,(hs K).2.1 hu⟩
  · have hd : (↑(Finset.univ : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) :
        Set (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent).PairwiseDisjoint (retainedParts G x identifier hfree) := by
      intro K _ J _ hne
      apply Finset.disjoint_left.mpr
      intro u huK huJ
      exact hne (huniq K J u ((hs K).2.1 huK) ((hs J).2.1 huJ))
    simpa only [retainedVertices, huniv] using Finset.card_biUnion hd
set_option maxHeartbeats 200000
theorem retained_edge_card_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    Nat.card (G.induce (↑(retainedVertices G x identifier hfree) : Set V)).edgeSet =
      ∑ K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent,
        Nat.card (G.induce (↑(retainedParts G x identifier hfree K) : Set V)).edgeSet := by
  classical
  let S := retainedVertices G x identifier hfree
  let R := retainedParts G x identifier hfree
  let E := Paper.HighGirthInducedEdgeSets.edges G
  have huniv : @Finset.univ (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
      (Fintype.ofFinite _) = (Finset.univ : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) := by
    ext; simp only [Finset.mem_univ]
  have hs := retainedParts_spec G x identifier hfree
  have hp := retained_set_partition G x identifier hfree
  have hmem : ∀ (T : Finset V) (u v : V), s(u,v) ∈ E T ↔ G.Adj u v ∧ u ∈ T ∧ v ∈ T := by
    intro T u v
    simp [E,Paper.HighGirthInducedEdgeSets.edges,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  have hsub : ∀ K, R K ⊆ S := by
    intro K u hu
    exact Finset.mem_biUnion.mpr ⟨K,(by simp only [Finset.mem_univ]),hu⟩
  have huniq : ∀ K J (u : V), u ∈ componentMembers G x identifier hfree K →
      u ∈ componentMembers G x identifier hfree J → K = J := by
    intro K J u huK huJ
    obtain ⟨hu,hK⟩ := (Finset.mem_filter.mp huK).2
    obtain ⟨hu',hJ⟩ := (Finset.mem_filter.mp huJ).2
    exact hK.symm.trans hJ
  have hdis : (↑(Finset.univ : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) :
      Set (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent).PairwiseDisjoint (fun K => E (R K)) := by
    intro K _ J _ hne
    apply Finset.disjoint_left.mpr
    intro e heK heJ
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huK := ((hmem (R K) u v).mp heK).2.1
      have huJ := ((hmem (R J) u v).mp heJ).2.1
      exact hne (huniq K J u ((hs K).2.1 huK) ((hs J).2.1 huJ))
  have hcover : E S = Finset.univ.biUnion (fun K => E (R K)) := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      constructor
      · intro he
        obtain ⟨hadj,huS,hvS⟩ := (hmem S u v).mp he
        have huU : u ∈ core G x identifier hfree := hp.1 huS
        have hvU : v ∈ core G x identifier hfree := hp.1 hvS
        let K := (G.induce (↑(core G x identifier hfree) : Set V)).connectedComponentMk ⟨u,huU⟩
        have huK : u ∈ componentMembers G x identifier hfree K :=
          Finset.mem_filter.mpr ⟨(by simp only [Finset.mem_univ]),⟨huU,rfl⟩⟩
        have hvK := component_adj_closed G x identifier hfree K huK hvU hadj
        have huR : u ∈ R K := by
          change u ∈ retainedParts G x identifier hfree K
          rw [←hp.2.2.1 K]
          exact Finset.mem_inter.mpr ⟨huS,huK⟩
        have hvR : v ∈ R K := by
          change v ∈ retainedParts G x identifier hfree K
          rw [←hp.2.2.1 K]
          exact Finset.mem_inter.mpr ⟨hvS,hvK⟩
        exact Finset.mem_biUnion.mpr ⟨K,(by simp only [Finset.mem_univ]),(hmem (R K) u v).mpr ⟨hadj,huR,hvR⟩⟩
      · intro he
        obtain ⟨K,_,heK⟩ := Finset.mem_biUnion.mp he
        obtain ⟨hadj,huR,hvR⟩ := (hmem (R K) u v).mp heK
        exact (hmem S u v).mpr ⟨hadj,hsub K huR,hsub K hvR⟩
  calc
    _ = (E S).card := (Paper.HighGirthInducedEdgeSets.edges_card G S).symm
    _ = (Finset.univ.biUnion (fun K => E (R K))).card := congrArg Finset.card hcover
    _ = ∑ K, (E (R K)).card := Finset.card_biUnion hdis
    _ = _ := by
      apply Finset.sum_congr rfl
      intro K hK
      exact Paper.HighGirthInducedEdgeSets.edges_card G (R K)


theorem retained_edge_count
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    Nat.card (G.induce (↑(retainedVertices G x identifier hfree) : Set V)).edgeSet +
      (pathComponents G x identifier hfree).card =
      (retainedVertices G x identifier hfree).card := by
  classical
  have hpoint : ∀ K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent,
      Nat.card (G.induce (↑(retainedParts G x identifier hfree K) : Set V)).edgeSet +
        (if isPathComponent G x identifier hfree K then 1 else 0) =
        (retainedParts G x identifier hfree K).card := by
    intro K
    by_cases hp : isPathComponent G x identifier hfree K
    · simpa only [hp,ite_true] using (retained_path_is_tree_and_edge_count G x identifier hfree K hp).2
    · simpa only [hp,ite_false,Nat.add_zero] using retained_nonpath_edge_count G x identifier hfree K hp
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun K _ => hpoint K)
  have huniv : @Finset.univ (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
      (Fintype.ofFinite _) = (Finset.univ : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) := by
    ext; simp only [Finset.mem_univ]
  have hcp : (∑ K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent,
      if isPathComponent G x identifier hfree K then 1 else 0) =
      (pathComponents G x identifier hfree).card := by
    simp [pathComponents, huniv]
  rw [Finset.sum_add_distrib,hcp,←retained_edge_card_sum G x identifier hfree,
    ←(retained_set_partition G x identifier hfree).2.2.2] at hsum
  exact hsum

end Paper.TotalDomination.HighGirthSetup
