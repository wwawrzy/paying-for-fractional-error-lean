import Paper.Endpoints.Girth.HighGirthRetainedSet
set_option maxHeartbeats 400000
namespace Paper.HighGirthRetainedPartition
theorem retained_set_partition
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    Paper.HighGirthRetainedSet.vertices G x ⊆ Paper.HighGirthRounding.last G x ∧
    Paper.HighGirthAttachments.vertices G x ⊆ Paper.HighGirthRetainedSet.vertices G x ∧
    (∀ K, Paper.HighGirthRetainedSet.vertices G x ∩ Paper.HighGirthFreePaths.members G x K =
      Paper.HighGirthRetainedSet.parts G x K) ∧
    (Paper.HighGirthRetainedSet.vertices G x).card =
      ∑ K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent,
        (Paper.HighGirthRetainedSet.parts G x K).card := by
  classical
  have hs := Paper.HighGirthRetainedSet.parts_spec G x
  have huniq : ∀ K J (u : V), u ∈ Paper.HighGirthFreePaths.members G x K →
      u ∈ Paper.HighGirthFreePaths.members G x J → K = J := by
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
    have huU : u ∈ Paper.HighGirthRounding.last G x := (Finset.mem_filter.mp huA).1
    let K := (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).connectedComponentMk ⟨u,huU⟩
    have huK : u ∈ Paper.HighGirthFreePaths.members G x K :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨huU,rfl⟩⟩
    exact Finset.mem_biUnion.mpr ⟨K,Finset.mem_univ _,(hs K).2.2.2.1 u huK huA⟩
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
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨K,Finset.mem_univ _,hu⟩,(hs K).2.1 hu⟩
  · have hd : (↑(Finset.univ : Finset (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
        Set (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent).PairwiseDisjoint (Paper.HighGirthRetainedSet.parts G x) := by
      intro K _ J _ hne
      apply Finset.disjoint_left.mpr
      intro u huK huJ
      exact hne (huniq K J u ((hs K).2.1 huK) ((hs J).2.1 huJ))
    exact Finset.card_biUnion hd
end Paper.HighGirthRetainedPartition
#print axioms Paper.HighGirthRetainedPartition.retained_set_partition
