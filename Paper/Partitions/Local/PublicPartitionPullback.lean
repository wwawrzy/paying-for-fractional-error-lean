import Paper.Preliminaries.PublicPartPullback
import Paper.Owners.Construction.BoundaryOwners

/-! Pullback of the entire actual public partition, preserving small
connected parts, disjointness, coverage and the exact boundary owners. -/
namespace Paper.PublicPartitionPullback
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V)

noncomputable local instance mappedAdj : DecidableRel (PublicEmbedding.graph J e).Adj :=
  fun _ _ => Classical.propDecidable _

noncomputable def data (S : Finset V) (k : ℕ)
    (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e) (P : SmallParts.Data (PublicEmbedding.graph J e) S k) :
    SmallParts.Data J Finset.univ k := by
  have hr : ∀ I ∈ P.parts, (I : Set V) ⊆ Set.range e :=
    fun I hI v hv => (hS v).mp (P.subset I hI hv)
  refine {
    parts := P.parts.image (PublicPartPullback.pull e)
    nonempty := ?_
    subset := fun _ _ _ _ => Finset.mem_univ _
    connected := ?_
    size := ?_
    disjoint := ?_
    covers := ?_ }
  · intro U hU
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨v, hv⟩ := P.nonempty I hI
    obtain ⟨w, he⟩ := hr I hI hv
    exact ⟨w, (PublicPartPullback.mem_pull e I w).mpr (he.symm ▸ hv)⟩
  · intro U hU
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hU
    exact PublicPartPullback.connected e J I (hr I hI) (P.connected I hI)
  · intro U hU
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hU
    rw [PublicPartPullback.card_pull e I (hr I hI)]
    exact P.size I hI
  · intro U hU Z hZ hne
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hZ
    apply Finset.disjoint_left.mpr
    intro w hwI hwK
    exact Finset.disjoint_left.mp (P.disjoint hI hK (fun he => hne (congrArg (PublicPartPullback.pull e) he)))
      ((PublicPartPullback.mem_pull e I w).mp hwI) ((PublicPartPullback.mem_pull e K w).mp hwK)
  · intro w _
    obtain ⟨I, hI, hw⟩ := P.covers (e w) ((hS (e w)).mpr ⟨w, rfl⟩)
    exact ⟨PublicPartPullback.pull e I, Finset.mem_image.mpr ⟨I, hI, rfl⟩,
      (PublicPartPullback.mem_pull e I w).mpr hw⟩

theorem same_part (S : Finset V) (k : ℕ) (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e)
    (P : SmallParts.Data (PublicEmbedding.graph J e) S k) (w z : W) :
    (∃ U ∈ (data J e S k hS P).parts, w ∈ U ∧ z ∈ U) ↔
      ∃ I ∈ P.parts, e w ∈ I ∧ e z ∈ I := by
  change (∃ U ∈ P.parts.image (PublicPartPullback.pull e), w ∈ U ∧ z ∈ U) ↔ _
  constructor
  · rintro ⟨U, hU, hw, hz⟩
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨I, hI, (PublicPartPullback.mem_pull e I w).mp hw, (PublicPartPullback.mem_pull e I z).mp hz⟩
  · rintro ⟨I, hI, hw, hz⟩
    exact ⟨PublicPartPullback.pull e I, Finset.mem_image.mpr ⟨I, hI, rfl⟩,
      (PublicPartPullback.mem_pull e I w).mpr hw, (PublicPartPullback.mem_pull e I z).mpr hz⟩

theorem boundary (S : Finset V) (k : ℕ) (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e)
    (P : SmallParts.Data (PublicEmbedding.graph J e) S k) (w : W) :
    w ∈ BoundaryOwners.vertices J Finset.univ (data J e S k hS P).parts ↔
      e w ∈ BoundaryOwners.vertices (PublicEmbedding.graph J e) S P.parts := by
  simp only [BoundaryOwners.vertices, Set.mem_toFinset, SimpleGraph.mem_support, PartCut.graph,
    Finset.mem_univ, true_and, same_part J e S k hS P]
  constructor
  · rintro ⟨z, ha, hne⟩
    exact ⟨e z, (PublicEmbedding.adj_iff J e _ _).mpr ⟨w, z, ha, rfl, rfl⟩,
      (hS (e w)).mpr ⟨w, rfl⟩, (hS (e z)).mpr ⟨z, rfl⟩, hne⟩
  · rintro ⟨v, ha, _, _, hne⟩
    obtain ⟨u, z, huz, hu, hz⟩ := (PublicEmbedding.adj_iff J e _ _).mp ha
    have he : u = w := e.injective hu
    subst u
    refine ⟨z, huz, ?_⟩
    rw [hz]
    exact hne

end Paper.PublicPartitionPullback
