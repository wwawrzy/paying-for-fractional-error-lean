import Paper.Endpoints.Girth.HighGirthFreeTrim
set_option maxHeartbeats 200000
namespace Paper.HighGirthRetainedParts

theorem retained_component_parts_exist
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) :
    ∃ parts : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent → Finset V,
      ∀ K, (parts K).Nonempty ∧ (parts K) ⊆ Paper.HighGirthFreePaths.members G x K ∧
      (G.induce (↑(parts K) : Set V)).Connected ∧
      (∀ u ∈ Paper.HighGirthFreePaths.members G x K, u ∈ Paper.HighGirthAttachments.vertices G x → u ∈ (parts K)) ∧
      (¬ Paper.HighGirthFreePaths.isFreePath G x K → (parts K) = Paper.HighGirthFreePaths.members G x K) ∧
      (Paper.HighGirthFreePaths.isFreePath G x K →
        (parts K).card + 4 ≤ 5 * Paper.HighGirthComponentAttachments.count G x K ∧
        (Paper.HighGirthComponentAttachments.count G x K = 2 →
          K ∉ Paper.HighGirthFewAttachments.twoFamily G x → (parts K).card ≤ 5)) := by
  classical
    have h : ∀ K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent, ∃ S : Finset V, S.Nonempty ∧ S ⊆ Paper.HighGirthFreePaths.members G x K ∧
          (G.induce (↑S : Set V)).Connected ∧
          (∀ u ∈ Paper.HighGirthFreePaths.members G x K, u ∈ Paper.HighGirthAttachments.vertices G x → u ∈ S) ∧
          (¬ Paper.HighGirthFreePaths.isFreePath G x K → S = Paper.HighGirthFreePaths.members G x K) ∧
          (Paper.HighGirthFreePaths.isFreePath G x K →
            S.card + 4 ≤ 5 * Paper.HighGirthComponentAttachments.count G x K ∧
            (Paper.HighGirthComponentAttachments.count G x K = 2 →
              K ∉ Paper.HighGirthFewAttachments.twoFamily G x → S.card ≤ 5)) := by
      intro K
      by_cases hf : Paper.HighGirthFreePaths.isFreePath G x K
      · obtain ⟨S,hne,hsub,hconn,hretain,hsize,hsmall⟩ := Paper.HighGirthFreeTrim.exists_trim G x K hf
        refine ⟨S,hne,hsub,hconn,hretain,?_,?_⟩
        · intro hn
          exact (hn hf).elim
        · intro _
          exact ⟨hsize,hsmall⟩
      · let M := Paper.HighGirthFreePaths.members G x K
        let f : K.toSimpleGraph →g G.induce (↑M : Set V) :=
          ⟨fun v => ⟨v.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨v.val.property,v.property⟩⟩⟩,
            by intro v w hvw; exact hvw⟩
        have hsur : Function.Surjective f := by
          intro u
          obtain ⟨hu,hK⟩ := (Finset.mem_filter.mp u.property).2
          refine ⟨⟨⟨u.val,hu⟩,hK⟩,?_⟩
          rfl
        have hc : (G.induce (↑M : Set V)).Connected := SimpleGraph.Connected.map f hsur K.connected_toSimpleGraph
        have hn : M.Nonempty := by
          obtain ⟨v⟩ := hc.nonempty
          exact ⟨v.val,v.property⟩
        refine ⟨M,hn,(by intro u hu; exact hu),hc,?_,?_,?_⟩
        · intro u hu _
          exact hu
        · intro _
          rfl
        · intro hfree
          exact (hf hfree).elim
    choose parts hp using h
    exact ⟨parts,hp⟩

end Paper.HighGirthRetainedParts

#print axioms Paper.HighGirthRetainedParts.retained_component_parts_exist
