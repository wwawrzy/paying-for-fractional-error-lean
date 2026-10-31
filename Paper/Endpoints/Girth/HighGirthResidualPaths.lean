import Paper.Endpoints.Girth.HighGirthShortPaths
set_option maxHeartbeats 200000
namespace Paper.HighGirthResidualPaths

theorem residual_short_paths
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (u : V) (hu : u ∈ Paper.HighGirthRounding.last G x) :
    (∃ b ∈ Paper.HighGirthTransformation.branches G ∩ Paper.HighGirthRounding.last G x,
      ∃ w : G.Walk u b, w.IsPath ∧ w.length ≤ 2 ∧
        ∀ v ∈ w.support, v ∈ Paper.HighGirthRounding.last G x) ∨
    (∃ b ∈ Paper.HighGirthAttachments.vertices G x,
      ∃ w : G.Walk u b, w.IsPath ∧ w.length ≤ 1 ∧
        ∀ v ∈ w.support, v ∈ Paper.HighGirthRounding.last G x) ∨
    (∃ l ∈ Paper.HighGirthRounding.middle G x,
      ∃ w : G.Walk u l, w.IsPath ∧ w.length ≤ 2 ∧
        ∀ v ∈ w.support, v ∈ insert l (Paper.HighGirthRounding.last G x)) := by
  classical
  let U := Paper.HighGirthRounding.last G x
  have hone : ∀ (b : V), b ∈ U → u ∈ Paper.SevenFoundation.closed G b →
      ∃ w : G.Walk u b, w.IsPath ∧ w.length ≤ 1 ∧ ∀ v ∈ w.support, v ∈ U := by
    intro b hb hub
    have hw : ∃ w : G.Walk u b, w.length ≤ 1 ∧ ∀ v ∈ w.support, v ∈ U := by
      rcases (Paper.SevenFoundation.mem_closed G u b).mp hub with heq | hbu
      · subst u
        exact ⟨SimpleGraph.Walk.nil, by simp, by simpa using hb⟩
      · refine ⟨SimpleGraph.Walk.cons hbu.symm SimpleGraph.Walk.nil, by simp, ?_⟩
        intro v hv
        have hv' : v = u ∨ v = b := by simpa using hv
        rcases hv' with rfl | rfl
        · exact hu
        · exact hb
    obtain ⟨w, hw, hs⟩ := hw
    exact ⟨w.bypass, w.bypass_isPath, (w.length_bypass_le).trans hw,
      fun v hv => hs v (w.support_bypass_subset hv)⟩
  rcases Paper.HighGirthShortAccess.short_access_witness G x u hu with
    ⟨b, hb, p, hp, hup, hpb⟩ | ⟨b, hb, hub⟩ | ⟨l, hl, hpath⟩
  · left
    exact ⟨b, hb, Paper.HighGirthShortPaths.two_closed_steps_path G U u p b hu hp
      (Finset.mem_inter.mp hb).2 hup hpb⟩
  · right
    left
    exact ⟨b, hb, hone b (Finset.mem_filter.mp hb).1 hub⟩
  · right
    right
    refine ⟨l, hl, ?_⟩
    have huS : u ∈ insert l U := Finset.mem_insert_of_mem hu
    have hlS : l ∈ insert l U := Finset.mem_insert_self l U
    rcases hpath with hul | ⟨p, hp, hup, hpl⟩
    · exact Paper.HighGirthShortPaths.two_closed_steps_path G (insert l U) u l l huS hlS hlS
        hul (Paper.SevenFoundation.self_mem_closed G l)
    · exact Paper.HighGirthShortPaths.two_closed_steps_path G (insert l U) u p l huS
        (Finset.mem_insert_of_mem hp) hlS hup hpl

end Paper.HighGirthResidualPaths

#print axioms Paper.HighGirthResidualPaths.residual_short_paths
