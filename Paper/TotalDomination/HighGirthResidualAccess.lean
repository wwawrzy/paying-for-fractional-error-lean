import Paper.TotalDomination.HighGirthResidualGeometry

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem walk_access {u b : V} (p : G.Walk u b) (hu : u ∈ core G x identifier hfree)
    (hb : b ∈ B G) (hs : ∀ v ∈ p.support, v ∈ Z G) :
    (∃ b ∈ B G ∩ core G x identifier hfree, ∃ q : G.Walk u b,
      q.length ≤ p.length ∧ ∀ v ∈ q.support, v ∈ core G x identifier hfree) ∨
    (∃ b ∈ attachments G x identifier hfree, ∃ q : G.Walk u b,
      q.length+1 ≤ p.length ∧ ∀ v ∈ q.support, v ∈ core G x identifier hfree) ∨
    (∃ y ∈ served G (I G x identifier hfree), ∃ q : G.Walk u y,
      q.length ≤ p.length ∧ ∀ v ∈ q.support, v = y ∨ v ∈ core G x identifier hfree) := by
  induction p with
  | @nil u =>
    exact Or.inl ⟨u,Finset.mem_inter.mpr ⟨hb,hu⟩,.nil,le_rfl,by simpa using hu⟩
  | @cons u v b ha p ih =>
    have hvZ : v ∈ Z G := hs v (by simp)
    have hs' : ∀ z ∈ p.support, z ∈ Z G := fun z hz => hs z (by simp [hz])
    by_cases hv : v ∈ core G x identifier hfree
    · rcases ih hv hb hs' with ⟨z,hz,q,hq,hqs⟩ | ⟨z,hz,q,hq,hqs⟩ | ⟨z,hz,q,hq,hqs⟩
      · left
        refine ⟨z,hz,.cons ha q,by simpa using hq,?_⟩
        intro z hz
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hu
        · exact hqs z hz
      · right; left
        refine ⟨z,hz,.cons ha q,?_,?_⟩
        · simp only [SimpleGraph.Walk.length_cons]; omega
        · intro z hz
          simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hu
          · exact hqs z hz
      · right; right
        refine ⟨z,hz,.cons ha q,by simpa using hq,?_⟩
        intro z hz
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Or.inr hu
        · exact hqs z hz
    · by_cases hvR : v ∈ residual G (I G x identifier hfree)
      · have hm := core_neighbor_partition G x identifier hfree hu hvR ha
        have hy : v ∈ served G (I G x identifier hfree) :=
          (Finset.mem_sdiff.mp ((Finset.mem_union.mp hm).resolve_left hv)).1
        right; right
        refine ⟨v,hy,.cons ha .nil,by simp,?_⟩
        intro z hz
        have hz' : z = u ∨ z = v := by simpa using hz
        rcases hz' with rfl | rfl
        · exact Or.inr hu
        · exact Or.inl rfl
      · have ht := outside_neighbor_connector G x identifier hfree hu
          (Finset.mem_sdiff.mpr ⟨hvZ,hvR⟩) ha
        have hat : u ∈ attachments G x identifier hfree :=
          Finset.mem_inter.mpr ⟨hu,(mem_neighbors G).mpr ⟨v,ht,ha⟩⟩
        right; left
        exact ⟨u,hat,.nil,by simp,by simpa using hu⟩

theorem short_access {u : V} (hu : u ∈ core G x identifier hfree) :
    (∃ b ∈ B G ∩ core G x identifier hfree, ∃ q : G.Walk u b,
      q.IsPath ∧ q.length ≤ 3 ∧ ∀ v ∈ q.support, v ∈ core G x identifier hfree) ∨
    (∃ b ∈ attachments G x identifier hfree, ∃ q : G.Walk u b,
      q.IsPath ∧ q.length ≤ 2 ∧ ∀ v ∈ q.support, v ∈ core G x identifier hfree) ∨
    (∃ y ∈ served G (I G x identifier hfree), ∃ q : G.Walk u y,
      q.IsPath ∧ q.length ≤ 3 ∧ ∀ v ∈ q.support, v = y ∨ v ∈ core G x identifier hfree) := by
  have hz := (Finset.mem_sdiff.mp (core_residual G x identifier hfree hu)).1
  obtain ⟨b,hb,p,hp,hs⟩ := HighGirthSelection.remaining_path G hfree hz
  rcases walk_access G x identifier hfree (p : G.Walk u b) hu hb hs with
    ⟨b,hb,q,hq,hqs⟩ | ⟨b,hb,q,hq,hqs⟩ | ⟨y,hy,q,hq,hqs⟩
  · exact Or.inl ⟨b,hb,q.bypass,q.bypass_isPath,(q.length_bypass_le.trans hq).trans hp,
      fun v hv => hqs v (q.support_bypass_subset hv)⟩
  · right; left
    refine ⟨b,hb,q.bypass,q.bypass_isPath,?_,fun v hv => hqs v (q.support_bypass_subset hv)⟩
    have hh := q.length_bypass_le
    omega
  · right; right
    exact ⟨y,hy,q.bypass,q.bypass_isPath,(q.length_bypass_le.trans hq).trans hp,
      fun v hv => hqs v (q.support_bypass_subset hv)⟩

end Paper.TotalDomination.HighGirthSetup
