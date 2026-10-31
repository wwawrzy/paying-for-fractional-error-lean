import Paper.TotalDomination.HighGirthTrimmedPath

namespace Paper.TotalDomination.HighGirthSetup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def isFreePathComponent
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Prop :=
  isPathComponent G x identifier hfree C ∧ freeComponent G x identifier hfree C
noncomputable def freeComponents : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent := by
  classical
  letI := Fintype.ofFinite (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
  exact Finset.univ.filter (isFreePathComponent G x identifier hfree)
noncomputable def pathComponents : Finset (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent := by
  classical
  letI := Fintype.ofFinite (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
  exact Finset.univ.filter (isPathComponent G x identifier hfree)
noncomputable def freeVertices : Finset V :=
  (freeComponents G x identifier hfree).biUnion (componentMembers G x identifier hfree)
noncomputable def nonfreeVertices : Finset V := core G x identifier hfree \ freeVertices G x identifier hfree
noncomputable def nonfreeAttachments : Finset V := attachments G x identifier hfree ∩ nonfreeVertices G x identifier hfree

theorem component_members_connected
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) :
    (G.induce (↑(componentMembers G x identifier hfree C) : Set V)).Connected := by
  classical
  let M := componentMembers G x identifier hfree C
  let f : C.toSimpleGraph →g G.induce (↑M : Set V) :=
    ⟨fun v => ⟨v.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.val.property,v.property⟩⟩,
      by intro v w hvw; exact hvw⟩
  have hsur : Function.Surjective f := by
    intro u
    obtain ⟨hu,hC⟩ := (Finset.mem_filter.mp u.property).2
    exact ⟨⟨⟨u.val,hu⟩,hC⟩,rfl⟩
  exact SimpleGraph.Connected.map f hsur C.connected_toSimpleGraph

theorem core_member_component {u : V} (hu : u ∈ core G x identifier hfree) :
    ∃ C, u ∈ componentMembers G x identifier hfree C := by
  classical
  let C := (G.induce (↑(core G x identifier hfree) : Set V)).connectedComponentMk ⟨u,hu⟩
  exact ⟨C,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu,rfl⟩⟩

theorem retained_component_parts_exist :
    ∃ parts : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent → Finset V,
      ∀ C, (parts C).Nonempty ∧ parts C ⊆ componentMembers G x identifier hfree C ∧
        (G.induce (↑(parts C) : Set V)).Connected ∧
        (∀ u ∈ componentMembers G x identifier hfree C, u ∈ attachments G x identifier hfree → u ∈ parts C) ∧
        (¬isFreePathComponent G x identifier hfree C → parts C = componentMembers G x identifier hfree C) ∧
        (isFreePathComponent G x identifier hfree C →
          (parts C).card+8 ≤ 7*(componentAttachmentPairs G x identifier hfree C).card + badCorrection G x identifier hfree C) := by
  classical
  have hex : ∀ C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent,
      ∃ S : Finset V, S.Nonempty ∧ S ⊆ componentMembers G x identifier hfree C ∧
        (G.induce (↑S : Set V)).Connected ∧
        (∀ u ∈ componentMembers G x identifier hfree C, u ∈ attachments G x identifier hfree → u ∈ S) ∧
        (¬isFreePathComponent G x identifier hfree C → S = componentMembers G x identifier hfree C) ∧
        (isFreePathComponent G x identifier hfree C →
          S.card+8 ≤ 7*(componentAttachmentPairs G x identifier hfree C).card + badCorrection G x identifier hfree C) := by
    intro C
    by_cases hf : isFreePathComponent G x identifier hfree C
    · obtain ⟨hpath,hC⟩ := hf
      obtain ⟨a,b,p,hp,hcover,hgraph⟩ := hpath
      have hS := (attachment_positions_count G x identifier hfree C hC a b p hp hcover).1
      have hs := trimmed_path_support G x identifier hfree C a b p hS
      refine ⟨trimmedVertices G x identifier hfree C p hS,hs.1,hs.2.1,
        trimmed_path_connected G x identifier hfree C a b p hS,
        trimmed_keeps_attachments G x identifier hfree C a b p hcover hS,?_,?_⟩
      · intro hn
        exact False.elim (hn ⟨⟨a,b,p,hp,hcover,hgraph⟩,hC⟩)
      · intro _
        exact trimmed_size_bound G x identifier hfree C hC a b p hp hcover hgraph hS
    · let M := componentMembers G x identifier hfree C
      have hc := component_members_connected G x identifier hfree C
      have hn : M.Nonempty := by
        obtain ⟨u⟩ := hc.nonempty
        exact ⟨u.val,u.property⟩
      exact ⟨M,hn,fun _ hu => hu,hc,fun _ hu _ => hu,fun _ => rfl,fun h => False.elim (hf h)⟩
  choose parts hp using hex
  exact ⟨parts,hp⟩

noncomputable def retainedParts := Classical.choose (retained_component_parts_exist G x identifier hfree)

theorem retainedParts_spec :
    ∀ C, (retainedParts G x identifier hfree C).Nonempty ∧
      retainedParts G x identifier hfree C ⊆ componentMembers G x identifier hfree C ∧
      (G.induce (↑(retainedParts G x identifier hfree C) : Set V)).Connected ∧
      (∀ u ∈ componentMembers G x identifier hfree C, u ∈ attachments G x identifier hfree → u ∈ retainedParts G x identifier hfree C) ∧
      (¬isFreePathComponent G x identifier hfree C → retainedParts G x identifier hfree C = componentMembers G x identifier hfree C) ∧
      (isFreePathComponent G x identifier hfree C →
        (retainedParts G x identifier hfree C).card+8 ≤ 7*(componentAttachmentPairs G x identifier hfree C).card + badCorrection G x identifier hfree C) :=
  Classical.choose_spec (retained_component_parts_exist G x identifier hfree)

noncomputable def retainedVertices : Finset V := by
  classical
  letI := Fintype.ofFinite (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent
  exact Finset.univ.biUnion (retainedParts G x identifier hfree)

end Paper.TotalDomination.HighGirthSetup
