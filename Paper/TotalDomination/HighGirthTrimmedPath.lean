import Paper.TotalDomination.HighGirthAttachmentGap
import Paper.TotalDomination.HighGirthSpan
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Paper.TotalDomination.HighGirthSetup
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)
variable (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)

noncomputable def trimmedIndices {a b : C} (p : C.toSimpleGraph.Walk a b)
    (hS : (attachmentPositions G x identifier hfree C p).Nonempty) : Finset ℕ :=
  Finset.Icc ((attachmentPositions G x identifier hfree C p).min' hS)
    ((attachmentPositions G x identifier hfree C p).max' hS)
noncomputable def trimmedVertices {a b : C} (p : C.toSimpleGraph.Walk a b)
    (hS : (attachmentPositions G x identifier hfree C p).Nonempty) : Finset V := by
  classical
  exact (trimmedIndices G x identifier hfree C p hS).image (fun i => (p.getVert i).val.val)

theorem trimmed_path_support
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : K) (p : K.toSimpleGraph.Walk a b)
    (hS : (attachmentPositions G x identifier hfree K p).Nonempty) :
    let S := attachmentPositions G x identifier hfree K p
    let m := S.min' hS
    let M := S.max' hS
    (trimmedVertices G x identifier hfree K p hS).Nonempty ∧
    trimmedVertices G x identifier hfree K p hS ⊆ componentMembers G x identifier hfree K ∧
    (((p.drop m).take (M - m)).support.toFinset.image (fun v : K => v.val.val)) =
      trimmedVertices G x identifier hfree K p hS := by
  classical
  dsimp only
  let S := attachmentPositions G x identifier hfree K p
  let m := S.min' hS
  let M := S.max' hS
  change (trimmedVertices G x identifier hfree K p hS).Nonempty ∧
    trimmedVertices G x identifier hfree K p hS ⊆ componentMembers G x identifier hfree K ∧
    (((p.drop m).take (M-m)).support.toFinset.image (fun v : K => v.val.val)) =
      trimmedVertices G x identifier hfree K p hS
  have hmM : m ≤ M := Finset.min'_le S _ (Finset.max'_mem S hS)
  have hML : M ≤ p.length := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem S hS)).1
    omega
  have hlen : ((p.drop m).take (M-m)).length = M-m := by
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length]
    exact Nat.min_eq_left (by omega)
  have hget : ∀ k, k ≤ M-m → ((p.drop m).take (M-m)).getVert k = p.getVert (m+k) := by
    intro k hk
    rw [SimpleGraph.Walk.take_getVert,SimpleGraph.Walk.drop_getVert]
    rw [Nat.min_eq_right hk]
  constructor
  · exact ⟨(p.getVert m).val.val,Finset.mem_image.mpr ⟨m,Finset.mem_Icc.mpr ⟨le_rfl,hmM⟩,rfl⟩⟩
  constructor
  · intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨(p.getVert i).val.property,(p.getVert i).property⟩⟩
  · change (((p.drop m).take (M-m)).support.toFinset.image (fun v : K => v.val.val)) =
      (Finset.Icc m M).image (fun i => (p.getVert i).val.val)
    ext u
    constructor
    · intro hu
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
      obtain ⟨k,hkv,hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hv)
      have hkM : k ≤ M-m := by simpa only [hlen] using hk
      have he : (p.getVert (m+k)).val.val = u := by
        rw [←hget k hkM,hkv]
        exact hvu
      exact Finset.mem_image.mpr ⟨m+k,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,he⟩
    · intro hu
      obtain ⟨i,hi,hiu⟩ := Finset.mem_image.mp hu
      have hi' : m ≤ i ∧ i ≤ M := Finset.mem_Icc.mp hi
      have hk : i-m ≤ M-m := by omega
      have he : ((p.drop m).take (M-m)).getVert (i-m) = p.getVert i := by
        rw [hget (i-m) hk]
        congr 1
        omega
      apply Finset.mem_image.mpr
      refine ⟨p.getVert i,List.mem_toFinset.mpr ?_,hiu⟩
      exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨i-m,he,by simpa only [hlen] using hk⟩
theorem trimmed_path_connected
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : K) (p : K.toSimpleGraph.Walk a b)
    (hS : (attachmentPositions G x identifier hfree K p).Nonempty) :
    (G.induce (↑(trimmedVertices G x identifier hfree K p hS) : Set V)).Connected := by
  classical
  let S := attachmentPositions G x identifier hfree K p
  let m := S.min' hS
  let M := S.max' hS
  let r := (p.drop m).take (M-m)
  have hsup := (trimmed_path_support G x identifier hfree K a b p hS).2.2
  change r.support.toFinset.image (fun v : K => v.val.val) = trimmedVertices G x identifier hfree K p hS at hsup
  let f : K.toSimpleGraph →g G := ⟨fun v => v.val.val, by intro v w hvw; exact hvw⟩
  have he : {u | u ∈ (r.map f).support} = (↑(trimmedVertices G x identifier hfree K p hS) : Set V) := by
    rw [←hsup]
    ext u
    simp only [Set.mem_setOf_eq, SimpleGraph.Walk.support_map, Finset.mem_coe, List.mem_map, f]
    simp [List.mem_toFinset]
  rw [←he]
  exact (r.map f).connected_induce_support

theorem trimmed_keeps_attachments
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hcover : ∀ z : C, z ∈ p.support)
    (hS : (attachmentPositions G x identifier hfree C p).Nonempty) :
    ∀ u ∈ componentMembers G x identifier hfree C, u ∈ attachments G x identifier hfree →
      u ∈ trimmedVertices G x identifier hfree C p hS := by
  classical
  intro u hu hA
  obtain ⟨huS,huC⟩ := (Finset.mem_filter.mp hu).2
  let z : C := ⟨⟨u,huS⟩,huC⟩
  obtain ⟨i,hiz,hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
  have he : (p.getVert i).val.val = u := congrArg (fun z : C => z.val.val) hiz
  have hiS : i ∈ attachmentPositions G x identifier hfree C p := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega),by simpa only [he] using hA⟩
  exact Finset.mem_image.mpr ⟨i,Finset.mem_Icc.mpr
    ⟨Finset.min'_le _ _ hiS,Finset.le_max' _ _ hiS⟩,he⟩

noncomputable def badCorrection : ℕ := by
  classical
  exact if Bad G x identifier hfree C then 2 else 0

theorem trimmed_size_bound
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (hS : (attachmentPositions G x identifier hfree C p).Nonempty) :
    (trimmedVertices G x identifier hfree C p hS).card+8 ≤
      7*(componentAttachmentPairs G x identifier hfree C).card + badCorrection G x identifier hfree C := by
  classical
  unfold badCorrection
  let S := attachmentPositions G x identifier hfree C p
  let m := S.min' hS
  let M := S.max' hS
  have hScount := attachment_positions_count G x identifier hfree C hC a b p hp hcover
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  have hminmax : m ≤ M := Finset.min'_le S _ (Finset.max'_mem S hS)
  have hminL : m ≤ p.length := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.min'_mem S hS)).1
    omega
  have hsize : (trimmedVertices G x identifier hfree C p hS).card ≤ M+1-m := by
    have hh : (trimmedVertices G x identifier hfree C p hS).card ≤ (Finset.Icc m M).card := Finset.card_image_le
    simpa only [Nat.card_Icc] using hh
  have hgap : ∀ i ∈ S, ∀ j ∈ S, i < j → (∀ k ∈ S, i < k → k < j → False) → j-i ≤ 7 := by
    intro i hi j hj hij hn
    have hjL : j ≤ p.length := by have hh := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega
    apply attachment_gap_le_seven G x identifier hfree C hC a b p hp hcover hgraph i j hij hjL
    intro k hik hkj hkA
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hkA⟩
    exact hn k hkS hik hkj
  have hspan := HighGirthSpan.span_of_gaps S hS hgap
  have hkq : S.card ≤ (componentAttachmentPairs G x identifier hfree C).card := hScount.2.2
  by_cases hBad : Bad G x identifier hfree C
  · simp only [if_pos hBad]
    change M ≤ m+7*(S.card-1) at hspan
    omega
  · simp only [if_neg hBad,Nat.add_zero]
    by_cases heq : S.card = (componentAttachmentPairs G x identifier hfree C).card
    · have hdistinct : Set.InjOn (fun q : V × V => q.1) (componentAttachmentPairs G x identifier hfree C) :=
        Finset.card_image_iff.mp (hScount.2.1.symm.trans heq)
      have htwo : 2 ≤ S.card := by
        have hn : S.card ≠ 1 := by
          intro hone
          apply hBad
          exact ⟨hC,⟨a,b,p,hp,hcover,hgraph⟩,Or.inl (by omega)⟩
        omega
      have hfirst : ∀ j ∈ S, S.min' hS < j →
          (∀ k ∈ S, S.min' hS < k → k < j → False) → j-S.min' hS ≤ 5 := by
        intro j hj hmj hn
        have hjL : j ≤ p.length := by have hh := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega
        apply first_gap_le_five_of_not_bad G x identifier hfree C hC a b p hp hcover hgraph hBad hdistinct
          (S.min' hS) j hmj hjL (Finset.mem_filter.mp (Finset.min'_mem S hS)).2 (Finset.mem_filter.mp hj).2
        · intro k hkm hkA
          have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hkA⟩
          have hh := Finset.min'_le S k hkS
          omega
        · intro k hmk hkj hkA
          have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hkA⟩
          exact hn k hkS hmk hkj
      have hshort := HighGirthSpan.span_of_short_first_gap S hS htwo hgap hfirst
      change M ≤ m+5+7*(S.card-2) at hshort
      omega
    · change M ≤ m+7*(S.card-1) at hspan
      omega

end Paper.TotalDomination.HighGirthSetup

#print axioms Paper.TotalDomination.HighGirthSetup.trimmed_size_bound
