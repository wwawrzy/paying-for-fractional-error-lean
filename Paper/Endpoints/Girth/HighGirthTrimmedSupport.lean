import Paper.Endpoints.Girth.HighGirthTrimmedSize
set_option maxHeartbeats 200000
namespace Paper.HighGirthTrimmedSupport
theorem trimmed_path_support
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (a b : K) (p : K.toSimpleGraph.Walk a b)
    (hS : (Paper.HighGirthAttachmentPositions.positions G x K p).Nonempty) :
    let S := Paper.HighGirthAttachmentPositions.positions G x K p
    let m := S.min' hS
    let M := S.max' hS
    (Paper.HighGirthTrimmedPath.vertices G x K p hS).Nonempty ∧
    Paper.HighGirthTrimmedPath.vertices G x K p hS ⊆ Paper.HighGirthFreePaths.members G x K ∧
    (((p.drop m).take (M - m)).support.toFinset.image (fun v : K => v.val.val)) =
      Paper.HighGirthTrimmedPath.vertices G x K p hS := by
  classical
  dsimp only
  let S := Paper.HighGirthAttachmentPositions.positions G x K p
  let m := S.min' hS
  let M := S.max' hS
  change (Paper.HighGirthTrimmedPath.vertices G x K p hS).Nonempty ∧
    Paper.HighGirthTrimmedPath.vertices G x K p hS ⊆ Paper.HighGirthFreePaths.members G x K ∧
    (((p.drop m).take (M-m)).support.toFinset.image (fun v : K => v.val.val)) =
      Paper.HighGirthTrimmedPath.vertices G x K p hS
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
end Paper.HighGirthTrimmedSupport
#print axioms Paper.HighGirthTrimmedSupport.trimmed_path_support
