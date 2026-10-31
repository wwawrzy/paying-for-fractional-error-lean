import Paper.Preliminaries.SmallParts

/-! Assemble a disjoint accepted family and a partition of the remaining
region. This constructs the output partition of the finite local process. -/
namespace Paper.PartAssembly
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def singletons (S : Finset V) (k : ℕ) (hk : 0 < k) : SmallParts.Data G S k := by
  classical
  refine {
    parts := S.image (fun v => {v})
    nonempty := ?_
    subset := ?_
    connected := ?_
    size := ?_
    disjoint := ?_
    covers := ?_ }
  · intro U hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hU
    exact Finset.singleton_nonempty v
  · intro U hU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
    exact Finset.singleton_subset_iff.mpr hv
  · intro U hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hU
    letI : Nonempty V := ⟨v⟩
    exact FiniteConnector.singleton_connected G v
  · intro U hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hU
    simpa only [Finset.card_singleton] using hk
  · intro U hU W hW hne
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hW
    apply Finset.disjoint_left.mpr
    intro w hwu hwv
    have he := (Finset.mem_singleton.mp hwu).symm.trans (Finset.mem_singleton.mp hwv)
    exact hne (congrArg (fun x : V => ({x} : Finset V)) he)
  · intro v hv
    exact ⟨{v}, Finset.mem_image.mpr ⟨v, hv, rfl⟩, Finset.mem_singleton_self _⟩

noncomputable def merge (S : Finset V) (k : ℕ) (A : Finset (Finset V))
    (hsub : ∀ U ∈ A, U ⊆ S) (hnonempty : ∀ U ∈ A, U.Nonempty)
    (hconn : ∀ U ∈ A, (G.induce (U : Set V)).Connected) (hsize : ∀ U ∈ A, U.card ≤ k)
    (hdis : (A : Set (Finset V)).Pairwise Disjoint)
    (P : SmallParts.Data G (S \ A.biUnion id) k) : SmallParts.Data G S k := by
  classical
  have hcross : ∀ U ∈ A, ∀ W ∈ P.parts, Disjoint U W := by
    intro U hU W hW
    apply Finset.disjoint_left.mpr
    intro v hvU hvW
    exact (Finset.mem_sdiff.mp (P.subset W hW hvW)).2 (Finset.mem_biUnion.mpr ⟨U, hU, hvU⟩)
  refine {
    parts := A ∪ P.parts
    nonempty := ?_
    subset := ?_
    connected := ?_
    size := ?_
    disjoint := ?_
    covers := ?_ }
  · intro U hU
    exact (Finset.mem_union.mp hU).elim (hnonempty U) (P.nonempty U)
  · intro U hU
    exact (Finset.mem_union.mp hU).elim (hsub U) (fun h => (P.subset U h).trans Finset.sdiff_subset)
  · intro U hU
    exact (Finset.mem_union.mp hU).elim (hconn U) (P.connected U)
  · intro U hU
    exact (Finset.mem_union.mp hU).elim (hsize U) (P.size U)
  · intro U hU W hW hne
    rcases Finset.mem_union.mp hU with hU | hU <;> rcases Finset.mem_union.mp hW with hW | hW
    · exact hdis hU hW hne
    · exact hcross U hU W hW
    · exact (hcross W hW U hU).symm
    · exact P.disjoint hU hW hne
  · intro v hv
    by_cases hremoved : v ∈ A.biUnion id
    · obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hremoved
      exact ⟨U, Finset.mem_union_left _ hU, hv⟩
    · obtain ⟨U, hU, hvU⟩ := P.covers v (Finset.mem_sdiff.mpr ⟨hv, hremoved⟩)
      exact ⟨U, Finset.mem_union_right _ hU, hvU⟩
end Paper.PartAssembly
