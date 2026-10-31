import Paper.Preliminaries.ForestRegions
import Paper.Preliminaries.CoreMinorCounting
import Paper.Preliminaries.MinorDensity

/-! Contract actual connected ancestor regions and keep selected vertices
as singleton branch sets. The resulting bipartite graph is a genuine minor. -/
namespace Paper.RegionMinor
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (parent : V → Option V) (rank : V → ℕ)
variable (decrease : ∀ u v, parent u = some v → rank v < rank u)

def graph (X Q S : Finset V) : SimpleGraph (Q ⊕ S) where
  Adj a b := match a, b with
    | .inl x, .inr s => ∃ v, ForestRegions.owner parent rank decrease X v = some x.val ∧ G.Adj v s.val
    | .inr s, .inl x => ∃ v, ForestRegions.owner parent rank decrease X v = some x.val ∧ G.Adj v s.val
    | _, _ => False
  symm := by intro a b; cases a <;> cases b <;> exact id
  loopless := ⟨by intro a; cases a <;> exact id⟩

def branch (X Q S : Finset V) : Q ⊕ S → Set V
  | .inl x => {v | ForestRegions.owner parent rank decrease X v = some x.val}
  | .inr s => {s.val}

noncomputable def model (X Q S : Finset V) (hQ : Q ⊆ X)
    (hsub : ParentForest.graph parent rank decrease ≤ G)
    (havoid : ∀ x ∈ Q, ∀ s ∈ S, ForestRegions.owner parent rank decrease X s ≠ some x) :
    SimpleGraph.MinorModel (graph G parent rank decrease X Q S) G where
  branchSet := branch parent rank decrease X Q S
  nonempty a := by
    cases a with
    | inl x => exact ⟨x.val, ForestRegions.owner_center _ _ _ X (hQ x.property)⟩
    | inr s => exact ⟨s.val, rfl⟩
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v ha hb
    cases a with
    | inl x =>
      cases b with
      | inl y => exact hab (congrArg Sum.inl (Subtype.ext (Option.some.inj (ha.symm.trans hb))))
      | inr s =>
        change v = s.val at hb
        subst v
        exact havoid x.val x.property s.val s.property ha
    | inr s =>
      change v = s.val at ha
      subst v
      cases b with
      | inl x => exact havoid x.val x.property s.val s.property hb
      | inr t => exact hab (congrArg Sum.inr (Subtype.ext hb))
  connected a := by
    cases a with
    | inl x =>
      have hh : (ParentForest.graph parent rank decrease).induce
          {v | ForestRegions.owner parent rank decrease X v = some x.val} ≤
          G.induce {v | ForestRegions.owner parent rank decrease X v = some x.val} :=
        fun _ _ h => hsub h
      exact SimpleGraph.Connected.mono hh
        (ForestRegions.connected parent rank decrease X (hQ x.property))
    | inr s =>
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨s.val, rfl⟩, ?_⟩
      intro v
      have he : (⟨s.val, rfl⟩ : {v // v ∈ branch parent rank decrease X Q S (.inr s)}) = v :=
        Subtype.ext v.property.symm
      rw [he]
  adjacent a b hab := by
    cases a with
    | inl x =>
      cases b with
      | inl y => exact False.elim hab
      | inr s => obtain ⟨v, hv, ha⟩ := hab; exact ⟨v, hv, s.val, rfl, ha⟩
    | inr s =>
      cases b with
      | inl x => obtain ⟨v, hv, ha⟩ := hab; exact ⟨s.val, rfl, v, hv, ha.symm⟩
      | inr t => exact False.elim hab

theorem count {a : ℝ} (hden : MinorDensity.Bound G a)
    (X Q S : Finset V) (hQ : Q ⊆ X)
    (hsub : ParentForest.graph parent rank decrease ≤ G)
    (havoid : ∀ x ∈ Q, ∀ s ∈ S, ForestRegions.owner parent rank decrease X s ≠ some x)
    (T : ℕ) (htouch : ∀ x ∈ Q, T ≤ (S.filter (fun s => ∃ v,
      ForestRegions.owner parent rank decrease X v = some x ∧ G.Adj v s)).card) :
    ((T : ℝ) - a) * Q.card ≤ a * S.card := by
  classical
  let K := graph G parent rank decrease X Q S
  let L : Finset (Q ⊕ S) := Finset.univ.image Sum.inl
  let W : Finset (Q ⊕ S) := Finset.univ.image Sum.inr
  have hdis : Disjoint L W := by
    apply Finset.disjoint_left.mpr
    rintro v hv hw
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨s, _, he⟩ := Finset.mem_image.mp hw
    cases he
  have hdeg : ∀ r ∈ L, T ≤ (W.filter (K.Adj r)).card := by
    intro r hr
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hr
    let D := S.filter (fun s => ∃ v,
      ForestRegions.owner parent rank decrease X v = some x.val ∧ G.Adj v s)
    let Ds := D.subtype (fun s => s ∈ S)
    have hc : Ds.card = D.card := StarCounting.subtype_card S D (Finset.filter_subset ..)
    have hs : Ds.image (Sum.inr : S → Q ⊕ S) ⊆ W.filter (K.Adj (.inl x)) := by
      intro r hr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩, ?_⟩
      exact (Finset.mem_filter.mp (Finset.mem_subtype.mp hs)).2
    have hd := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ Sum.inr_injective, hc] at hd
    exact (htouch x.val x.property).trans hd
  have hminor : SimpleGraph.IsMinor K G := ⟨model G parent rank decrease X Q S hQ hsub havoid⟩
  have hh := CoreMinorCounting.cross_degree_count K
    (MinorDensity.minor_induced_bound G K hden hminor) L W hdis T hdeg
  have hLc : L.card = Q.card := by simp [L, Finset.card_image_of_injective, Sum.inl_injective]
  have hWc : W.card = S.card := by simp [W, Finset.card_image_of_injective, Sum.inr_injective]
  simpa only [hLc, hWc] using hh
end Paper.RegionMinor
