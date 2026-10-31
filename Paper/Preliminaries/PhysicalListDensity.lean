import Paper.Preliminaries.IncidenceRoles
import Paper.Preliminaries.BoundedLists
import Paper.Initialization.Pruning.InitializerPass

/-! Derive the entire incidence-density hierarchy from the physical graph.
Distinct derived sets assigned to one demand are distinct subsets of its
original short list, so require at most 2^f local set roles. -/
namespace Paper.PhysicalListDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem family_density (Λ : V → Finset V) (f : ℕ) (H : Finset (Finset V))
    (hsource : ∀ C ∈ H, ∃ r, C ⊆ Λ r ∧ (Λ r).card ≤ f)
    (hclosed : ∀ r v, v ∈ Λ r → v = r ∨ G.Adj v r)
    {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a) :
    DepthOne.Bound (CoreIncidence.graph H)
      (a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ)) := by
  classical
  let origin := fun C : H => (hsource C.val C.property).choose
  have horigin : ∀ C : H, C.val ⊆ Λ (origin C) ∧ (Λ (origin C)).card ≤ f := fun C =>
    (hsource C.val C.property).choose_spec
  have hfib : ∀ v, Fintype.card {C : H // origin C = v} ≤ 2 ^ f := by
    intro v
    by_cases hn : Nonempty {C : H // origin C = v}
    · obtain ⟨C⟩ := hn
      have hcard : (Λ v).card ≤ f := by simpa only [C.property] using (horigin C.val).2
      let g : {C : H // origin C = v} → (Λ v).powerset := fun C =>
        ⟨C.val.val, Finset.mem_powerset.mpr (by simpa only [C.property] using (horigin C.val).1)⟩
      have hinj : Function.Injective g := by
        intro C D he
        exact Subtype.ext (Subtype.ext (congrArg (fun s : (Λ v).powerset => s.val) he))
      have hh := Fintype.card_le_of_injective g hinj
      have hh' : Fintype.card {C : H // origin C = v} ≤ 2 ^ (Λ v).card := by
        simpa only [Fintype.card_coe, Finset.card_powerset] using hh
      exact hh'.trans (Nat.pow_le_pow_right (by omega) hcard)
    · haveI : IsEmpty {C : H // origin C = v} := ⟨fun C => hn ⟨C⟩⟩
      simp
  exact IncidenceRoles.density G H origin (2 ^ f) hfib
    (fun C v hv => hclosed (origin C) v ((horigin C).1 hv)) hden ha

theorem bound_mono {H : SimpleGraph V} [DecidableRel H.Adj] {a b : ℝ}
    (h : DepthOne.Bound H a) (hab : a ≤ b) : DepthOne.Bound H b := by
  intro A _ _ J _ M
  exact (h A J M).trans (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))

theorem hierarchy (Λ : V → Finset V) (f b : ℕ) (hb : 1 ≤ b)
    (hclosed : ∀ r v, v ∈ Λ r → v = r ∨ G.Adj v r)
    {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (j : ℕ) (H : Finset (Finset V))
    (hsource : ∀ C ∈ H, ∃ r, C ⊆ Λ r ∧ (Λ r).card ≤ f) :
    BoundedLists.densityHierarchy H b j := by
  induction j generalizing H with
  | zero => trivial
  | succ j ih =>
    refine ⟨?_, ih _ ?_⟩
    · have hh := family_density G Λ f H hsource hclosed hden ha
      intro A _ _ J _ M
      exact (hh A J M).trans (mul_le_mul_of_nonneg_right hba (Nat.cast_nonneg _))
    · intro C hC
      obtain ⟨s, hs, hCs⟩ := CoreHierarchy.core_subset_original H (2 * b) (by omega) hC
      obtain ⟨r, hr, hf⟩ := hsource s hs
      exact ⟨r, hCs.trans hr, hf⟩

theorem actual_lists (h f b : ℕ) (hb : 1 ≤ b) (R : Finset V)
    {a : ℝ} (hden : DepthOne.Bound G a) (ha : 0 ≤ a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b) :
    BoundedLists.densityHierarchy (InitializerPass.lists G h f R) b f := by
  apply hierarchy G (InitializerPass.eligibleList G h R) f b hb _ hden ha hba f
  · intro C hC
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨r, Finset.Subset.refl _, (Finset.mem_filter.mp hr).2.1⟩
  · intro r v hv
    have hc := (Finset.mem_inter.mp hv).1
    exact ((SevenFoundation.mem_closed G v r).mp hc).elim Or.inl (fun ha => Or.inr ha.symm)
end Paper.PhysicalListDensity
