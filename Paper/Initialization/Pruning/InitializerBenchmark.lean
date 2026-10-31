import Paper.Initialization.Pruning.InitializerPass

/-! Actual short-list and empty-list benchmarks from any integral cover O.
Ineligible vertices cover at most h current demands. -/
namespace Paper.InitializerBenchmark
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem coverage_count (h : ℕ) (R O : Finset V)
    (hsmall : ∀ o ∈ O, ((closed G o) ∩ R).card ≤ h) :
    (R ∩ covered G O).card ≤ h * O.card := by
  have he : R ∩ covered G O = O.biUnion (fun o => (closed G o) ∩ R) := by
    ext v
    simp only [covered, Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [he]
  calc
    _ ≤ ∑ o ∈ O, ((closed G o) ∩ R).card := Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ O, h := Finset.sum_le_sum hsmall
    _ = _ := by simp [mul_comm]

theorem ineligible_count (h : ℕ) (R O : Finset V) :
    (R ∩ covered G (O \ candidates G h R)).card ≤ h * (O \ candidates G h R).card := by
  apply coverage_count G h
  intro o ho
  have hn := (Finset.mem_sdiff.mp ho).2
  have hh : ¬ h < ((closed G o) ∩ R).card := by
    intro hc
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  omega

theorem assigned_ineligible (h : ℕ) (R O : Finset V) (hO : R ⊆ covered G O) {v : V}
    (hv : v ∈ R) (hdis : Disjoint (eligibleList G h R v) (O ∩ candidates G h R)) :
    v ∈ covered G (O \ candidates G h R) := by
  obtain ⟨o, ho, hvo⟩ := Finset.mem_biUnion.mp (hO hv)
  have hoc : o ∉ candidates G h R := by
    intro hc
    have hol : o ∈ eligibleList G h R v := Finset.mem_inter.mpr ⟨(closed_symm G v o).mp hvo, hc⟩
    exact Finset.disjoint_left.mp hdis hol (Finset.mem_inter.mpr ⟨ho, hc⟩)
  exact Finset.mem_biUnion.mpr ⟨o, Finset.mem_sdiff.mpr ⟨ho, hoc⟩, hvo⟩

theorem empty_count (h : ℕ) (R O : Finset V) (hO : R ⊆ covered G O) :
    (emptyLists G h R).card ≤ h * O.card := by
  have hs : emptyLists G h R ⊆ R ∩ covered G (O \ candidates G h R) := by
    intro v hv
    have hm := Finset.mem_filter.mp hv
    exact Finset.mem_inter.mpr ⟨hm.1, assigned_ineligible G h R O hO hm.1
      (by rw [hm.2]; simp)⟩
  exact (Finset.card_le_card hs).trans ((ineligible_count G h R O).trans
    (Nat.mul_le_mul_left h (Finset.card_le_card Finset.sdiff_subset)))

theorem list_benchmark (h f : ℕ) (hh : 1 ≤ h) (R O : Finset V) (hO : R ⊆ covered G O) :
    ∃ D : Finset V, (∀ s ∈ lists G h f R, (s ∩ D).Nonempty) ∧ D.card ≤ h * O.card := by
  classical
  let E := O ∩ candidates G h R
  let A := (listed G h f R).filter (fun v => Disjoint (eligibleList G h R v) E)
  have hAn : ∀ v : A, (eligibleList G h R v.val).Nonempty := fun v =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp v.property).1).2.2
  let pick := fun v : A => (eligibleList G h R v.val).min' (hAn v)
  let D := E ∪ Finset.univ.image pick
  have hAc : A.card ≤ h * (O \ candidates G h R).card := by
    have hs : A ⊆ R ∩ covered G (O \ candidates G h R) := by
      intro v hv
      have hm := Finset.mem_filter.mp hv
      have hvR := (Finset.mem_filter.mp hm.1).1
      exact Finset.mem_inter.mpr ⟨hvR, assigned_ineligible G h R O hO hvR hm.2⟩
    exact (Finset.card_le_card hs).trans (ineligible_count G h R O)
  refine ⟨D, ?_, ?_⟩
  · intro s hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    by_cases hd : Disjoint (eligibleList G h R v) E
    · let v' : A := ⟨v, Finset.mem_filter.mpr ⟨hv, hd⟩⟩
      exact ⟨pick v', Finset.mem_inter.mpr ⟨Finset.min'_mem _ _,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v', Finset.mem_univ _, rfl⟩)⟩⟩
    · obtain ⟨u, hul, huE⟩ := Finset.not_disjoint_iff.mp hd
      exact ⟨u, Finset.mem_inter.mpr ⟨hul, Finset.mem_union_left _ huE⟩⟩
  · have hDc : D.card ≤ E.card + A.card := by
      apply (Finset.card_union_le _ _).trans
      have hi := Finset.card_image_le (s := Finset.univ) (f := pick)
      simpa using Nat.add_le_add_left hi E.card
    have hp := Finset.card_inter_add_card_sdiff O (candidates G h R)
    have hm := Nat.mul_le_mul_right E.card hh
    change E.card + (O \ candidates G h R).card = O.card at hp
    nlinarith

theorem pass_cost (a h f : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) (R O : Finset V)
    (hO : R ⊆ covered G O) (hden : BoundedLists.densityHierarchy (lists G h f R) a f) :
    (selected G a h f R).card ≤ h * (BoundedLists.factor (2 * a) f + 1) * O.card := by
  obtain ⟨D, hD, hDc⟩ := list_benchmark G h f hh R O hO
  have hc := (BoundedLists.cover_spec (lists G h f R) a ha f
    (lists_rank G h f R) (lists_nonempty G h f R) hden D hD).2
  have he := empty_count G h R O hO
  have hu := Finset.card_union_le (BoundedLists.cover (lists G h f R) (2 * a) f) (emptyLists G h R)
  have hm := Nat.mul_le_mul_left (BoundedLists.factor (2 * a) f) hDc
  change (selected G a h f R).card ≤ _ at hu
  nlinarith
end Paper.InitializerBenchmark
