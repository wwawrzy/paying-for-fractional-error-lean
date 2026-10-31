import Paper.Solver.LocalSearch.GeneralCoveringInitializerPassLists
import Paper.Solver.LocalSearch.GeneralCoveringRequests
import Paper.Endpoints.Rounding.CoreSelectionCorrect
import Paper.Preliminaries.ListSupport
import Paper.Preliminaries.PhysicalListDensity

/-! One concrete arbitrary-covering initializer pass. All global sets below
are mathematical interpretations of the private protocol input. The program
computes its own eligibility/list data, runs the real bounded-list/core cover,
and uses the accepted request protocol for empty Lambda rows. -/
namespace Paper.GeneralCoveringInitializerPass
open BroadcastModel SevenFoundation GeneralCoveringInitializerPassLists
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringInitializerPassLists.Input

def prepareCore : Program V (Data V) (Finset V × Data V) :=
  .local fun _ _ s => (s.hosted, s)

def requestInput (chosen : Bool) (s : Data V) : GeneralCoveringRequests.Input V :=
  ⟨chosen, s.empty, s.input.residual, s.input.candidates⟩

def finishCore : Program V (Bool × Data V) (GeneralCoveringRequests.Input V) :=
  .local fun _ _ s => requestInput s.1 s.2

def program {bits : ℕ} (ids : BitCode V bits) (b h f : ℕ) :
    Program V (Input V) GeneralCoveringRequests.Output :=
  .seq (GeneralCoveringInitializerPassLists.program h f)
    (.seq prepareCore (.seq (ProgramMemory.carry (CoreSelectionBroadcast.program ids f (2 * b)))
      (.seq finishCore (GeneralCoveringRequests.program ids))))

variable [Fintype V]

theorem rounds {bits : ℕ} (ids : BitCode V bits) (b h f : ℕ) :
    (program ids b h f).rounds = 5 + 2 * f := by
  simp only [program, prepareCore, finishCore, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringInitializerPassLists.rounds, CoreSelectionBroadcast.rounds,
    GeneralCoveringRequests.rounds]
  omega

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (b h f : ℕ) :
    (program ids b h f).maxBits ≤ max (bits + 1) (f * (bits + 1)) := by
  have hc := CoreSelectionBroadcast.maxBits ids f (2 * b)
  have hr := GeneralCoveringRequests.maxBits ids
  simp only [program, prepareCore, finishCore, Program.maxBits, ProgramMemory.maxBits,
    GeneralCoveringInitializerPassLists.maxBits, Nat.zero_max]
  apply max_le
  · exact (by omega : 1 ≤ bits + 1).trans (le_max_left _ _)
  · apply max_le
    · exact hc.trans (max_le
        ((by omega : 1 ≤ bits + 1).trans (le_max_left _ _)) (le_max_right _ _))
    · exact hr.trans (le_max_left _ _)

noncomputable def core (C : V → Finset V) (b h f : ℕ) (R : Finset V) : Finset V :=
  BoundedLists.cover (lists C h f R) (2 * b) f

noncomputable def selected (C : V → Finset V) (b h f : ℕ) (R : Finset V) : Finset V :=
  GeneralCoveringRequests.selectedPlus C (core C b h f R) (emptyLists C h R)

noncomputable def residual (C : V → Finset V) (b h f : ℕ) (R : Finset V) : Finset V :=
  GeneralCoveringRequests.residual C R (core C b h f R) (emptyLists C h R)

/-- Integral competitors cover actual C(r), not physical neighborhoods. -/
def Covers (C : V → Finset V) (R O : Finset V) : Prop :=
  ∀ r ∈ R, ∃ o ∈ O, o ∈ C r

def served (C : V → Finset V) (R O : Finset V) : Finset V :=
  O.biUnion (inverse C R)

theorem core_support (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b) (R : Finset V)
    {v : V} (hv : v ∈ core C b h f R) :
    ∃ r ∈ R, v ∈ eligibleList C h R r := by
  obtain ⟨t, ht, hvt⟩ := ListSupport.cover_support (lists C h f R) (2 * b) (by omega) f v hv
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨r, (Finset.mem_filter.mp hr).1, hvt⟩

theorem core_admissible (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b) (R : Finset V) :
    core C b h f R ⊆ CoveringSupport.admissible C R := by
  intro v hv
  obtain ⟨r, hr, hvr⟩ := core_support C b h f hb R hv
  exact Finset.mem_biUnion.mpr ⟨r, hr, (Finset.mem_inter.mp hvr).1⟩

theorem selected_admissible (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b) (R : Finset V) :
    selected C b h f R ⊆ CoveringSupport.admissible C R :=
  GeneralCoveringRequests.admissible C R (core C b h f R) (emptyLists C h R)
    (empty_subset C h R) (core_admissible C b h f hb R)

theorem small_covered (C : V → Finset V) (b h f : ℕ) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) {r : V} (hr : r ∈ R)
    (hsmall : (eligibleList C h R r).card ≤ f) :
    ∃ v ∈ selected C b h f R, v ∈ C r := by
  by_cases hn : (eligibleList C h R r).Nonempty
  · have ht : eligibleList C h R r ∈ lists C h f R :=
      Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hsmall, hn⟩, rfl⟩
    obtain ⟨v, hv⟩ := ListSupport.cover_hits (lists C h f R) (2 * b) f
      (lists_rank C h f R) (lists_nonempty C h f R) _ ht
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst] at hv
    obtain ⟨hvl, hvc⟩ := Finset.mem_inter.mp hv
    exact ⟨v, GeneralCoveringRequests.selected_subset C _ _ hvc, (Finset.mem_inter.mp hvl).1⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    exact GeneralCoveringRequests.covers_requesters C (core C b h f R) (emptyLists C h R)
      (fun u hu => hrows u ((empty_subset C h R) hu)) r
      (Finset.mem_filter.mpr ⟨hr, he⟩)

theorem coverage_count (C : V → Finset V) (h : ℕ) (R O : Finset V)
    (hsmall : ∀ o ∈ O, (inverse C R o).card ≤ h) :
    (served C R O).card ≤ h * O.card := by
  calc
    _ ≤ ∑ o ∈ O, (inverse C R o).card := Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ O, h := Finset.sum_le_sum hsmall
    _ = _ := by simp [mul_comm]

theorem ineligible_count (C : V → Finset V) (h : ℕ) (R O : Finset V) :
    (served C R (O \ eligible C h R)).card ≤ h * (O \ eligible C h R).card := by
  apply coverage_count C h
  intro o ho
  have hn := (Finset.mem_sdiff.mp ho).2
  have hh : ¬ h < (inverse C R o).card := by
    intro hc
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  omega

theorem assigned_ineligible (C : V → Finset V) (h : ℕ) (R O : Finset V)
    (hO : Covers C R O) {r : V} (hr : r ∈ R)
    (hdis : Disjoint (eligibleList C h R r) (O ∩ eligible C h R)) :
    r ∈ served C R (O \ eligible C h R) := by
  obtain ⟨o, ho, hor⟩ := hO r hr
  have hone : o ∉ eligible C h R := by
    intro he
    have hol : o ∈ eligibleList C h R r := Finset.mem_inter.mpr ⟨hor, he⟩
    exact Finset.disjoint_left.mp hdis hol (Finset.mem_inter.mpr ⟨ho, he⟩)
  exact Finset.mem_biUnion.mpr ⟨o, Finset.mem_sdiff.mpr ⟨ho, hone⟩,
    Finset.mem_filter.mpr ⟨hr, hor⟩⟩

theorem empty_count (C : V → Finset V) (h : ℕ) (R O : Finset V) (hO : Covers C R O) :
    (emptyLists C h R).card ≤ h * O.card := by
  have hs : emptyLists C h R ⊆ served C R (O \ eligible C h R) := by
    intro r hr
    obtain ⟨hrR, he⟩ := Finset.mem_filter.mp hr
    exact assigned_ineligible C h R O hO hrR (by rw [he]; simp)
  exact (Finset.card_le_card hs).trans ((ineligible_count C h R O).trans
    (Nat.mul_le_mul_left h (Finset.card_le_card Finset.sdiff_subset)))

theorem list_benchmark (C : V → Finset V) (h f : ℕ) (hh : 1 ≤ h)
    (R O : Finset V) (hO : Covers C R O) :
    ∃ D : Finset V, (∀ t ∈ lists C h f R, (t ∩ D).Nonempty) ∧ D.card ≤ h * O.card := by
  let E := O ∩ eligible C h R
  let A := (listed C h f R).filter (fun r => Disjoint (eligibleList C h R r) E)
  have hAn : ∀ r : A, (eligibleList C h R r.val).Nonempty := fun r =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2.2
  let pick := fun r : A => (eligibleList C h R r.val).min' (hAn r)
  let D := E ∪ Finset.univ.image pick
  have hAc : A.card ≤ h * (O \ eligible C h R).card := by
    have hs : A ⊆ served C R (O \ eligible C h R) := by
      intro r hr
      obtain ⟨hrl, hd⟩ := Finset.mem_filter.mp hr
      exact assigned_ineligible C h R O hO (Finset.mem_filter.mp hrl).1 hd
    exact (Finset.card_le_card hs).trans (ineligible_count C h R O)
  refine ⟨D, ?_, ?_⟩
  · intro t ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    by_cases hd : Disjoint (eligibleList C h R r) E
    · let r' : A := ⟨r, Finset.mem_filter.mpr ⟨hr, hd⟩⟩
      exact ⟨pick r', Finset.mem_inter.mpr ⟨Finset.min'_mem _ _,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r', Finset.mem_univ _, rfl⟩)⟩⟩
    · obtain ⟨v, hvl, hvE⟩ := Finset.not_disjoint_iff.mp hd
      exact ⟨v, Finset.mem_inter.mpr ⟨hvl, Finset.mem_union_left _ hvE⟩⟩
  · have hDc : D.card ≤ E.card + A.card := by
      apply (Finset.card_union_le _ _).trans
      have hi := Finset.card_image_le (s := Finset.univ) (f := pick)
      simpa using Nat.add_le_add_left hi E.card
    have hp := Finset.card_inter_add_card_sdiff O (eligible C h R)
    have hm := Nat.mul_le_mul_right E.card hh
    change E.card + (O \ eligible C h R).card = O.card at hp
    nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem candidate_neighbors (C : V → Finset V) (h : ℕ) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {v : V} (hv : v ∈ eligible C h R) :
    h ≤ ((G.neighborFinset v) ∩ R).card := by
  have hc := Finset.card_le_card (inverse_local G C R hlocal v)
  have hb := InitializerPass.closed_inter_card G R v
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hb
  have hh := (Finset.mem_filter.mp hv).2
  omega

theorem surviving_neighbors (C : V → Finset V) (b h f : ℕ) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    {r : V} (hr : r ∈ residual C b h f R) :
    f ≤ ((G.neighborFinset r) ∩ eligible C h R).card := by
  obtain ⟨hrR, he⟩ := Finset.mem_filter.mp hr
  have hn : ¬ (eligibleList C h R r).card ≤ f := by
    intro hs
    obtain ⟨v, hvS, hvC⟩ := small_covered C b h f R hrows hrR hs
    exact (Finset.nonempty_iff_ne_empty.mp ⟨v, Finset.mem_inter.mpr ⟨hvC, hvS⟩⟩) he
  have hsub : eligibleList C h R r ⊆ closed G r ∩ eligible C h R := by
    intro v hv
    obtain ⟨hvC, hvE⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨hlocal r hrR hvC, hvE⟩
  have hc := Finset.card_le_card hsub
  have hb := InitializerPass.closed_inter_card G (eligible C h R) r
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hb
  omega

theorem removed_physically_covered (C : V → Finset V) (b h f : ℕ) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    R \ residual C b h f R ⊆ covered G (selected C b h f R) := by
  intro r hr
  obtain ⟨hrR, hnot⟩ := Finset.mem_sdiff.mp hr
  have hn : C r ∩ selected C b h f R ≠ ∅ := by
    intro he
    exact hnot (Finset.mem_filter.mpr ⟨hrR, he⟩)
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hn
  obtain ⟨hvC, hvS⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_biUnion.mpr ⟨v, hvS, (closed_symm G r v).mpr (hlocal r hrR hvC)⟩

/-- Derive the actual hosted-list hierarchy from physical minor density.
No hierarchy, core cover or family is supplied as a runtime oracle. -/
theorem density_hierarchy (C : V → Finset V) (h f b : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b) :
    BoundedLists.densityHierarchy (lists C h f R) b f := by
  apply PhysicalListDensity.hierarchy G (hosted C h f R) f b hb ?_
    (DepthOne.bound_of_minor_density G hden) ha hba f _ ?_
  · intro r v hv
    exact ((mem_closed G v r).mp (hosted_local G C h f R hlocal r hv)).elim
      Or.inl (fun ha => Or.inr ha.symm)
  · intro t ht
    have ht' : t ∈ ListIncidenceBroadcast.family (hosted C h f R) := by
      rw [family_eq C h f R]
      exact ht
    obtain ⟨_, r, he⟩ := (ListIncidenceBroadcast.mem_family _ t).mp ht'
    refine ⟨r, ?_, hosted_bound C h f R r⟩
    rw [he]

theorem pass_cost (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b) (hh : 1 ≤ h)
    (R O : Finset V) (hO : Covers C R O) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b) :
    (selected C b h f R).card ≤ h * (BoundedLists.factor (2 * b) f + 1) * O.card := by
  obtain ⟨D, hD, hDc⟩ := list_benchmark C h f hh R O hO
  have hd := density_hierarchy G C h f b hb R hlocal ha hden hba
  have hcover := BoundedLists.cover_spec (lists C h f R) b hb f
    (lists_rank C h f R) (lists_nonempty C h f R) hd D
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hcover
  have hcore := (hcover hD).2
  have he := empty_count C h R O hO
  have hreq := GeneralCoveringRequests.requested_card C (emptyLists C h R)
  have hu := Finset.card_union_le (core C b h f R) (GeneralCoveringRequests.requested C (emptyLists C h R))
  have hm := Nat.mul_le_mul_left (BoundedLists.factor (2 * b) f) hDc
  change (selected C b h f R).card ≤ _ at hu
  change (core C b h f R).card ≤ _ at hcore
  nlinarith

/-- Evaluate the private list/core stages while preserving all own input data. -/
theorem run_program {bits : ℕ} (ids : BitCode V bits) (b h f : ℕ) (s : V → Input V) :
    (program ids b h f).run G s = (GeneralCoveringRequests.program ids).run G
      (fun v => requestInput
        ((CoreSelectionBroadcast.program ids f (2 * b)).run G
          (fun u => ((GeneralCoveringInitializerPassLists.program h f).run G s u).hosted) v)
        ((GeneralCoveringInitializerPassLists.program h f).run G s v)) := by
  change (GeneralCoveringRequests.program ids).run G
    (finishCore.run G ((ProgramMemory.carry (CoreSelectionBroadcast.program ids f (2 * b))).run G
      (prepareCore.run G ((GeneralCoveringInitializerPassLists.program h f).run G s)))) = _
  rw [ProgramMemory.run]
  rfl

/-- Exact mathematical selection and residual for the literal composed pass. -/
theorem correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) :
    (program ids b h f).run G s = fun v =>
      ⟨decide (v ∈ selected C b h f R), decide (v ∈ residual C b h f R)⟩ := by
  rw [run_program, GeneralCoveringInitializerPassLists.correct G C targets h f R hinc hlocal s hR hC hT]
  have hc := CoreSelectionCorrect.correct G ids f (2 * b) (by omega)
    (hosted C h f R) (hosted_bound C h f R) (hosted_local G C h f R hlocal)
  rw [family_eq C h f R] at hc
  dsimp only
  rw [hc]
  exact GeneralCoveringRequests.correct G ids C R (core C b h f R) (emptyLists C h R)
    (fun v => requestInput (decide (v ∈ core C b h f R))
      ⟨s v, hosted C h f R v, decide (v ∈ emptyLists C h R)⟩)
    (fun _ => rfl) (fun _ => rfl) hR hC (empty_subset C h R) hlocal

def output {bits : ℕ} (ids : BitCode V bits) (b h f : ℕ) (s : V → Input V) : Finset V :=
  Finset.univ.filter (fun v => ((program ids b h f).run G s v).selected = true)

theorem output_eq {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f : ℕ) (hb : 1 ≤ b) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) :
    output G ids b h f s = selected C b h f R := by
  unfold output
  rw [correct G ids C targets b h f hb R hinc hlocal s hR hC hT]
  ext v
  simp

/-- Guarantees of the actual pass against any integral C-cover O. The
hierarchy is derived inside pass_cost from physical minor density. -/
theorem spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f : ℕ) (hb : 1 ≤ b) (hh : 1 ≤ h) (R O : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v)
    (hO : Covers C R O) {a : ℝ} (ha : 0 ≤ a) (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b) :
    output G ids b h f s ⊆ CoveringSupport.admissible C R ∧
      (output G ids b h f s).card ≤ h * (BoundedLists.factor (2 * b) f + 1) * O.card ∧
      ∀ r ∈ R, (eligibleList C h R r).card ≤ f →
        ∃ v ∈ output G ids b h f s, v ∈ C r := by
  rw [output_eq G ids C targets b h f hb R hinc hlocal s hR hC hT]
  refine ⟨selected_admissible C b h f hb R,
    pass_cost G C b h f hb hh R O hO hlocal ha hden hba, ?_⟩
  have hrows : ∀ r ∈ R, (C r).Nonempty := by
    intro r hr
    obtain ⟨v, _, hv⟩ := hO r hr
    exact ⟨v, hv⟩
  intro r hr hs
  exact small_covered C b h f R hrows hr hs

end Paper.GeneralCoveringInitializerPass

#print axioms Paper.GeneralCoveringInitializerPass.correct
#print axioms Paper.GeneralCoveringInitializerPass.output_eq
#print axioms Paper.GeneralCoveringInitializerPass.small_covered
#print axioms Paper.GeneralCoveringInitializerPass.candidate_neighbors
#print axioms Paper.GeneralCoveringInitializerPass.surviving_neighbors
#print axioms Paper.GeneralCoveringInitializerPass.removed_physically_covered
#print axioms Paper.GeneralCoveringInitializerPass.selected_admissible
#print axioms Paper.GeneralCoveringInitializerPass.density_hierarchy
#print axioms Paper.GeneralCoveringInitializerPass.pass_cost
#print axioms Paper.GeneralCoveringInitializerPass.rounds
#print axioms Paper.GeneralCoveringInitializerPass.maxBits

#print axioms Paper.GeneralCoveringInitializerPass.spec
