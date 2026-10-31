import Paper.Preliminaries.FlagNeighborhood
import Paper.Communication.ListIncidenceBroadcast

/-! The two real flag broadcasts at the start of a general-covering pass.
A candidate filters received residual bits through its private targets. A
residual demand filters received eligibility bits through its private C(r).
Only bounded hosted lists are later supplied to CoreSelectionBroadcast. -/
namespace Paper.GeneralCoveringInitializerPassLists
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

structure Input (V : Type) where
  residual : Bool
  candidates : Finset V
  targets : Finset V

structure Data (V : Type) where
  input : Input V
  hosted : Finset V
  empty : Bool

def candidateRound (h : ℕ) : Round V (Input V) (Input V × Bool) Bool where
  send _ _ s := s.residual
  update v N s msg := (s, decide (h <
    (s.targets ∩ FlagNeighborhood.selected v N s.residual msg).card))

def listRound (f : ℕ) : Round V (Input V × Bool) (Data V) Bool where
  send _ _ s := s.2
  update v N s msg :=
    let row := s.1.candidates ∩ FlagNeighborhood.selected v N s.2 msg
    ⟨s.1, if s.1.residual = true ∧ row.card ≤ f then row else ∅,
      s.1.residual && decide (row = ∅)⟩

def program (h f : ℕ) : Program V (Input V) (Data V) :=
  .seq (.broadcast 1 BitCode.bool (candidateRound h))
    (.broadcast 1 BitCode.bool (listRound f))

theorem rounds (h f : ℕ) : (program (V := V) h f).rounds = 2 := rfl

theorem maxBits (h f : ℕ) : (program (V := V) h f).maxBits = 1 := rfl

variable [Fintype V]

/-- Actual demanded rows covered by v, without using symmetry of coverage. -/
def inverse (C : V → Finset V) (R : Finset V) (v : V) : Finset V :=
  R.filter (fun r => v ∈ C r)

def eligible (C : V → Finset V) (h : ℕ) (R : Finset V) : Finset V :=
  Finset.univ.filter (fun v => h < (inverse C R v).card)

def eligibleList (C : V → Finset V) (h : ℕ) (R : Finset V) (r : V) : Finset V :=
  C r ∩ eligible C h R

def listed (C : V → Finset V) (h f : ℕ) (R : Finset V) : Finset V :=
  R.filter (fun r => (eligibleList C h R r).card ≤ f ∧ (eligibleList C h R r).Nonempty)

def lists (C : V → Finset V) (h f : ℕ) (R : Finset V) : Finset (Finset V) :=
  (listed C h f R).image (eligibleList C h R)

def emptyLists (C : V → Finset V) (h : ℕ) (R : Finset V) : Finset V :=
  R.filter (fun r => eligibleList C h R r = ∅)

def hosted (C : V → Finset V) (h f : ℕ) (R : Finset V) (r : V) : Finset V :=
  if r ∈ R ∧ (eligibleList C h R r).card ≤ f then eligibleList C h R r else ∅

theorem empty_subset (C : V → Finset V) (h : ℕ) (R : Finset V) :
    emptyLists C h R ⊆ R := Finset.filter_subset _ _

theorem lists_rank (C : V → Finset V) (h f : ℕ) (R : Finset V) :
    ∀ t ∈ lists C h f R, t.card ≤ f := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
  exact (Finset.mem_filter.mp hr).2.1

theorem lists_nonempty (C : V → Finset V) (h f : ℕ) (R : Finset V) :
    ∀ t ∈ lists C h f R, t.Nonempty := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
  exact (Finset.mem_filter.mp hr).2.2

theorem hosted_bound (C : V → Finset V) (h f : ℕ) (R : Finset V) :
    ∀ r, (hosted C h f R r).card ≤ f := by
  intro r
  unfold hosted
  split_ifs with hr
  · exact hr.2
  · simp

theorem family_eq (C : V → Finset V) (h f : ℕ) (R : Finset V) :
    ListIncidenceBroadcast.family (hosted C h f R) = lists C h f R := by
  ext t
  rw [ListIncidenceBroadcast.mem_family]
  constructor
  · rintro ⟨hne, r, he⟩
    have hr : r ∈ R ∧ (eligibleList C h R r).card ≤ f := by
      by_contra hn
      have hh : hosted C h f R r = ∅ := if_neg hn
      exact hne (he.symm.trans hh)
    have hrow : hosted C h f R r = eligibleList C h R r := if_pos hr
    have hn : (eligibleList C h R r).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by rw [← hrow, he]; exact hne)
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr.1, hr.2, hn⟩,
      hrow.symm.trans he⟩
  · intro ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hrR, hbound, hne⟩ := Finset.mem_filter.mp hr
    exact ⟨Finset.nonempty_iff_ne_empty.mp hne, r, if_pos ⟨hrR, hbound⟩⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inverse_local (C : V → Finset V) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (v : V) :
    inverse C R v ⊆ closed G v ∩ R := by
  intro r hr
  obtain ⟨hrR, hvr⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_inter.mpr ⟨(closed_symm G r v).mpr (hlocal r hrR hvr), hrR⟩

theorem hosted_local (C : V → Finset V) (h f : ℕ) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    ∀ r, hosted C h f R r ⊆ closed G r := by
  intro r
  unfold hosted
  split_ifs with hr
  · exact Finset.inter_subset_left.trans (hlocal r hr.1)
  · exact Finset.empty_subset _

/-- Filtering the physical residual snapshot through the candidate's actual
incidence bits gives exactly its inverse incidence list in R. -/
theorem snapshot_targets (C targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (v : V) :
    targets v ∩ (closed G v ∩ R) = inverse C R v := by
  ext r
  simp only [Finset.mem_inter, inverse, Finset.mem_filter]
  constructor
  · rintro ⟨ht, _, hr⟩
    exact ⟨hr, (hinc v r).mp ht⟩
  · rintro ⟨hr, hc⟩
    exact ⟨(hinc v r).mpr hc, (closed_symm G r v).mpr (hlocal r hr hc), hr⟩

theorem snapshot_row (C : V → Finset V) (h : ℕ) (R : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (r : V) (hr : r ∈ R) :
    C r ∩ (closed G r ∩ eligible C h R) = eligibleList C h R r := by
  ext v
  simp only [eligibleList, Finset.mem_inter]
  constructor
  · rintro ⟨hc, _, he⟩
    exact ⟨hc, he⟩
  · rintro ⟨hc, he⟩
    exact ⟨hc, hlocal r hr hc, he⟩

theorem candidate_correct (C targets : V → Finset V) (h : ℕ) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hT : ∀ v, (s v).targets = targets v) :
    eval G (candidateRound h) s = fun v => (s v, decide (v ∈ eligible C h R)) := by
  have hflags : (fun r => (s r).residual) = fun r => decide (r ∈ R) := funext hR
  funext v
  change (s v, decide (h < ((s v).targets ∩
    FlagNeighborhood.program.run G (fun r => (s r).residual) v).card)) = _
  rw [hflags, hT v, FlagNeighborhood.correct G R v, snapshot_targets G C targets R hinc hlocal v]
  simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Both incidence lists remain private and unchanged. Large lists are
suppressed, and only residual demands with empty Lambda become requesters. -/
theorem correct (C targets : V → Finset V) (h f : ℕ) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) :
    (program h f).run G s = fun v =>
      ⟨s v, hosted C h f R v, decide (v ∈ emptyLists C h R)⟩ := by
  change eval G (listRound f) (eval G (candidateRound h) s) = _
  rw [candidate_correct G C targets h R hinc hlocal s hR hT]
  funext v
  change (Data.mk (s v)
    (if (s v).residual = true ∧ ((s v).candidates ∩ FlagNeighborhood.program.run G
      (fun u => decide (u ∈ eligible C h R)) v).card ≤ f then
      (s v).candidates ∩ FlagNeighborhood.program.run G (fun u => decide (u ∈ eligible C h R)) v else ∅)
    ((s v).residual && decide ((s v).candidates ∩ FlagNeighborhood.program.run G
      (fun u => decide (u ∈ eligible C h R)) v = ∅))) = _
  rw [hR v, hC v, FlagNeighborhood.correct G (eligible C h R) v]
  by_cases hv : v ∈ R
  · rw [snapshot_row G C h R hlocal v hv]
    simp [hosted, emptyLists, hv]
  · simp [hosted, emptyLists, hv]

end Paper.GeneralCoveringInitializerPassLists

#print axioms Paper.GeneralCoveringInitializerPassLists.snapshot_targets
#print axioms Paper.GeneralCoveringInitializerPassLists.candidate_correct
#print axioms Paper.GeneralCoveringInitializerPassLists.correct
#print axioms Paper.GeneralCoveringInitializerPassLists.hosted_bound
#print axioms Paper.GeneralCoveringInitializerPassLists.hosted_local
#print axioms Paper.GeneralCoveringInitializerPassLists.family_eq
#print axioms Paper.GeneralCoveringInitializerPassLists.rounds
#print axioms Paper.GeneralCoveringInitializerPassLists.maxBits
