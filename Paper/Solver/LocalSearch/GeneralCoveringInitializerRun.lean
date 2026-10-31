import Paper.Solver.LocalSearch.GeneralCoveringInitializerPass

/-! The concrete fixed-pass initializer for arbitrary covering incidences.
Each vertex retains its own candidates/targets, residual bit and saved
selection bit. Terminal survivors request min C(r) using the accepted
two-round protocol. Global sets below interpret the run only. -/
namespace Paper.GeneralCoveringInitializerRun
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringInitializerPass.Input
abbrev State (V : Type) := Input V × Bool

def advance (out : GeneralCoveringRequests.Output) (s : State V) : State V :=
  ({ s.1 with residual := out.uncovered }, s.2 || out.selected)

def step {bits : ℕ} (ids : BitCode V bits) (b h f : ℕ) :
    Program V (State V) (State V) :=
  .seq (.local fun _ _ s => (s.1, s))
    (.seq (ProgramMemory.carry (GeneralCoveringInitializerPass.program ids b h f))
      (.local fun _ _ s => advance s.1 s.2))

def terminalInput (s : State V) : GeneralCoveringRequests.Input V :=
  ⟨s.2, s.1.residual, s.1.residual, s.1.candidates⟩

/-- Public parameters precede the graph. No global covering relation, demand
set, competitor, hierarchy or sequence of selections is a program input. -/
def program {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) :
    Program V (Input V) GeneralCoveringRequests.Output :=
  .seq (.local fun _ _ s => (s, false))
    (.seq ((step ids b h f).iterate T)
      (.seq (.local fun _ _ s => terminalInput s) (GeneralCoveringRequests.program ids)))

variable [Fintype V]

theorem rounds {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) :
    (program ids b h f T).rounds = T * (5 + 2 * f) + 2 := by
  simp only [program, step, Program.rounds, Program.iterate_rounds, ProgramMemory.rounds,
    GeneralCoveringInitializerPass.rounds, GeneralCoveringRequests.rounds,
    Nat.zero_add, Nat.add_zero]

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) :
    (program ids b h f T).maxBits ≤ max (bits + 1) (f * (bits + 1)) := by
  have hs : (step ids b h f).maxBits ≤ max (bits + 1) (f * (bits + 1)) := by
    simpa only [step, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max,
      Nat.max_zero] using GeneralCoveringInitializerPass.maxBits ids b h f
  have hi := Program.iterate_maxBits (step ids b h f) T
  have hr := GeneralCoveringRequests.maxBits ids
  simp only [program, Program.maxBits, Nat.zero_max]
  exact max_le (hi.trans hs) (hr.trans (le_max_left _ _))

noncomputable def state (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) : ℕ → Finset V
  | 0 => R₀
  | n + 1 => GeneralCoveringInitializerPass.residual C b h f (state C b h f R₀ n)

noncomputable def selection (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (n : ℕ) :
    Finset V := GeneralCoveringInitializerPass.selected C b h f (state C b h f R₀ n)

noncomputable def past (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) : ℕ → Finset V
  | 0 => ∅
  | n + 1 => past C b h f R₀ n ∪ selection C b h f R₀ n

noncomputable def selected (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (T : ℕ) :
    Finset V := GeneralCoveringRequests.selectedPlus C (past C b h f R₀ T) (state C b h f R₀ T)

theorem mem_state_succ (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (n : ℕ) (r : V) :
    r ∈ state C b h f R₀ (n + 1) ↔
      r ∈ state C b h f R₀ n ∧ C r ∩ selection C b h f R₀ n = ∅ := by
  exact Finset.mem_filter

theorem antitone (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) :
    Antitone (state C b h f R₀) :=
  antitone_nat_of_succ_le (fun _ => Finset.filter_subset _ _)

theorem state_subset_initial (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (n : ℕ) :
    state C b h f R₀ n ⊆ R₀ := antitone C b h f R₀ (Nat.zero_le n)

/-- Exact C-residual, including all saved choices, rather than removal of
entire physical neighborhoods. -/
theorem remaining (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (n : ℕ) :
    state C b h f R₀ n = R₀.filter (fun r => C r ∩ past C b h f R₀ n = ∅) := by
  induction n with
  | zero => ext r; simp [state, past]
  | succ n ih =>
    ext r
    rw [mem_state_succ, ih]
    simp only [Finset.mem_filter, past, Finset.inter_union_distrib_left,
      Finset.union_eq_empty]
    tauto

/-- An earlier choice has no covering incidence to a later residual demand.
It may still have a physical edge to that demand. -/
theorem earlier_incidence_absent (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V)
    {i j : ℕ} (hij : i < j) {v r : V}
    (hv : v ∈ selection C b h f R₀ i) (hr : r ∈ state C b h f R₀ j) : v ∉ C r := by
  have hr' := antitone C b h f R₀ (show i + 1 ≤ j by omega) hr
  have he := ((mem_state_succ C b h f R₀ i r).mp hr').2
  intro hvC
  exact (Finset.nonempty_iff_ne_empty.mp ⟨v, Finset.mem_inter.mpr ⟨hvC, hv⟩⟩) he

theorem selections_disjoint (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b)
    (R₀ : Finset V) {i j : ℕ} (hne : i ≠ j) :
    Disjoint (selection C b h f R₀ i) (selection C b h f R₀ j) := by
  have forward : ∀ {i j : ℕ}, i < j →
      Disjoint (selection C b h f R₀ i) (selection C b h f R₀ j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have had := GeneralCoveringInitializerPass.selected_admissible C b h f hb
      (state C b h f R₀ j) hvj
    obtain ⟨r, hr, hvC⟩ := Finset.mem_biUnion.mp had
    exact earlier_incidence_absent C b h f R₀ hij hvi hr hvC
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact forward hij
  · exact (forward hji).symm

theorem selection_admissible (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b)
    (R₀ : Finset V) (n : ℕ) :
    selection C b h f R₀ n ⊆ CoveringSupport.admissible C R₀ := by
  intro v hv
  obtain ⟨r, hr, hvC⟩ := Finset.mem_biUnion.mp
    (GeneralCoveringInitializerPass.selected_admissible C b h f hb (state C b h f R₀ n) hv)
  exact Finset.mem_biUnion.mpr ⟨r, state_subset_initial C b h f R₀ n hr, hvC⟩

theorem past_admissible (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b)
    (R₀ : Finset V) (n : ℕ) : past C b h f R₀ n ⊆ CoveringSupport.admissible C R₀ := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ih hv
    · exact selection_admissible C b h f hb R₀ n hv

theorem selected_admissible (C : V → Finset V) (b h f : ℕ) (hb : 1 ≤ b)
    (R₀ : Finset V) (T : ℕ) : selected C b h f R₀ T ⊆ CoveringSupport.admissible C R₀ :=
  GeneralCoveringRequests.admissible C R₀ (past C b h f R₀ T) (state C b h f R₀ T)
    (state_subset_initial C b h f R₀ T) (past_admissible C b h f hb R₀ T)

theorem saved_subset (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (T : ℕ) :
    past C b h f R₀ T ⊆ selected C b h f R₀ T :=
  GeneralCoveringRequests.selected_subset C _ _

theorem selected_covers (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (T : ℕ)
    (hrows : ∀ r ∈ R₀, (C r).Nonempty) :
    GeneralCoveringInitializerPass.Covers C R₀ (selected C b h f R₀ T) := by
  intro r hr
  by_cases hs : r ∈ state C b h f R₀ T
  · exact GeneralCoveringRequests.covers_requesters C (past C b h f R₀ T)
      (state C b h f R₀ T)
      (fun u hu => hrows u (state_subset_initial C b h f R₀ T hu)) r hs
  · have hn : C r ∩ past C b h f R₀ T ≠ ∅ := by
      intro he
      apply hs
      rw [remaining]
      exact Finset.mem_filter.mpr ⟨hr, he⟩
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hn
    have hm := Finset.mem_inter.mp hv
    exact ⟨v, saved_subset C b h f R₀ T hm.2, hm.1⟩

theorem terminal_empty (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (T : ℕ)
    (hrows : ∀ r ∈ R₀, (C r).Nonempty) :
    GeneralCoveringRequests.residual C (state C b h f R₀ T)
      (past C b h f R₀ T) (state C b h f R₀ T) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hrR, he⟩ := Finset.mem_filter.mp hr
  obtain ⟨v, hvS, hvC⟩ := GeneralCoveringRequests.covers_requesters C (past C b h f R₀ T)
    (state C b h f R₀ T)
    (fun u hu => hrows u (state_subset_initial C b h f R₀ T hu)) r hrR
  exact (Finset.nonempty_iff_ne_empty.mp ⟨v, Finset.mem_inter.mpr ⟨hvC, hvS⟩⟩) he

theorem terminal_new_card (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (T : ℕ) :
    (selected C b h f R₀ T \ past C b h f R₀ T).card ≤ (state C b h f R₀ T).card :=
  GeneralCoveringRequests.new_card C _ _

/-- Proof-side interpretation preserving the literal private candidates and
targets. The program never receives R or P. -/
def snapshot (s : V → Input V) (R P : Finset V) (v : V) : State V :=
  (⟨decide (v ∈ R), (s v).candidates, (s v).targets⟩, decide (v ∈ P))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_step {bits : ℕ} (ids : BitCode V bits) (b h f : ℕ) (s : V → State V) :
    (step ids b h f).run G s = fun v =>
      advance ((GeneralCoveringInitializerPass.program ids b h f).run G (fun u => (s u).1) v)
        (s v) := by
  change (fun v => advance
    (((ProgramMemory.carry (GeneralCoveringInitializerPass.program ids b h f)).run G
      (fun u => ((s u).1, s u)) v).1)
    (((ProgramMemory.carry (GeneralCoveringInitializerPass.program ids b h f)).run G
      (fun u => ((s u).1, s u)) v).2)) = _
  simp only [ProgramMemory.run]

theorem step_correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f : ℕ) (hb : 1 ≤ b) (R P : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (s : V → Input V)
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) :
    (step ids b h f).run G (snapshot s R P) =
      snapshot s (GeneralCoveringInitializerPass.residual C b h f R)
        (P ∪ GeneralCoveringInitializerPass.selected C b h f R) := by
  rw [run_step, GeneralCoveringInitializerPass.correct G ids C targets b h f hb R
    hinc hlocal (fun v => (snapshot s R P v).1) (fun _ => rfl) hC hT]
  funext v
  apply Prod.ext
  · rfl
  · change (decide (v ∈ P) || decide (v ∈ GeneralCoveringInitializerPass.selected C b h f R)) =
      decide (v ∈ P ∪ GeneralCoveringInitializerPass.selected C b h f R)
    simp only [Finset.mem_union, Bool.decide_or]

/-- The actual iterate computes the exact C-residual and saved past bits,
while retaining only each vertex's own original incidence lists. -/
theorem iterate_correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f : ℕ) (hb : 1 ≤ b) (R₀ : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) (s : V → Input V)
    (hR : ∀ r, (s r).residual = decide (r ∈ R₀))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) (T : ℕ) :
    ((step ids b h f).iterate T).run G (fun v => (s v, false)) =
      snapshot s (state C b h f R₀ T) (past C b h f R₀ T) := by
  induction T with
  | zero =>
    funext v
    apply Prod.ext
    · change s v = { s v with residual := decide (v ∈ R₀) }
      rw [← hR v]
    · change false = decide (v ∈ (∅ : Finset V))
      simp
  | succ T ih =>
    change (step ids b h f).run G
      (((step ids b h f).iterate T).run G (fun v => (s v, false))) = _
    rw [ih]
    exact step_correct G ids C targets b h f hb (state C b h f R₀ T) (past C b h f R₀ T)
      hinc (fun r hr => hlocal r (state_subset_initial C b h f R₀ T hr)) s hC hT

/-- Exact complete output of the real loop followed by terminal min-C requests.
Nonempty rows are used to prove that the final uncovered bits are all false. -/
theorem correct {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T : ℕ) (hb : 1 ≤ b) (R₀ : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) (hrows : ∀ r ∈ R₀, (C r).Nonempty)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R₀))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) :
    (program ids b h f T).run G s = fun v => ⟨decide (v ∈ selected C b h f R₀ T), false⟩ := by
  change (GeneralCoveringRequests.program ids).run G
    (fun v => terminalInput (((step ids b h f).iterate T).run G (fun u => (s u, false)) v)) = _
  rw [iterate_correct G ids C targets b h f hb R₀ hinc hlocal s hR hC hT T]
  have hq := GeneralCoveringRequests.correct G ids C (state C b h f R₀ T)
    (past C b h f R₀ T) (state C b h f R₀ T)
    (fun v => terminalInput (snapshot s (state C b h f R₀ T) (past C b h f R₀ T) v))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hC (Finset.Subset.refl _)
    (fun r hr => hlocal r (state_subset_initial C b h f R₀ T hr))
  rw [terminal_empty C b h f R₀ T hrows] at hq
  simpa only [Finset.notMem_empty, decide_false] using hq

def output {bits : ℕ} (ids : BitCode V bits) (b h f T : ℕ) (s : V → Input V) : Finset V :=
  Finset.univ.filter (fun v => ((program ids b h f T).run G s v).selected = true)

theorem output_eq {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T : ℕ) (hb : 1 ≤ b) (R₀ : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) (hrows : ∀ r ∈ R₀, (C r).Nonempty)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R₀))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) :
    output G ids b h f T s = selected C b h f R₀ T := by
  unfold output
  rw [correct G ids C targets b h f T hb R₀ hinc hlocal hrows s hR hC hT]
  ext v
  simp

/-- Actual feasibility, admissibility and preservation of saved selections.
The quantitative GeneralPruning instantiation is a separate dependency. -/
theorem spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f T : ℕ) (hb : 1 ≤ b) (R₀ : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) (hrows : ∀ r ∈ R₀, (C r).Nonempty)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R₀))
    (hC : ∀ r, (s r).candidates = C r) (hT : ∀ v, (s v).targets = targets v) :
    GeneralCoveringInitializerPass.Covers C R₀ (output G ids b h f T s) ∧
      output G ids b h f T s ⊆ CoveringSupport.admissible C R₀ ∧
      past C b h f R₀ T ⊆ output G ids b h f T s ∧
      (output G ids b h f T s \ past C b h f R₀ T).card ≤ (state C b h f R₀ T).card := by
  rw [output_eq G ids C targets b h f T hb R₀ hinc hlocal hrows s hR hC hT]
  exact ⟨selected_covers C b h f R₀ T hrows, selected_admissible C b h f hb R₀ T,
    saved_subset C b h f R₀ T, terminal_new_card C b h f R₀ T⟩

end Paper.GeneralCoveringInitializerRun

#print axioms Paper.GeneralCoveringInitializerRun.remaining
#print axioms Paper.GeneralCoveringInitializerRun.earlier_incidence_absent
#print axioms Paper.GeneralCoveringInitializerRun.selections_disjoint
#print axioms Paper.GeneralCoveringInitializerRun.selected_covers
#print axioms Paper.GeneralCoveringInitializerRun.selected_admissible
#print axioms Paper.GeneralCoveringInitializerRun.terminal_empty
#print axioms Paper.GeneralCoveringInitializerRun.terminal_new_card
#print axioms Paper.GeneralCoveringInitializerRun.iterate_correct
#print axioms Paper.GeneralCoveringInitializerRun.correct
#print axioms Paper.GeneralCoveringInitializerRun.output_eq
#print axioms Paper.GeneralCoveringInitializerRun.spec
#print axioms Paper.GeneralCoveringInitializerRun.rounds
#print axioms Paper.GeneralCoveringInitializerRun.maxBits
