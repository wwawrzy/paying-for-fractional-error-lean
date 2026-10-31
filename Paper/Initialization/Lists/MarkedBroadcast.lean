import Paper.Initialization.Lists.MarkedLists
import Paper.Preliminaries.CohostKnown
import Paper.Preliminaries.IncidentPhase
import Paper.Communication.ProgramMemory

/-! Finite local tests and physical broadcasts for the marked-list procedure.
The private test enumerates subsets of the received support, never vertices
outside the local input. All ranks refer to the original family of lists. -/
namespace Paper.MarkedBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

def support (H : Finset (Finset V)) : Finset V := H.biUnion id

def markedTest (H : Finset (Finset V)) (q : ℕ) (C : Finset V) : Bool :=
  decide (C.Nonempty ∧ (∃ L ∈ H, C ⊆ L) ∧
    ∀ B ∈ (support H).powerset, Disjoint B C →
      (∀ L ∈ H, C ⊆ L → (L ∩ B).Nonempty) → q ≤ B.card)

def finiteLevel (H : Finset (Finset V)) (q j : ℕ) : Finset (Finset V) :=
  (H.biUnion Finset.powerset).filter (fun C => C.card = j ∧ markedTest H q C = true)

def localLevel (v : V) (H : Finset (Finset V)) (q j : ℕ) : Finset (Finset V) :=
  (finiteLevel H q j).filter (fun C => v ∈ C)

variable [Fintype V]

theorem markedTest_correct (H : Finset (Finset V)) (q : ℕ) (C : Finset V) :
    markedTest H q C = true ↔ MarkedLists.Marked H q C := by
  have hinst : (fun x y : V => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  simp only [markedTest, decide_eq_true_eq, MarkedLists.Marked,
    MarkedLists.Admissible, MarkedLists.ExternalCover]
  rw [hinst]
  constructor
  · rintro ⟨hne, hadm, htest⟩
    refine ⟨⟨hne, hadm⟩, ?_⟩
    intro B hB
    let B' := B ∩ support H
    have hsub : B' ⊆ support H := Finset.inter_subset_right
    have hdis : Disjoint B' C := Finset.disjoint_left.mpr
      (fun v hv hc => Finset.disjoint_left.mp hB.1 (Finset.mem_inter.mp hv).1 hc)
    have hcover : ∀ L ∈ H, C ⊆ L → (L ∩ B').Nonempty := by
      intro L hL hCL
      obtain ⟨v, hv⟩ := hB.2 L hL hCL
      have hs : v ∈ support H := Finset.mem_biUnion.mpr
        ⟨L, hL, (Finset.mem_inter.mp hv).1⟩
      exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).2, hs⟩⟩⟩
    exact (htest B' (Finset.mem_powerset.mpr hsub) hdis hcover).trans
      (Finset.card_le_card Finset.inter_subset_left)
  · intro h
    exact ⟨h.1.1, h.1.2, fun B _ hd hc => h.2 B ⟨hd, hc⟩⟩

theorem finiteLevel_eq (H : Finset (Finset V)) (q j : ℕ) :
    finiteLevel H q j = MarkedLists.level H q j := by
  have hinst : (fun x y : V => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  have hinstF : (fun x y : Finset V => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq (Finset V)) := Subsingleton.elim _ _
  ext C
  simp only [finiteLevel, MarkedLists.level, MarkedLists.candidates,
    Finset.mem_filter, markedTest_correct]
  rw [hinst]
  constructor
  · rintro ⟨hc, hj, hm⟩
    exact ⟨hc, hm, hj⟩
  · rintro ⟨hc, hm, hj⟩
    exact ⟨hc, hj, hm⟩

theorem marked_incident_iff (H : Finset (Finset V)) (q : ℕ) (v : V)
    {C : Finset V} (hv : v ∈ C) :
    MarkedLists.Marked (IncidentHierarchy.incident H v) q C ↔
      MarkedLists.Marked H q C := by
  classical
  constructor
  · rintro ⟨⟨hne, L, hL, hCL⟩, hmarked⟩
    refine ⟨⟨hne, L, (Finset.mem_filter.mp hL).1, hCL⟩, ?_⟩
    intro B hB
    exact hmarked B ⟨hB.1, fun A hA hCA => hB.2 A (Finset.mem_filter.mp hA).1 hCA⟩
  · rintro ⟨⟨hne, L, hL, hCL⟩, hmarked⟩
    refine ⟨⟨hne, L, Finset.mem_filter.mpr ⟨hL, hCL hv⟩, hCL⟩, ?_⟩
    intro B hB
    exact hmarked B ⟨hB.1, fun A hA hCA =>
      hB.2 A (Finset.mem_filter.mpr ⟨hA, hCA hv⟩) hCA⟩

theorem local_global (H : Finset (Finset V)) (q j : ℕ) (v : V) :
    localLevel v (IncidentHierarchy.incident H v) q j =
      IncidentHierarchy.incident (MarkedLists.level H q j) v := by
  classical
  rw [localLevel, finiteLevel_eq]
  ext C
  simp only [IncidentHierarchy.incident, Finset.mem_filter]
  rw [MarkedLists.mem_level, MarkedLists.mem_level]
  constructor
  · rintro ⟨⟨hm, hc⟩, hv⟩
    exact ⟨⟨(marked_incident_iff H q v hv).mp hm, hc⟩, hv⟩
  · rintro ⟨⟨hm, hc⟩, hv⟩
    exact ⟨⟨(marked_incident_iff H q v hv).mpr hm, hc⟩, hv⟩

end Paper.MarkedBroadcast

namespace Paper.MarkedBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure State (V : Type) where
  ownList : Finset V
  incident : Finset (Finset V)
  selected : Bool

def prepareKnown : Program V (State V) ((Finset V × Bool) × State V) :=
  .local fun _ _ s => ((s.ownList, s.selected), s)

def finishKnown (q j : ℕ) : Program V (Finset V × State V) (State V) :=
  .local fun v _ s => ⟨s.2.ownList, s.2.incident,
    IncidentPhase.chosen v (localLevel v s.2.incident q j) s.1 s.2.selected⟩

def step {b : ℕ} (C : BitCode V b) (f q j : ℕ) : Program V (State V) (State V) :=
  .seq prepareKnown (.seq (ProgramMemory.carry (CohostKnown.program C f)) (finishKnown q j))

def body {b : ℕ} (C : BitCode V b) (f q : ℕ) : ℕ → Program V (State V) (State V)
  | 0 => .local fun _ _ s => ⟨s.ownList, s.incident, false⟩
  | j + 1 => .seq (body C f q j) (step C f q (j + 1))

def start : Program V (Finset V) (Finset V × Finset V) := .local fun _ _ s => (s, s)

def initializeState : Program V (Finset (Finset V) × Finset V) (State V) :=
  .local fun _ _ s => ⟨s.2, s.1, false⟩

def program {b : ℕ} (C : BitCode V b) (f q : ℕ) : Program V (Finset V) Bool :=
  .seq start (.seq (ProgramMemory.carry (ListIncidenceBroadcast.program C f))
    (.seq initializeState (.seq (body C f q f) (.local fun _ _ s => s.selected))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_step {b : ℕ} (C : BitCode V b) (f q j : ℕ) (s : V → State V) :
    (step C f q j).run G s = fun v => ⟨(s v).ownList, (s v).incident,
      IncidentPhase.chosen v (localLevel v (s v).incident q j)
        ((CohostKnown.program C f).run G (fun u => ((s u).ownList, (s u).selected)) v) (s v).selected⟩ := by
  change (finishKnown q j).run G ((ProgramMemory.carry (CohostKnown.program C f)).run G
    (fun u => (((s u).ownList, (s u).selected), s u))) = _
  rw [ProgramMemory.run]
  rfl

theorem body_metadata {b : ℕ} (C : BitCode V b) (f q j : ℕ) (s : V → State V) :
    ∀ v, ((body C f q j).run G s v).ownList = (s v).ownList ∧
      ((body C f q j).run G s v).incident = (s v).incident := by
  induction j generalizing s with
  | zero => exact fun _ => ⟨rfl, rfl⟩
  | succ j ih =>
    intro v
    change ((step C f q (j+1)).run G ((body C f q j).run G s) v).ownList = _ ∧ _
    rw [run_step]
    exact ih s v

theorem level_known (lists : V → Finset V)
    (hlocal : ∀ u, lists u ⊆ SevenFoundation.closed G u)
    (q j : ℕ) (S : Finset V) (v : V) :
    ∀ t ∈ IncidentHierarchy.incident (MarkedLists.level (ListIncidenceBroadcast.family lists) q j) v,
      ∀ u ∈ t, u ∈ CohostKnown.known G lists S v ↔ u ∈ S := by
  intro t ht u hu
  have hmem := Finset.mem_filter.mp ht
  have hmarked := ((MarkedLists.mem_level _ q j t).mp hmem.1).1
  obtain ⟨original, horiginal, hsub⟩ := hmarked.1.2
  obtain ⟨_, host, he⟩ := (ListIncidenceBroadcast.mem_family lists original).mp horiginal
  rw [← he] at hsub
  exact CohostKnown.cohost_agrees G lists hlocal S v host u (hsub hmem.2) (hsub hu)

theorem step_correct {b : ℕ} (C : BitCode V b) (f q j : ℕ)
    (lists : V → Finset V) (hbound : ∀ u, (lists u).card ≤ f)
    (hlocal : ∀ u, lists u ⊆ SevenFoundation.closed G u) (S : Finset V) (s : V → State V)
    (hown : ∀ v, (s v).ownList = lists v)
    (hincident : ∀ v, (s v).incident = IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v)
    (hselected : ∀ v, (s v).selected = decide (v ∈ S)) (v : V) :
    ((step C f q j).run G s v).selected =
      decide (v ∈ ListPhase.phase (MarkedLists.level (ListIncidenceBroadcast.family lists) q j) S) := by
  have hin : (fun u => ((s u).ownList, (s u).selected)) = fun u => (lists u, decide (u ∈ S)) := by
    funext u
    rw [hown u, hselected u]
  rw [run_step]
  dsimp only
  rw [hin, CohostKnown.correct G C f lists hbound hlocal S, hincident v, hselected v,
    local_global _ q j v]
  have hh := IncidentPhase.correct
    (MarkedLists.level (ListIncidenceBroadcast.family lists) q j) S
    (CohostKnown.known G lists S v) v
  have hinst : (fun x y : V => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hh
  exact hh (level_known G lists hlocal q j S v)

theorem body_correct {b : ℕ} (C : BitCode V b) (f q : ℕ)
    (lists : V → Finset V) (hbound : ∀ u, (lists u).card ≤ f)
    (hlocal : ∀ u, lists u ⊆ SevenFoundation.closed G u) (j : ℕ) (s : V → State V)
    (hown : ∀ v, (s v).ownList = lists v)
    (hincident : ∀ v, (s v).incident = IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v) :
    ∀ v, ((body C f q j).run G s v).selected =
      decide (v ∈ MarkedLists.output (ListIncidenceBroadcast.family lists) q j) := by
  induction j generalizing s with
  | zero => intro v; simp only [body, Program.run, MarkedLists.output, Finset.notMem_empty, decide_false]
  | succ j ih =>
    let t := (body C f q j).run G s
    have hm := body_metadata G C f q j s
    have ht0 : ∀ v, (t v).ownList = lists v := fun v => (hm v).1.trans (hown v)
    have ht1 : ∀ v, (t v).incident = IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v :=
      fun v => (hm v).2.trans (hincident v)
    intro v
    change ((step C f q (j+1)).run G t v).selected = _
    exact step_correct G C f q (j+1) lists hbound hlocal
      (MarkedLists.output (ListIncidenceBroadcast.family lists) q j) t ht0 ht1 (ih s hown hincident) v

theorem correct {b : ℕ} (C : BitCode V b) (f q : ℕ)
    (lists : V → Finset V) (hbound : ∀ u, (lists u).card ≤ f)
    (hlocal : ∀ u, lists u ⊆ SevenFoundation.closed G u) :
    (program C f q).run G lists = fun v => decide (v ∈ MarkedLists.output (ListIncidenceBroadcast.family lists) q f) := by
  let raw := (ProgramMemory.carry (ListIncidenceBroadcast.program C f)).run G (fun u => (lists u, lists u))
  change (fun v => ((body C f q f).run G (initializeState.run G raw) v).selected) = _
  have hraw : raw = fun u => ((ListIncidenceBroadcast.program C f).run G lists u, lists u) :=
    ProgramMemory.run G (ListIncidenceBroadcast.program C f) lists lists
  rw [hraw]
  have hg : (ListIncidenceBroadcast.program C f).run G lists =
      fun v => IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v :=
    funext (ListIncidenceBroadcast.correct G C f lists hbound hlocal)
  rw [hg]
  funext v
  exact body_correct G C f q lists hbound hlocal f
    (fun u => ⟨lists u, IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) u, false⟩)
    (fun _ => rfl) (fun _ => rfl) v

theorem body_rounds {b : ℕ} (C : BitCode V b) (f q j : ℕ) : (body C f q j).rounds = 2*j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [body, step, prepareKnown, finishKnown, Program.rounds, ProgramMemory.rounds,
      CohostKnown.rounds, Nat.zero_add, Nat.add_zero, ih]
    omega

theorem body_maxBits {b : ℕ} (C : BitCode V b) (f q j : ℕ) :
    (body C f q j).maxBits ≤ max 1 (f*(b+1)) := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    apply max_le ih
    simp only [step, prepareKnown, finishKnown, Program.maxBits, ProgramMemory.maxBits,
      CohostKnown.maxBits, Nat.zero_max, Nat.max_zero]
    exact le_rfl

theorem rounds {b : ℕ} (C : BitCode V b) (f q : ℕ) : (program C f q).rounds = 1+2*f := by
  simp only [program, start, initializeState, Program.rounds, ProgramMemory.rounds,
    ListIncidenceBroadcast.rounds, body_rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (f q : ℕ) :
    (program C f q).maxBits ≤ max 1 (f*(b+1)) := by
  simp only [program, start, initializeState, Program.maxBits, ProgramMemory.maxBits,
    ListIncidenceBroadcast.maxBits, Nat.zero_max, Nat.max_zero]
  exact max_le (le_max_right _ _) (body_maxBits C f q f)

end Paper.MarkedBroadcast
