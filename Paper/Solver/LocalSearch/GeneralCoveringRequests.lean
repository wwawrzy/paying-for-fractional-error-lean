import Paper.Communication.EncodedProgram
import Paper.Preliminaries.FlagNeighborhood
import Paper.Preliminaries.MaskedMinimum
import Paper.Certificates.Counting.CoveringSupport

/-! A concrete two-round request protocol for arbitrary local covering lists.
Each requester announces its least candidate ID. A candidate selects itself
when it receives its own ID, also handling its own request locally. The second
round announces the new selection bits. Only private lists and own S/W/R bits
are input; the graph and the global sets occur solely in correctness. -/
namespace Paper.GeneralCoveringRequests
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

structure Input (V : Type) where
  selected : Bool
  requester : Bool
  demand : Bool
  candidates : Finset V

structure State (V : Type) where
  input : Input V
  selected : Bool

structure Output where
  selected : Bool
  uncovered : Bool

def message (s : Input V) : Option V :=
  if s.requester then MaskedMinimum.minimum s.candidates else none

def selectRound : Round V (Input V) (State V) (Option V) where
  send _ _ s := message s
  update v N s msg := ⟨s, s.selected ||
    decide (v ∈ MaskedMinimum.pool N (message s) msg)⟩

def finishRound : Round V (State V) Output Bool where
  send _ _ s := s.selected
  update v N s msg := ⟨s.selected, s.input.demand &&
    decide (s.input.candidates ∩ FlagNeighborhood.selected v N s.selected msg = ∅)⟩

def program {b : ℕ} (ids : BitCode V b) : Program V (Input V) Output :=
  .seq (.broadcast (b + 1) ids.option selectRound)
    (.broadcast 1 BitCode.bool finishRound)

/-- A self request selects the sender without needing a physical self-loop. -/
theorem self_request_selected (v : V) (N : Finset V) (s : Input V)
    (msg : N → Option V) (h : message s = some v) :
    (selectRound.update v N s msg).selected = true := by
  change (s.selected || decide (v ∈ MaskedMinimum.pool N (message s) msg)) = true
  have hp := MaskedMinimum.mem_pool_self N msg h
  simp [hp]

theorem rounds {b : ℕ} (ids : BitCode V b) : (program ids).rounds = 2 := rfl

theorem maxBits {b : ℕ} (ids : BitCode V b) : (program ids).maxBits ≤ b + 1 := by
  change max (b + 1) 1 ≤ b + 1
  exact max_le le_rfl (by omega)

/-- The requests are a finite union of singleton minima. Empty rows contribute
nothing; nonemptiness is needed only to prove coverage of every requester. -/
def requested (C : V → Finset V) (W : Finset V) : Finset V :=
  W.biUnion (fun r => (MaskedMinimum.minimum (C r)).toFinset)

def selectedPlus (C : V → Finset V) (S W : Finset V) : Finset V :=
  S ∪ requested C W

def residual (C : V → Finset V) (R S W : Finset V) : Finset V :=
  R.filter (fun r => C r ∩ selectedPlus C S W = ∅)

theorem mem_requested (C : V → Finset V) (W : Finset V) (v : V) :
    v ∈ requested C W ↔ ∃ r ∈ W, MaskedMinimum.minimum (C r) = some v := by
  constructor
  · intro hv
    obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hv
    exact ⟨r, hr, by simpa using hm⟩
  · rintro ⟨r, hr, hm⟩
    exact Finset.mem_biUnion.mpr ⟨r, hr, by simp [hm]⟩

theorem message_iff (C : V → Finset V) (W : Finset V) (s : V → Input V)
    (hW : ∀ r, (s r).requester = decide (r ∈ W))
    (hC : ∀ r, (s r).candidates = C r) (r v : V) :
    message (s r) = some v ↔ r ∈ W ∧ MaskedMinimum.minimum (C r) = some v := by
  unfold message
  rw [hW r, hC r]
  by_cases hr : r ∈ W <;> simp [hr]

/-- A request always names a least member of the requester's actual list. -/
theorem message_minimum (C : V → Finset V) (W : Finset V) (s : V → Input V)
    (hW : ∀ r, (s r).requester = decide (r ∈ W))
    (hC : ∀ r, (s r).candidates = C r) (r v : V)
    (hm : message (s r) = some v) :
    r ∈ W ∧ v ∈ C r ∧ ∀ u ∈ C r, v ≤ u := by
  obtain ⟨hr, hmin⟩ := (message_iff C W s hW hC r v).mp hm
  refine ⟨hr, MaskedMinimum.minimum_mem hmin, ?_⟩
  intro u hu
  obtain ⟨w, hw, hwu⟩ := MaskedMinimum.minimum_le hu
  have he : v = w := Option.some.inj (hmin.symm.trans hw)
  rw [he]
  exact hwu

theorem selected_subset (C : V → Finset V) (S W : Finset V) :
    S ⊆ selectedPlus C S W := Finset.subset_union_left

theorem covers_requesters (C : V → Finset V) (S W : Finset V)
    (hne : ∀ r ∈ W, (C r).Nonempty) :
    ∀ r ∈ W, ∃ v ∈ selectedPlus C S W, v ∈ C r := by
  intro r hr
  obtain ⟨u, hu⟩ := hne r hr
  obtain ⟨v, hm, _⟩ := MaskedMinimum.minimum_le hu
  refine ⟨v, Finset.mem_union_right _ ((mem_requested C W v).mpr ⟨r, hr, hm⟩),
    MaskedMinimum.minimum_mem hm⟩

theorem requested_card (C : V → Finset V) (W : Finset V) :
    (requested C W).card ≤ W.card := by
  have hsingle (r : V) : ((MaskedMinimum.minimum (C r)).toFinset).card ≤ 1 := by
    cases hm : MaskedMinimum.minimum (C r) <;> simp [hm]
  calc
    _ ≤ ∑ r ∈ W, ((MaskedMinimum.minimum (C r)).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ W, 1 := Finset.sum_le_sum (fun r _ => hsingle r)
    _ = W.card := by simp

theorem new_subset (C : V → Finset V) (S W : Finset V) :
    selectedPlus C S W \ S ⊆ requested C W := by
  intro v hv
  obtain ⟨hv, hnot⟩ := Finset.mem_sdiff.mp hv
  exact (Finset.mem_union.mp hv).resolve_left hnot

theorem new_card (C : V → Finset V) (S W : Finset V) :
    (selectedPlus C S W \ S).card ≤ W.card :=
  (Finset.card_le_card (new_subset C S W)).trans (requested_card C W)

variable [Fintype V]

theorem requested_admissible (C : V → Finset V) (R0 W : Finset V) (hW : W ⊆ R0) :
    requested C W ⊆ CoveringSupport.admissible C R0 := by
  intro v hv
  obtain ⟨r, hr, hm⟩ := (mem_requested C W v).mp hv
  exact Finset.mem_biUnion.mpr ⟨r, hW hr, MaskedMinimum.minimum_mem hm⟩

theorem admissible (C : V → Finset V) (R0 S W : Finset V) (hW : W ⊆ R0)
    (hS : S ⊆ CoveringSupport.admissible C R0) :
    selectedPlus C S W ⊆ CoveringSupport.admissible C R0 := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact hS hv
  · exact requested_admissible C R0 W hW hv

/-- Only new selections are charged, with at most one bounded-cost choice
per requester. Costs are used in the proof, not in the request program. -/
theorem new_cost (C : V → Finset V) (R0 S W : Finset V) (hW : W ⊆ R0)
    (B : ℕ) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R0, c v ≤ B) :
    (∑ v ∈ selectedPlus C S W \ S, c v) ≤ (B : ℝ) * W.card := by
  calc
    _ ≤ ∑ _v ∈ selectedPlus C S W \ S, (B : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hc v (requested_admissible C R0 W hW (new_subset C S W hv))
    _ = (B : ℝ) * (selectedPlus C S W \ S).card := by simp [mul_comm]
    _ ≤ (B : ℝ) * W.card := mul_le_mul_of_nonneg_left
      (by exact_mod_cast (new_card C S W)) (Nat.cast_nonneg B)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All requests for a receiver are delivered either on a physical edge or
through the receiver's own local request. Incoming request pools stay private. -/
theorem select_correct (C : V → Finset V) (S W : Finset V) (s : V → Input V)
    (hS : ∀ v, (s v).selected = decide (v ∈ S))
    (hW : ∀ v, (s v).requester = decide (v ∈ W))
    (hC : ∀ v, (s v).candidates = C v)
    (hlocal : ∀ r ∈ W, C r ⊆ closed G r) :
    eval G selectRound s = fun v => ⟨s v, decide (v ∈ selectedPlus C S W)⟩ := by
  have horigin : ∀ r v, message (s r) = some v → v ∈ requested C W := by
    intro r v hm
    obtain ⟨hr, he⟩ := (message_iff C W s hW hC r v).mp hm
    exact (mem_requested C W v).mpr ⟨r, hr, he⟩
  funext v
  have hpool : v ∈ MaskedMinimum.pool (G.neighborFinset v) (message (s v))
      (fun r => message (s r.val)) ↔ v ∈ requested C W := by
    constructor
    · intro hv
      exact MaskedMinimum.pool_origin (G.neighborFinset v) (message (s v))
        (fun r => message (s r.val)) (fun u => u ∈ requested C W)
        (horigin v) (fun r => horigin r.val) hv
    · intro hv
      obtain ⟨r, hr, hm⟩ := (mem_requested C W v).mp hv
      have hmsg : message (s r) = some v := (message_iff C W s hW hC r v).mpr ⟨hr, hm⟩
      have hphys := (mem_closed G v r).mp (hlocal r hr (MaskedMinimum.minimum_mem hm))
      rcases hphys with he | ha
      · subst r
        exact MaskedMinimum.mem_pool_self _ _ hmsg
      · exact MaskedMinimum.mem_pool_incoming _ _ _
          ⟨r, (SimpleGraph.mem_neighborFinset G v r).mpr ha.symm⟩ hmsg
  change (State.mk (s v) ((s v).selected || decide (v ∈ MaskedMinimum.pool
    (G.neighborFinset v) (message (s v)) (fun r => message (s r.val))))) = _
  apply congrArg (State.mk (s v))
  rw [hS v, ← Bool.decide_or]
  apply Bool.decide_congr
  simp only [selectedPlus, Finset.mem_union, hpool]

/-- Exact selection and residual-demand bits from the two physical broadcasts.
Only actual requesters need nonempty lists (for coverage, proved separately). -/
theorem correct {b : ℕ} (ids : BitCode V b) (C : V → Finset V) (R S W : Finset V)
    (s : V → Input V)
    (hS : ∀ v, (s v).selected = decide (v ∈ S))
    (hW : ∀ v, (s v).requester = decide (v ∈ W))
    (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v) (hWR : W ⊆ R)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    (program ids).run G s = fun v =>
      ⟨decide (v ∈ selectedPlus C S W), decide (v ∈ residual C R S W)⟩ := by
  change eval G finishRound (eval G selectRound s) = _
  rw [select_correct G C S W s hS hW hC (fun r hr => hlocal r (hWR hr))]
  funext v
  have hnear := FlagNeighborhood.correct G (selectedPlus C S W) v
  change FlagNeighborhood.selected v (G.neighborFinset v)
    (decide (v ∈ selectedPlus C S W)) (fun u => decide (u.val ∈ selectedPlus C S W)) =
      closed G v ∩ selectedPlus C S W at hnear
  change (Output.mk (decide (v ∈ selectedPlus C S W))
    ((s v).demand && decide ((s v).candidates ∩ FlagNeighborhood.selected v
      (G.neighborFinset v) (decide (v ∈ selectedPlus C S W))
      (fun u => decide (u.val ∈ selectedPlus C S W)) = ∅))) = _
  apply congrArg (Output.mk (decide (v ∈ selectedPlus C S W)))
  rw [hR v, hC v, hnear]
  by_cases hv : v ∈ R
  · have he : C v ∩ (closed G v ∩ selectedPlus C S W) = C v ∩ selectedPlus C S W := by
      ext u
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hu, _, hs⟩
        exact ⟨hu, hs⟩
      · rintro ⟨hu, hs⟩
        exact ⟨hu, hlocal v hv hu, hs⟩
    rw [he]
    simp [residual, hv]
  · simp [residual, hv]

def output {b : ℕ} (ids : BitCode V b) (s : V → Input V) : Finset V :=
  Finset.univ.filter (fun v => ((program ids).run G s v).selected = true)

theorem output_eq {b : ℕ} (ids : BitCode V b) (C : V → Finset V) (R S W : Finset V)
    (s : V → Input V)
    (hS : ∀ v, (s v).selected = decide (v ∈ S))
    (hW : ∀ v, (s v).requester = decide (v ∈ W))
    (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v) (hWR : W ⊆ R)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    output G ids s = selectedPlus C S W := by
  unfold output
  rw [correct G ids C R S W s hS hW hR hC hWR hlocal]
  ext v
  simp

/-- A proof-side initial demand set R0 permits existing selections from earlier
passes. They need not remain admissible for the current residual set R. -/
theorem spec {b : ℕ} (ids : BitCode V b) (C : V → Finset V) (R0 R S W : Finset V)
    (s : V → Input V)
    (hS : ∀ v, (s v).selected = decide (v ∈ S))
    (hW : ∀ v, (s v).requester = decide (v ∈ W))
    (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v) (hRR : R ⊆ R0) (hWR : W ⊆ R)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hne : ∀ r ∈ W, (C r).Nonempty)
    (hSad : S ⊆ CoveringSupport.admissible C R0) (B : ℕ) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R0, c v ≤ B) :
    S ⊆ output G ids s ∧
      (∀ r ∈ W, ∃ v ∈ output G ids s, v ∈ C r) ∧
      (output G ids s \ S).card ≤ W.card ∧
      output G ids s ⊆ CoveringSupport.admissible C R0 ∧
      (∑ v ∈ output G ids s \ S, c v) ≤ (B : ℝ) * W.card ∧
      ∀ r, ((program ids).run G s r).uncovered =
        decide (r ∈ R ∧ C r ∩ output G ids s = ∅) := by
  have hout := output_eq G ids C R S W s hS hW hR hC hWR hlocal
  rw [hout]
  refine ⟨selected_subset C S W, covers_requesters C S W hne, new_card C S W,
    admissible C R0 S W (hWR.trans hRR) hSad,
    new_cost C R0 S W (hWR.trans hRR) B c hc, ?_⟩
  intro r
  rw [correct G ids C R S W s hS hW hR hC hWR hlocal]
  simp only [residual, Finset.mem_filter]

theorem correct_encoded {b : ℕ} (ids : BitCode V b) (C : V → Finset V) (R S W : Finset V)
    (s : V → Input V)
    (hS : ∀ v, (s v).selected = decide (v ∈ S))
    (hW : ∀ v, (s v).requester = decide (v ∈ W))
    (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = C v) (hWR : W ⊆ R)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    (program ids).runEncoded G s = fun v =>
      ⟨decide (v ∈ selectedPlus C S W), decide (v ∈ residual C R S W)⟩ := by
  rw [Program.runEncoded_eq_run]
  exact correct G ids C R S W s hS hW hR hC hWR hlocal

end Paper.GeneralCoveringRequests

#print axioms Paper.GeneralCoveringRequests.message_minimum
#print axioms Paper.GeneralCoveringRequests.correct
#print axioms Paper.GeneralCoveringRequests.correct_encoded
#print axioms Paper.GeneralCoveringRequests.covers_requesters
#print axioms Paper.GeneralCoveringRequests.new_card
#print axioms Paper.GeneralCoveringRequests.admissible
#print axioms Paper.GeneralCoveringRequests.new_cost
#print axioms Paper.GeneralCoveringRequests.spec
#print axioms Paper.GeneralCoveringRequests.rounds
#print axioms Paper.GeneralCoveringRequests.maxBits

#print axioms Paper.GeneralCoveringRequests.self_request_selected
