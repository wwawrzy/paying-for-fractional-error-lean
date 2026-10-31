import Paper.Solver.LocalSearch.GeneralCoveringRequests
import Paper.Preliminaries.CostTag

/-! Three broadcast rounds implement threshold selection and cheapest requests.
The first round sends every candidate's cost, including candidates below the
threshold. Private covering lists are never sent. -/

namespace Paper.CoveringRoundingProtocol

open BroadcastModel SevenFoundation

variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B : ℕ) where
  selected : Bool
  demand : Bool
  cost : Fin (B + 1)
  candidates : Finset V

def localCost {B : ℕ} (v : V) (N : Finset V) (s : Input V B)
    (msg : N → Bool × Fin (B + 1)) (u : V) : Fin (B + 1) :=
  if u = v then s.cost else if h : u ∈ N then (msg ⟨u, h⟩).2 else 0

def choice {B : ℕ} (C : Finset V) (c : V → Fin (B + 1)) : Option V :=
  (MaskedMinimum.minimum (C.image (CostTag.tag c))).map (fun t => (ofLex t).2)

def prepareRound (B : ℕ) :
    Round V (Input V B) (GeneralCoveringRequests.Input V) (Bool × Fin (B + 1)) where
  send _ _ s := (s.selected, s.cost)
  update v N s msg :=
    ⟨s.selected,
      s.demand && decide (s.candidates ∩
        FlagNeighborhood.selected v N s.selected (fun u => (msg u).1) = ∅),
      s.demand,
      (choice s.candidates (localCost v N s msg)).toFinset⟩

def program {b : ℕ} (ids : BitCode V b) (B : ℕ) :
    Program V (Input V B) GeneralCoveringRequests.Output :=
  .seq (.broadcast (1 + (B + 1))
    (PacketCode.product BitCode.bool (SmallNumberCode.code (B + 1)))
    (prepareRound B)) (GeneralCoveringRequests.program ids)

theorem rounds {b : ℕ} (ids : BitCode V b) (B : ℕ) :
    (program ids B).rounds = 3 := rfl

theorem maxBits {b : ℕ} (ids : BitCode V b) (B : ℕ) :
    (program ids B).maxBits ≤ max (B + 2) (b + 1) := by
  change max (1 + (B + 1)) (max (b + 1) 1) ≤ _
  omega

variable [Fintype V]

theorem choice_spec {B : ℕ} (C : Finset V) (c : V → Fin (B + 1))
    (hne : C.Nonempty) :
    ∃ u, choice C c = some u ∧ u ∈ C ∧ ∀ w ∈ C, (c u).val ≤ (c w).val := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨t, ht, _⟩ := MaskedMinimum.minimum_le (Finset.mem_image.mpr ⟨v, hv, rfl⟩ :
    CostTag.tag c v ∈ C.image (CostTag.tag c))
  have h := CostTag.least_cost c C ht
  exact ⟨(ofLex t).2, by simp [choice, ht], h.1, h.2.2⟩

theorem choice_mem {B : ℕ} (C : Finset V) (c : V → Fin (B + 1)) {u : V}
    (hu : u ∈ (choice C c).toFinset) : u ∈ C := by
  unfold choice at hu
  cases ht : MaskedMinimum.minimum (C.image (CostTag.tag c)) with
  | none => simp [ht] at hu
  | some t =>
    have he : (ofLex t).2 = u := by simpa [ht, eq_comm] using hu
    exact he ▸ (CostTag.least_cost c C ht).1

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem localCost_correct {B : ℕ} (s : V → Input V B) (v u : V)
    (hu : u ∈ closed G v) :
    localCost v (G.neighborFinset v) (s v)
      (fun w => ((s w.val).selected, (s w.val).cost)) u = (s u).cost := by
  rcases (mem_closed G u v).mp hu with he | ha
  · subst u
    simp [localCost]
  · have hn : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr ha
    by_cases he : u = v
    · subst u; simp [localCost]
    · simp [localCost, he, hn]

def cheapestRows {B : ℕ} (s : V → Input V B) (v : V) : Finset V :=
  (choice (s v).candidates (fun u => (s u).cost)).toFinset

def residual {B : ℕ} (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun r => (s r).demand = true ∧
    (s r).candidates ∩ Finset.univ.filter (fun v => (s v).selected = true) = ∅)

/-- On actual demands, the first round reconstructs the true cheapest row
and the exact residual bit from one cost/threshold message per neighbor. -/
theorem prepare_correct {B : ℕ} (s : V → Input V B)
    (hlocal : ∀ r, (s r).candidates ⊆ closed G r) :
    eval G (prepareRound B) s = fun v =>
      ⟨(s v).selected, decide (v ∈ residual s), (s v).demand, cheapestRows s v⟩ := by
  funext v
  have hc : (s v).candidates.image
      (CostTag.tag (localCost v (G.neighborFinset v) (s v)
        (fun u => ((s u.val).selected, (s u.val).cost)))) =
      (s v).candidates.image (CostTag.tag (fun u => (s u).cost)) := by
    apply Finset.image_congr
    intro u hu
    simp only [CostTag.tag, localCost_correct G s v u (hlocal v hu)]
  have hchoice : choice (s v).candidates
      (localCost v (G.neighborFinset v) (s v)
        (fun u => ((s u.val).selected, (s u.val).cost))) =
      choice (s v).candidates (fun u => (s u).cost) := by
    simp only [choice, hc]
  let S := Finset.univ.filter (fun u => (s u).selected = true)
  have hf : (fun u => decide (u ∈ S)) = fun u => (s u).selected := by
    funext u
    simp [S]
  have hn := FlagNeighborhood.correct G S v
  rw [hf] at hn
  have hi : (s v).candidates ∩ (closed G v ∩ S) = (s v).candidates ∩ S := by
    ext u
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨h, _, hs⟩; exact ⟨h, hs⟩
    · rintro ⟨h, hs⟩; exact ⟨h, hlocal v h, hs⟩
  change GeneralCoveringRequests.Input.mk _ _ _ _ = _
  dsimp only [prepareRound]
  rw [hchoice]
  change GeneralCoveringRequests.Input.mk _
    ((s v).demand && decide ((s v).candidates ∩
      FlagNeighborhood.program.run G (fun u => (s u).selected) v = ∅)) _ _ = _
  rw [hn, hi]
  simp [residual, cheapestRows, S]

def output {b B : ℕ} (ids : BitCode V b) (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => ((program ids B).runEncoded G s v).selected = true)

/-- The complete encoded execution selects precisely the threshold set and
one least-cost, least-ID candidate for each residual demand. -/
theorem output_eq {b B : ℕ} (ids : BitCode V b) (s : V → Input V B)
    (hlocal : ∀ r, (s r).candidates ⊆ closed G r) :
    output G ids s = GeneralCoveringRequests.selectedPlus (cheapestRows s)
      (Finset.univ.filter (fun v => (s v).selected = true)) (residual s) := by
  let S := Finset.univ.filter (fun v => (s v).selected = true)
  let R := Finset.univ.filter (fun v => (s v).demand = true)
  let t : V → GeneralCoveringRequests.Input V := fun v =>
    ⟨(s v).selected, decide (v ∈ residual s), (s v).demand, cheapestRows s v⟩
  have hW : residual s ⊆ R := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.1⟩
  have hC : ∀ r ∈ R, cheapestRows s r ⊆ closed G r := by
    intro r _ u hu
    exact hlocal r (choice_mem (s r).candidates (fun w => (s w).cost) hu)
  have h := GeneralCoveringRequests.output_eq G ids (cheapestRows s) R S (residual s) t
    (by intro v; simp [t, S]) (by intro v; rfl)
    (by intro v; simp [t, R]) (by intro v; rfl) hW hC
  unfold output
  rw [Program.runEncoded_eq_run]
  change Finset.univ.filter (fun v =>
    ((GeneralCoveringRequests.program ids).run G (eval G (prepareRound B) s) v).selected = true) = _
  rw [prepare_correct G s hlocal]
  exact h

/-- Rows outside the demand set are private irrelevant data. The local
normalization removes them before any message is sent. -/
def normalized {B : ℕ} (s : Input V B) : Input V B :=
  { s with candidates := if s.demand then s.candidates else ∅ }

def normalizedProgram {b : ℕ} (ids : BitCode V b) (B : ℕ) :
    Program V (Input V B) GeneralCoveringRequests.Output :=
  .seq (.local (fun _ _ s => normalized s)) (program ids B)

omit [Fintype V] in
theorem normalized_rounds {b : ℕ} (ids : BitCode V b) (B : ℕ) :
    (normalizedProgram ids B).rounds = 3 := rfl

omit [Fintype V] in
theorem normalized_maxBits {b : ℕ} (ids : BitCode V b) (B : ℕ) :
    (normalizedProgram ids B).maxBits ≤ max (B + 2) (b + 1) := by
  change max 0 (program ids B).maxBits ≤ _
  exact max_le (Nat.zero_le _) (maxBits ids B)

theorem normalized_output_eq {b B : ℕ} (ids : BitCode V b) (s : V → Input V B)
    (hlocal : ∀ r, (s r).demand = true → (s r).candidates ⊆ closed G r) :
    (Finset.univ.filter (fun v =>
      ((normalizedProgram ids B).runEncoded G s v).selected = true)) =
      GeneralCoveringRequests.selectedPlus (cheapestRows (fun v => normalized (s v)))
        (Finset.univ.filter (fun v => (s v).selected = true)) (residual s) := by
  have hl : ∀ r, (normalized (s r)).candidates ⊆ closed G r := by
    intro r
    by_cases h : (s r).demand = true
    · simpa [normalized, h] using hlocal r h
    · simp [normalized, h]
  have hr : residual (fun v => normalized (s v)) = residual s := by
    ext r
    by_cases h : (s r).demand = true <;> simp [residual, normalized, h] <;> rfl
  have hout := output_eq G ids (fun v => normalized (s v)) hl
  rw [hr] at hout
  simpa only [output, Program.runEncoded_eq_run, normalizedProgram,
    Program.run, normalized] using hout

end Paper.CoveringRoundingProtocol

#print axioms Paper.CoveringRoundingProtocol.choice_spec
#print axioms Paper.CoveringRoundingProtocol.choice_mem
#print axioms Paper.CoveringRoundingProtocol.prepare_correct
#print axioms Paper.CoveringRoundingProtocol.rounds
#print axioms Paper.CoveringRoundingProtocol.maxBits

#print axioms Paper.CoveringRoundingProtocol.output_eq

#print axioms Paper.CoveringRoundingProtocol.normalized_output_eq
#print axioms Paper.CoveringRoundingProtocol.normalized_rounds
#print axioms Paper.CoveringRoundingProtocol.normalized_maxBits
