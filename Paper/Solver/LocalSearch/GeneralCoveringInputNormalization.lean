import Paper.Solver.LocalSearch.GeneralCoveringFractional
import Paper.Communication.EncodedProgram
import Paper.Preliminaries.CohostKnown
import Paper.Certificates.Counting.CoveringSupport

/-! One demand-bit broadcast normalizes the private arbitrary-C input.
Only demanded original rows must be physically local. The executable reads
its own demand and actual neighbor messages, trims both incidence lists and
sets the cost to one exactly when its retained inverse list is empty.
B >= 1 is explicit. R and admissibility occur only in the specification. -/
namespace Paper.GeneralCoveringInputNormalization
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractional.Input

def one (B : ℕ) (hB : 1 ≤ B) : Fin (B + 1) := ⟨1, by omega⟩

def retainedTargets {B : ℕ} (v : V) (N : Finset V) (s : Input V B)
    (incoming : N → Bool) : Finset V :=
  s.targets.filter (fun r => CohostKnown.read v N s.demand incoming r)

def update (B : ℕ) (hB : 1 ≤ B) (v : V) (N : Finset V)
    (s : Input V B) (incoming : N → Bool) : Input V B :=
  let targets := retainedTargets v N s incoming
  { active := s.active
    cost := if targets.Nonempty then s.cost else one B hB
    demand := s.demand
    candidates := if s.demand then s.candidates else ∅
    targets := targets }

def round (B : ℕ) (hB : 1 ≤ B) : Round V (Input V B) (Input V B) Bool where
  send _ _ s := s.demand
  update := update B hB

def program (B : ℕ) (hB : 1 ≤ B) : Program V (Input V B) (Input V B) :=
  .broadcast 1 BitCode.bool (round B hB)

/-- Mathematical specification of the trimmed rows, not a runtime input. -/
def trimmed (cover : V → Finset V) (R : Finset V) (r : V) : Finset V :=
  if r ∈ R then cover r else ∅

theorem mem_trimmed (cover : V → Finset V) (R : Finset V) (r v : V) :
    v ∈ trimmed cover R r ↔ r ∈ R ∧ v ∈ cover r := by
  by_cases hr : r ∈ R <;> simp [trimmed, hr]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program (B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) (v : V) :
    (program B hB).runEncoded G s v =
      update B hB v (G.neighborFinset v) (s v) (fun u => (s u.val).demand) := by
  rw [Program.runEncoded_eq_run]
  rfl

def heard {B : ℕ} (s : V → Input V B) (v r : V) : Bool :=
  CohostKnown.read v (G.neighborFinset v) (s v).demand (fun u => (s u.val).demand) r

/-- A true observed flag always comes from its real sender, including self. -/
theorem heard_sound {B : ℕ} (R : Finset V) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (v r : V)
    (h : heard G s v r = true) : r ∈ R := by
  by_cases he : r = v
  · subst r
    simpa only [heard, CohostKnown.read, if_pos rfl, if_true, hd, decide_eq_true_eq] using h
  · by_cases hn : r ∈ G.neighborFinset v
    · simpa only [heard, CohostKnown.read, if_neg he, dif_pos hn, hd,
        decide_eq_true_eq] using h
    · simp only [heard, CohostKnown.read, if_neg he, dif_neg hn,
        Bool.false_eq_true] at h

theorem heard_local {B : ℕ} (R : Finset V) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (v r : V) (hr : r ∈ closed G v) :
    heard G s v r = decide (r ∈ R) := by
  unfold heard
  simp only [hd]
  exact CohostKnown.read_correct G R v r hr

section Incidences
variable (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    {B : ℕ} (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (ht : ∀ v, (s v).targets = targets v)

include hinc hlocal hd ht in
theorem retainedTargets_eq (v : V) :
    retainedTargets v (G.neighborFinset v) (s v) (fun u => (s u.val).demand) =
      targets v ∩ R := by
  ext r
  change r ∈ (s v).targets.filter (fun r => heard G s v r) ↔ r ∈ targets v ∩ R
  rw [ht v]
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hr, hh⟩
    exact ⟨hr, heard_sound G R s hd v r hh⟩
  · rintro ⟨hr, hrR⟩
    have hv : v ∈ cover r := (hinc v r).mp hr
    have hnear : r ∈ closed G v := (closed_symm G v r).mp (hlocal r hrR hv)
    exact ⟨hr, (heard_local G R s hd v r hnear).trans (decide_eq_true hrR)⟩

include hinc hlocal hd ht in
theorem targets_eq (hB : 1 ≤ B) (v : V) :
    ((program B hB).runEncoded G s v).targets = targets v ∩ R := by
  rw [run_program]
  exact retainedTargets_eq G cover targets R hinc hlocal s hd ht v

include hinc in
theorem inverse_nonempty (v : V) :
    (targets v ∩ R).Nonempty ↔ v ∈ CoveringSupport.admissible cover R := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hrt, hrR⟩ := Finset.mem_inter.mp hr
    exact Finset.mem_biUnion.mpr ⟨r, hrR, (hinc v r).mp hrt⟩
  · intro hv
    obtain ⟨r, hrR, hvr⟩ := Finset.mem_biUnion.mp hv
    exact ⟨r, Finset.mem_inter.mpr ⟨(hinc v r).mpr hvr, hrR⟩⟩

include hinc hlocal hd ht in
theorem admissible_iff (hB : 1 ≤ B) (v : V) :
    (((program B hB).runEncoded G s v).targets).Nonempty ↔
      v ∈ CoveringSupport.admissible cover R := by
  rw [targets_eq G cover targets R hinc hlocal s hd ht hB v]
  exact inverse_nonempty cover targets R hinc v

include hinc hlocal hd ht in
theorem cost_eq (hB : 1 ≤ B) (v : V) :
    ((program B hB).runEncoded G s v).cost =
      if v ∈ CoveringSupport.admissible cover R then (s v).cost else one B hB := by
  rw [run_program]
  change (if (retainedTargets v (G.neighborFinset v) (s v)
    (fun u => (s u.val).demand)).Nonempty then (s v).cost else one B hB) = _
  rw [retainedTargets_eq G cover targets R hinc hlocal s hd ht v]
  by_cases hv : v ∈ CoveringSupport.admissible cover R
  · rw [if_pos ((inverse_nonempty cover targets R hinc v).mpr hv), if_pos hv]
  · rw [if_neg (fun hn => hv ((inverse_nonempty cover targets R hinc v).mp hn)), if_neg hv]

include hinc hlocal hd ht in
theorem positive (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (s v).cost.val) (v : V) :
    1 ≤ ((program B hB).runEncoded G s v).cost.val := by
  rw [cost_eq G cover targets R hinc hlocal s hd ht hB v]
  by_cases hv : v ∈ CoveringSupport.admissible cover R
  · rw [if_pos hv]
    exact hc v hv
  · rw [if_neg hv]
    exact le_refl 1

include hinc hlocal hd ht in
theorem supported_cost (hB : 1 ≤ B) (O : Finset V)
    (hO : O ⊆ CoveringSupport.admissible cover R) :
    (∑ v ∈ O, ((program B hB).runEncoded G s v).cost.val) =
      ∑ v ∈ O, (s v).cost.val := by
  apply Finset.sum_congr rfl
  intro v hv
  rw [cost_eq G cover targets R hinc hlocal s hd ht hB v, if_pos (hO hv)]

include hinc hlocal hd ht in
theorem supported_objective (hB : 1 ≤ B) (x : V → ℝ)
    (hx : ∀ v, v ∉ CoveringSupport.admissible cover R → x v = 0) :
    (∑ v, (((program B hB).runEncoded G s v).cost.val : ℝ) * x v) =
      ∑ v, ((s v).cost.val : ℝ) * x v := by
  apply Finset.sum_congr rfl
  intro v _
  rw [cost_eq G cover targets R hinc hlocal s hd ht hB v]
  by_cases hv : v ∈ CoveringSupport.admissible cover R
  · rw [if_pos hv]
  · rw [hx v hv]
    simp only [mul_zero]
end Incidences

theorem metadata (B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) (v : V) :
    ((program B hB).runEncoded G s v).active = (s v).active ∧
      ((program B hB).runEncoded G s v).demand = (s v).demand := by
  rw [run_program]
  exact ⟨rfl, rfl⟩

theorem candidates_eq (cover : V → Finset V) (R : Finset V) {B : ℕ}
    (hB : 1 ≤ B) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (r : V) :
    ((program B hB).runEncoded G s r).candidates = trimmed cover R r := by
  rw [run_program]
  change (if (s r).demand then (s r).candidates else ∅) = _
  rw [hd r, hC r]
  by_cases hr : r ∈ R <;> simp [trimmed, hr]

section Contract
variable (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)

include hinc hlocal hd hC ht in
theorem agreement (v r : V) :
    r ∈ ((program B hB).runEncoded G s v).targets ↔
      v ∈ ((program B hB).runEncoded G s r).candidates := by
  rw [targets_eq G cover targets R hinc hlocal s hd ht hB v,
    candidates_eq G cover R hB s hd hC r]
  simp only [Finset.mem_inter, mem_trimmed, hinc]
  exact and_comm

include hlocal hd hC in
/-- All rows are local after execution, including arbitrary old zero-demand rows. -/
theorem locality (r : V) :
    ((program B hB).runEncoded G s r).candidates ⊆ closed G r := by
  rw [candidates_eq G cover R hB s hd hC r]
  intro v hv
  obtain ⟨hr, hvr⟩ := (mem_trimmed cover R r v).mp hv
  exact hlocal r hr hvr

include hd hC in
theorem admissibility :
    CoveringSupport.admissible (fun r => ((program B hB).runEncoded G s r).candidates) R =
      CoveringSupport.admissible cover R := by
  ext v
  simp only [CoveringSupport.admissible, Finset.mem_biUnion,
    candidates_eq G cover R hB s hd hC, mem_trimmed]
  constructor
  · rintro ⟨r, hr, _, hvr⟩
    exact ⟨r, hr, hvr⟩
  · rintro ⟨r, hr, hvr⟩
    exact ⟨r, hr, hr, hvr⟩

include hd hC in
theorem integral_covers (O : Finset V) :
    (∀ r ∈ R, ∃ v ∈ O, v ∈ ((program B hB).runEncoded G s r).candidates) ↔
      (∀ r ∈ R, ∃ v ∈ O, v ∈ cover r) := by
  constructor
  · intro h r hr
    obtain ⟨v, hvO, hv⟩ := h r hr
    rw [candidates_eq G cover R hB s hd hC r] at hv
    exact ⟨v, hvO, ((mem_trimmed cover R r v).mp hv).2⟩
  · intro h r hr
    obtain ⟨v, hvO, hv⟩ := h r hr
    refine ⟨v, hvO, ?_⟩
    rw [candidates_eq G cover R hB s hd hC r]
    exact (mem_trimmed cover R r v).mpr ⟨hr, hv⟩

include hd hC in
theorem admissible_integral_covers (O : Finset V) :
    (O ⊆ CoveringSupport.admissible
        (fun r => ((program B hB).runEncoded G s r).candidates) R ∧
      ∀ r ∈ R, ∃ v ∈ O, v ∈ ((program B hB).runEncoded G s r).candidates) ↔
      (O ⊆ CoveringSupport.admissible cover R ∧ ∀ r ∈ R, ∃ v ∈ O, v ∈ cover r) := by
  rw [admissibility G cover R hB s hd hC,
    integral_covers G cover R hB s hd hC O]

include hinc hlocal hd hC ht in
theorem empty_demand (hR : R = ∅) (v : V) :
    ((program B hB).runEncoded G s v).candidates = ∅ ∧
      ((program B hB).runEncoded G s v).targets = ∅ ∧
      ((program B hB).runEncoded G s v).cost = one B hB := by
  rw [candidates_eq G cover R hB s hd hC v,
    targets_eq G cover targets R hinc hlocal s hd ht hB v,
    cost_eq G cover targets R hinc hlocal s hd ht hB v, hR]
  simp [trimmed, CoveringSupport.admissible]
end Contract

theorem rounds (B : ℕ) (hB : 1 ≤ B) : (program (V := V) B hB).rounds = 1 := rfl

theorem maxBits (B : ℕ) (hB : 1 ≤ B) : (program (V := V) B hB).maxBits = 1 := rfl
end Paper.GeneralCoveringInputNormalization

#print axioms Paper.GeneralCoveringInputNormalization.run_program
#print axioms Paper.GeneralCoveringInputNormalization.metadata
#print axioms Paper.GeneralCoveringInputNormalization.agreement
#print axioms Paper.GeneralCoveringInputNormalization.locality
#print axioms Paper.GeneralCoveringInputNormalization.positive
#print axioms Paper.GeneralCoveringInputNormalization.admissible_integral_covers
#print axioms Paper.GeneralCoveringInputNormalization.supported_cost
#print axioms Paper.GeneralCoveringInputNormalization.supported_objective
#print axioms Paper.GeneralCoveringInputNormalization.empty_demand
#print axioms Paper.GeneralCoveringInputNormalization.rounds
#print axioms Paper.GeneralCoveringInputNormalization.maxBits
