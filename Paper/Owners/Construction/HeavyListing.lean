import Paper.Owners.Construction.HeavyEligibility
import Paper.Preliminaries.SelectCorrect

/-! Actual bounded-size heavy branching list: exact demand count,
one-bit neighborhood incidence, and repeated minimum-ID queries. -/
namespace Paper.HeavyListing
open BroadcastModel
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (D a m : ℕ) :=
  Program.seq (HeavyEligibility.program C D m) (SelectProtocol.program C D (2 * a * m))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem physical_task {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (A : Finset V)
    (hA : A ⊆ PhysicalTasks.vertices G D R L Q I) (a m : ℕ)
    (ha : 1 ≤ a) (hm : 1 ≤ m) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (hlarge : 2 * (a + 1) * m ≤ A.card) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      (((program C (4 * k) a m).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), decide (u ∈ A))) v).chosen.toFinset =
          PhysicalTasks.vertices G D R L Q I ∩ LocalSearchBounds.heavy G A m) ∧
      ((program C (4 * k) a m).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), decide (u ∈ A))) v).chosen.Nodup ∧
      ((program C (4 * k) a m).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), decide (u ∈ A))) v).chosen.length ≤ 2 * a * m := by
  let H := PhysicalTasks.vertices G D R L Q I
  let active : V → Bool := fun v => decide (v ∈ H)
  let input : V → Bool × Bool := fun v => (active v, decide (v ∈ A))
  let E : V → Bool := fun v => ((HeavyEligibility.program C (4 * k) m).run G input v).2
  have hE (v : V) (hv : v ∈ H) : E v =
      decide (A.card ≤ m * (SevenFoundation.closed G v ∩ A).card) :=
    HeavyEligibility.physical_task G C D R L Q I hI k hsize A hA m v hv
  have he : SelectStep.candidates active E = H ∩ LocalSearchBounds.heavy G A m := by
    ext v
    by_cases hv : v ∈ H
    · simp [SelectStep.candidates, active, hv, hE v hv, LocalSearchBounds.heavy]
    · simp [SelectStep.candidates, active, hv]
  have hheavy : (LocalSearchBounds.heavy G A m).card ≤ 2 * a * m := by
    exact_mod_cast LocalSearchBounds.heavy_card_le G A m hm
      (by exact_mod_cast ha : (1 : ℝ) ≤ a) hden (by exact_mod_cast hlarge)
  have hcount : (SelectStep.candidates active E).card ≤ 2 * a * m := by
    rw [he]
    exact (Finset.card_le_card (Finset.inter_subset_right :
      H ∩ LocalSearchBounds.heavy G A m ⊆ LocalSearchBounds.heavy G A m)).trans hheavy
  obtain ⟨hne, hs, _, _⟩ := TaskTree.spec G C D R L Q I hI k hsize
  have har : active (H.min' hne) = true := decide_eq_true (Finset.min'_mem _ hne)
  have hi : (HeavyEligibility.program C (4 * k) m).run G input = fun v => (active v, E v) := by
    funext v
    exact Prod.ext (HeavyEligibility.active G C (4 * k) m input v) rfl
  have hrun : (program C (4 * k) a m).run G input =
      (SelectProtocol.program C (4 * k) (2 * a * m)).run G (fun v => (active v, E v)) := by
    change (SelectProtocol.program C (4 * k) (2 * a * m)).run G
      ((HeavyEligibility.program C (4 * k) m).run G input) = _
    rw [hi]
  intro v hv
  have hc := SelectCorrect.complete G C (4 * k) active E (H.min' hne) hs har
    (2 * a * m) hcount v (decide_eq_true hv)
  change (((program C (4 * k) a m).run G input v).chosen.toFinset =
      H ∩ LocalSearchBounds.heavy G A m) ∧
    ((program C (4 * k) a m).run G input v).chosen.Nodup ∧
    ((program C (4 * k) a m).run G input v).chosen.length ≤ 2 * a * m
  simpa only [hrun, he] using hc

theorem rounds {b : ℕ} (C : BitCode V b) (D a m : ℕ) :
    (program C D a m).rounds = (2 * a * m + 1) * (4 * D + 1) + 1 := by
  simp only [program, Program.rounds, HeavyEligibility.rounds, SelectCorrect.rounds]
  ring

theorem maxBits {b : ℕ} (C : BitCode V b) (D a m : ℕ) :
    (program C D a m).maxBits ≤ max (3 * b + 3) (D + 2) := by
  apply max_le (HeavyEligibility.maxBits C D m)
  apply (SelectCorrect.maxBits C D (2 * a * m)).trans
  exact max_le (by omega) (le_max_right _ _)

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (k a m n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C (4 * k) a m).maxBits ≤
      (3 * (c + 1) + 4 * k + 2) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hb : 3 * b + 3 ≤ (3 * (c + 1)) * Nat.clog 2 (n + 2) := by nlinarith
  have hd : 4 * k + 2 ≤ (4 * k + 2) * Nat.clog 2 (n + 2) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * k + 2) hl
  apply (maxBits C (4 * k) a m).trans
  apply max_le <;> nlinarith
end Paper.HeavyListing
