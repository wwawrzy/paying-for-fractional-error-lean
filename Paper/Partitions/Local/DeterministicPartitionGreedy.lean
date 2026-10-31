import Mathlib

/-! The executable greedy sweep processes one candidate color at a time.
Eligibility is fixed at the start of the stage. A batch is tested against
all earlier accepted sets, and equally colored candidates are disjoint. -/
namespace Paper.DeterministicPartitionGreedy
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

/-- Candidates of this color that avoid every earlier accepted set. -/
def batch (E : Finset (Finset V)) (color : Finset V → ℕ)
    (A : Finset (Finset V)) (i : ℕ) : Finset (Finset V) :=
  E.filter (fun U => color U = i ∧ ∀ W ∈ A, Disjoint U W)

/-- Actual finite color sweep, starting with no accepted sets. -/
def run (E : Finset (Finset V)) (color : Finset V → ℕ) : ℕ → Finset (Finset V)
  | 0 => ∅
  | n + 1 => run E color n ∪ batch E color (run E color n) n

theorem congr_colors (E : Finset (Finset V)) (color other : Finset V → ℕ)
    (hcolor : ∀ U ∈ E, color U = other U) (n : ℕ) :
    run E color n = run E other n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    apply congrArg (fun B => run E other n ∪ B)
    ext U
    simp only [batch, Finset.mem_filter]
    constructor
    · rintro ⟨hU, hc, ha⟩
      exact ⟨hU, (hcolor U hU).symm.trans hc, ha⟩
    · rintro ⟨hU, hc, ha⟩
      exact ⟨hU, (hcolor U hU).trans hc, ha⟩

/-- Properness of a candidate coloring, expressed directly on the sets. -/
def Proper (E : Finset (Finset V)) (color : Finset V → ℕ) : Prop :=
  ∀ U ∈ E, ∀ W ∈ E, color U = color W → U ≠ W → Disjoint U W

def removed (E : Finset (Finset V)) (color : Finset V → ℕ) (n : ℕ) : Finset V :=
  (run E color n).biUnion id

theorem mem_batch (E : Finset (Finset V)) (color : Finset V → ℕ)
    (A : Finset (Finset V)) (i : ℕ) (U : Finset V) :
    U ∈ batch E color A i ↔ U ∈ E ∧ color U = i ∧ ∀ W ∈ A, Disjoint U W := by
  simp only [batch, Finset.mem_filter]

theorem step (E : Finset (Finset V)) (color : Finset V → ℕ) (n : ℕ) :
    run E color n ⊆ run E color (n + 1) := Finset.subset_union_left

theorem mono (E : Finset (Finset V)) (color : Finset V → ℕ) {m n : ℕ} (h : m ≤ n) :
    run E color m ⊆ run E color n := by
  induction n, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n _ ih => exact ih.trans (step E color n)

theorem subset (E : Finset (Finset V)) (color : Finset V → ℕ) (n : ℕ) :
    run E color n ⊆ E := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    intro U hU
    rcases Finset.mem_union.mp hU with hU | hU
    · exact ih hU
    · exact (mem_batch E color _ n U).mp hU |>.1

theorem processed (E : Finset (Finset V)) (color : Finset V → ℕ) (n : ℕ)
    (U : Finset V) (hU : U ∈ run E color n) : color U < n := by
  induction n with
  | zero => exact False.elim (Finset.notMem_empty U hU)
  | succ n ih =>
    rcases Finset.mem_union.mp hU with hU | hU
    · exact Nat.lt.step (ih hU)
    · have he := ((mem_batch E color _ n U).mp hU).2.1
      omega

theorem disjoint (E : Finset (Finset V)) (color : Finset V → ℕ)
    (hc : Proper E color) (n : ℕ) :
    (run E color n : Set (Finset V)).Pairwise Disjoint := by
  induction n with
  | zero => intro U hU; exact False.elim (Finset.notMem_empty U hU)
  | succ n ih =>
    intro U hU W hW hne
    rcases Finset.mem_union.mp hU with hU | hU <;>
      rcases Finset.mem_union.mp hW with hW | hW
    · exact ih hU hW hne
    · exact (((mem_batch E color _ n W).mp hW).2.2 U hU).symm
    · exact ((mem_batch E color _ n U).mp hU).2.2 W hW
    · have hu := (mem_batch E color _ n U).mp hU
      have hw := (mem_batch E color _ n W).mp hW
      exact hc U hu.1 W hw.1 (hu.2.1.trans hw.2.1.symm) hne

/-- Every processed eligible set intersects an accepted set, including
itself when it was accepted. This theorem uses the actual sweep. -/
theorem dominates (E : Finset (Finset V)) (color : Finset V → ℕ)
    (hne : ∀ U ∈ E, U.Nonempty) (n : ℕ) :
    ∀ U ∈ E, color U < n → ∃ W ∈ run E color n, ¬ Disjoint U W := by
  induction n with
  | zero => intro U hU hc; omega
  | succ n ih =>
    intro U hU hc
    by_cases hlt : color U < n
    · obtain ⟨W, hW, hd⟩ := ih U hU hlt
      exact ⟨W, step E color n hW, hd⟩
    · have he : color U = n := by omega
      by_cases hex : ∃ W ∈ run E color n, ¬ Disjoint U W
      · obtain ⟨W, hW, hd⟩ := hex
        exact ⟨W, step E color n hW, hd⟩
      · have hd : ∀ W ∈ run E color n, Disjoint U W := by
          intro W hW
          by_contra hn
          exact hex ⟨W, hW, hn⟩
        refine ⟨U, Finset.mem_union_right _
          ((mem_batch E color _ n U).mpr ⟨hU, he, hd⟩), ?_⟩
        obtain ⟨v, hv⟩ := hne U hU
        exact fun h => Finset.disjoint_left.mp h hv hv

theorem removed_subset (E : Finset (Finset V)) (color : Finset V → ℕ)
    (n : ℕ) (S : Finset V) (hs : ∀ U ∈ E, U ⊆ S) : removed E color n ⊆ S := by
  intro v hv
  obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
  exact hs U (subset E color n hU) hv

theorem removed_card (E : Finset (Finset V)) (color : Finset V → ℕ)
    (hc : Proper E color) (n : ℕ) :
    (removed E color n).card = ∑ U ∈ run E color n, U.card :=
  Finset.card_biUnion (disjoint E color hc n)

theorem accepted_le_removed (E : Finset (Finset V)) (color : Finset V → ℕ)
    (hc : Proper E color) (hne : ∀ U ∈ E, U.Nonempty) (n : ℕ) :
    (run E color n).card ≤ (removed E color n).card := by
  rw [removed_card E color hc n]
  calc
    _ = ∑ _U ∈ run E color n, 1 := by simp
    _ ≤ ∑ U ∈ run E color n, U.card := by
      apply Finset.sum_le_sum
      intro U hU
      exact (hne U (subset E color n hU)).card_pos

/-- Intersecting candidates include the accepted set itself. -/
def touching (E : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  E.filter (fun W => ¬ Disjoint W U)

theorem candidate_count (E : Finset (Finset V)) (color : Finset V → ℕ)
    (hne : ∀ U ∈ E, U.Nonempty) (q M : ℕ)
    (hpalette : ∀ U ∈ E, color U < q)
    (htouch : ∀ U ∈ E, (touching E U).card ≤ M) :
    E.card ≤ M * (run E color q).card := by
  have hcover : E ⊆ (run E color q).biUnion (touching E) := by
    intro U hU
    obtain ⟨W, hW, hd⟩ := dominates E color hne q U hU (hpalette U hU)
    exact Finset.mem_biUnion.mpr ⟨W, hW, Finset.mem_filter.mpr ⟨hU, hd⟩⟩
  calc
    _ ≤ ((run E color q).biUnion (touching E)).card := Finset.card_le_card hcover
    _ ≤ ∑ U ∈ run E color q, (touching E U).card := Finset.card_biUnion_le
    _ ≤ ∑ _U ∈ run E color q, M := by
      apply Finset.sum_le_sum
      intro U hU
      exact htouch U (subset E color q hU)
    _ = _ := by simp [Nat.mul_comm]

/-- The union bound suffices even if eligible sets overlap. -/
theorem covered_count (E : Finset (Finset V)) (k : ℕ)
    (hsize : ∀ U ∈ E, U.card ≤ k) : (E.biUnion id).card ≤ k * E.card := by
  calc
    _ ≤ ∑ U ∈ E, U.card := Finset.card_biUnion_le
    _ ≤ ∑ _U ∈ E, k := Finset.sum_le_sum hsize
    _ = _ := by simp [Nat.mul_comm]

/-- Deterministic one-stage progress from half coverage and bounded conflicts. -/
theorem half_progress (E : Finset (Finset V)) (color : Finset V → ℕ)
    (hc : Proper E color) (hne : ∀ U ∈ E, U.Nonempty) (q k M : ℕ)
    (hpalette : ∀ U ∈ E, color U < q)
    (hsize : ∀ U ∈ E, U.card ≤ k)
    (htouch : ∀ U ∈ E, (touching E U).card ≤ M)
    (S : Finset V) (hhalf : S.card ≤ 2 * (E.biUnion id).card) :
    S.card ≤ (2 * k * M) * (removed E color q).card := by
  have h1 := covered_count E k hsize
  have h2 := candidate_count E color hne q M hpalette htouch
  have h3 := accepted_le_removed E color hc hne q
  calc
    S.card ≤ 2 * (E.biUnion id).card := hhalf
    _ ≤ 2 * (k * E.card) := Nat.mul_le_mul_left 2 h1
    _ ≤ 2 * (k * (M * (run E color q).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left k h2)
    _ ≤ 2 * (k * (M * (removed E color q).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left k (Nat.mul_le_mul_left M h3))
    _ = _ := by ring

/-- Arithmetic contraction, kept separate from graph and finite-set terms. -/
theorem remaining_of_progress {D s a r : ℕ} (hD : 0 < D)
    (hs : a + r = s) (hp : s ≤ D * r) : D * a ≤ (D - 1) * s := by
  have he : D - 1 + 1 = D := by omega
  nlinarith

end Paper.DeterministicPartitionGreedy

#print axioms Paper.DeterministicPartitionGreedy.disjoint
#print axioms Paper.DeterministicPartitionGreedy.dominates
#print axioms Paper.DeterministicPartitionGreedy.half_progress
