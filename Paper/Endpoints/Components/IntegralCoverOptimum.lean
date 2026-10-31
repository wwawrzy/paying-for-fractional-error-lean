import Paper.Solver.LocalSearch.GeneralCoveringIntegral
import Mathlib.Data.Nat.Lattice

/-! The original integral covering benchmark, defined from feasible admissible
sets and their actual natural costs. All constructions here are proof-side;
no global incidence data, optimum, or witness is supplied to a runtime. -/
namespace Paper.IntegralCoverOptimum
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def Feasible (C : V → Finset V) (R D : Finset V) : Prop :=
  D ⊆ CoveringSupport.admissible C R ∧ GeneralCoveringIntegral.Covers C R D

def cost (c : V → ℕ) (D : Finset V) : ℕ := ∑ v ∈ D, c v

def values (C : V → Finset V) (R : Finset V) (c : V → ℕ) : Set ℕ :=
  {n | ∃ D : Finset V, Feasible C R D ∧ cost c D = n}

/-- The benchmark is the infimum of actual feasible costs, not a supplied value. -/
noncomputable def optimum (C : V → Finset V) (R : Finset V) (c : V → ℕ) : ℕ :=
  sInf (values C R c)

theorem admissible_feasible (C : V → Finset V) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) : Feasible C R (CoveringSupport.admissible C R) := by
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro r hr
  obtain ⟨v, hv⟩ := hrows r hr
  exact ⟨v, Finset.mem_biUnion.mpr ⟨r, hr, hv⟩, hv⟩

theorem values_nonempty (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) : (values C R c).Nonempty :=
  ⟨cost c (CoveringSupport.admissible C R),
    CoveringSupport.admissible C R, admissible_feasible C R hrows, rfl⟩

/-- Nat's standard infimum attainment and lower-bound facts provide the minimum. -/
theorem isLeast_optimum (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) : IsLeast (values C R c) (optimum C R c) :=
  ⟨Nat.sInf_mem (values_nonempty C R c hrows), fun _ hn => Nat.sInf_le hn⟩

theorem exists_optimal (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) :
    ∃ D : Finset V, Feasible C R D ∧ cost c D = optimum C R c :=
  (isLeast_optimum C R c hrows).1

/-- Universal comparison needs only the competitor's literal feasibility. -/
theorem optimum_le_cost (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    {D : Finset V} (hD : Feasible C R D) : optimum C R c ≤ cost c D :=
  Nat.sInf_le ⟨D, hD, rfl⟩

noncomputable def minimizer (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) : Finset V :=
  (exists_optimal C R c hrows).choose

theorem minimizer_feasible (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) : Feasible C R (minimizer C R c hrows) :=
  (exists_optimal C R c hrows).choose_spec.1

theorem minimizer_cost (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) : cost c (minimizer C R c hrows) = optimum C R c :=
  (exists_optimal C R c hrows).choose_spec.2

theorem minimizer_le (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) {D : Finset V} (hD : Feasible C R D) :
    cost c (minimizer C R c hrows) ≤ cost c D := by
  rw [minimizer_cost]
  exact optimum_le_cost C R c hD

theorem optimum_le_iff (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (K : ℕ) :
    optimum C R c ≤ K ↔ ∃ D : Finset V, Feasible C R D ∧ cost c D ≤ K := by
  constructor
  · intro h
    obtain ⟨D, hD, he⟩ := exists_optimal C R c hrows
    exact ⟨D, hD, he.le.trans h⟩
  · rintro ⟨D, hD, hcost⟩
    exact (optimum_le_cost C R c hD).trans hcost

/-- Positivity is required only on admissible candidates, not on other vertices. -/
theorem card_le_cost (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v)
    {D : Finset V} (hD : Feasible C R D) : D.card ≤ cost c D := by
  calc
    D.card = ∑ _v ∈ D, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ D, c v := Finset.sum_le_sum (fun v hv => hc v (hD.1 hv))

/-- A small original optimum yields an actual admissible cover with the same
cost and at most `K` vertices. No candidate witness is assumed. -/
theorem small_witness (C : V → Finset V) (R : Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v)
    (K : ℕ) (hK : optimum C R c ≤ K) :
    ∃ D : Finset V, Feasible C R D ∧ cost c D = optimum C R c ∧
      cost c D ≤ K ∧ D.card ≤ K := by
  obtain ⟨D, hD, he⟩ := exists_optimal C R c hrows
  have hdK : cost c D ≤ K := he.le.trans hK
  exact ⟨D, hD, he, hdK, (card_le_cost C R c hc hD).trans hdK⟩

theorem feasible_empty_iff (C : V → Finset V) (D : Finset V) :
    Feasible C ∅ D ↔ D = ∅ := by
  simp [Feasible, CoveringSupport.admissible, GeneralCoveringIntegral.Covers]

theorem optimum_empty (C : V → Finset V) (c : V → ℕ) : optimum C ∅ c = 0 := by
  have hD : Feasible C ∅ (∅ : Finset V) := (feasible_empty_iff C ∅).mpr rfl
  have h := optimum_le_cost C ∅ c hD
  simpa only [cost, Finset.sum_empty, Nat.le_zero] using h

theorem minimizer_empty (C : V → Finset V) (c : V → ℕ)
    (hrows : ∀ r ∈ (∅ : Finset V), (C r).Nonempty) : minimizer C ∅ c hrows = ∅ :=
  (feasible_empty_iff C _).mp (minimizer_feasible C ∅ c hrows)

end Paper.IntegralCoverOptimum

#print axioms Paper.IntegralCoverOptimum.admissible_feasible
#print axioms Paper.IntegralCoverOptimum.isLeast_optimum
#print axioms Paper.IntegralCoverOptimum.exists_optimal
#print axioms Paper.IntegralCoverOptimum.minimizer_le
#print axioms Paper.IntegralCoverOptimum.optimum_le_iff
#print axioms Paper.IntegralCoverOptimum.card_le_cost
#print axioms Paper.IntegralCoverOptimum.small_witness
#print axioms Paper.IntegralCoverOptimum.optimum_empty
#print axioms Paper.IntegralCoverOptimum.minimizer_empty
