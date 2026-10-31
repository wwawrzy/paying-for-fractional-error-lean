import Paper.Preliminaries.FiniteConnectivity
import Paper.Preliminaries.EligibleSets

/-! Fully decidable finite eligibility using integer comparisons only.
The parameter t represents epsilon=1/t; no real comparison in the algorithm. -/
namespace Paper.FiniteEligibility
variable {V : Type} [LinearOrder V]

def boundary (N : V → Finset V) (S U : Finset V) : ℕ :=
  ∑ u ∈ U, (N u ∩ (S \ U)).card

def family (N : V → Finset V) (S : Finset V) (k t : ℕ) : Finset (Finset V) :=
  S.powerset.filter (fun U => FiniteConnectivity.connected N U = true ∧ U.card ≤ k ∧
    t * boundary N S U ≤ 4 * U.card)

theorem mem_family (N : V → Finset V) (S U : Finset V) (k t : ℕ) :
    U ∈ family N S k t ↔ U ⊆ S ∧ FiniteConnectivity.connected N U = true ∧ U.card ≤ k ∧
      t * boundary N S U ≤ 4 * U.card := by
  simp only [family, Finset.mem_filter, Finset.mem_powerset, and_assoc]

theorem arithmetic_iff (t b u : ℕ) (ht : 0 < t) :
    t * b ≤ 4 * u ↔ (b : ℝ) ≤ 4 * (1 / (t : ℝ)) * u := by
  have hp : (0 : ℝ) < t := by exact_mod_cast ht
  have he : 4 * (1 / (t : ℝ)) * u = (4 * u : ℝ) / t := by ring
  rw [he, le_div_iff₀ hp, mul_comm (b : ℝ) (t : ℝ)]
  exact_mod_cast (Iff.rfl : t * b ≤ 4 * u ↔ t * b ≤ 4 * u)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem boundary_eq (S U : Finset V) :
    boundary (fun u => G.neighborFinset u) S U = PartBoundaries.boundary G S U := by
  unfold PartBoundaries.boundary
  rfl

theorem correct (S : Finset V) (k t : ℕ) (ht : 0 < t) :
    family (fun u => G.neighborFinset u) S k t = EligibleSets.family G S k (1 / (t : ℝ)) := by
  ext U
  rw [mem_family, EligibleSets.mem_family, FiniteConnectivity.correct G U,
    boundary_eq G S U, arithmetic_iff t _ _ ht]
end Paper.FiniteEligibility
