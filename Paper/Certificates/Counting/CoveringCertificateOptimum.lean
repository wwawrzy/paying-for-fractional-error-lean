import Paper.Certificates.Counting.CoveringCertificate
import Paper.Certificates.Counting.CoveringSupport

/-! An optimum-level multicover certificate for arbitrary admissible covering
sets. Coordinates and certificate copies outside the union of demanded lists
are removed explicitly. -/
namespace Paper.CoveringCertificateOptimum
attribute [local instance] Classical.propDecidable
open SevenFoundation CoveringOptimum CoveringCertificate CoveringSupport
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def paddedCost (C : V → Finset V) (R : Finset V)
    (c : V → ℝ) (v : V) : ℝ :=
  if v ∈ admissible C R then c v else 1

def keepCopies (C : V → Finset V) (R : Finset V)
    (m : V → ℕ) (v : V) : ℕ :=
  if v ∈ admissible C R then m v else 0

theorem paddedCost_nonneg (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (v : V) : 0 ≤ paddedCost C R c v := by
  by_cases hv : v ∈ admissible C R
  · simpa [paddedCost, hv] using hc v
  · simp [paddedCost, hv]

theorem objective_eq_padded_of_supported (C : V → Finset V) (R : Finset V)
    (c x : V → ℝ) (hsupp : ∀ v ∉ admissible C R, x v = 0) :
    CoveringOptimum.objective (paddedCost C R c) x =
      CoveringOptimum.objective c x := by
  unfold CoveringOptimum.objective
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ admissible C R
  · simp [paddedCost, hv]
  · simp [paddedCost, hv, hsupp v hv]

theorem objective_keep_eq_original (C : V → Finset V) (R : Finset V)
    (c : V → ℝ) (m : V → ℕ) :
    CoveringOptimum.objective c (fun v => (keepCopies C R
      m v : ℝ)) =
      CoveringOptimum.objective (paddedCost C R c)
        (fun v => (keepCopies C R m v : ℝ)) := by
  unfold CoveringOptimum.objective
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ admissible C R
  · simp [paddedCost, keepCopies, hv]
  · simp [paddedCost, keepCopies, hv]

theorem objective_keep_le (C : V → Finset V) (R : Finset V)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) (m : V → ℕ) :
    CoveringOptimum.objective (paddedCost C R c)
        (fun v => (keepCopies C R m v : ℝ)) ≤
      CoveringOptimum.objective (paddedCost C R c)
        (fun v => (m v : ℝ)) := by
  unfold CoveringOptimum.objective
  apply Finset.sum_le_sum
  intro v _
  have hm : (keepCopies C R m v : ℝ) ≤ (m v : ℝ) := by
    by_cases hv : v ∈ admissible C R
    · simp [keepCopies, hv]
    · simp [keepCopies, hv]
  exact mul_le_mul_of_nonneg_left hm (paddedCost_nonneg C R c hc v)

theorem keep_covers (C : V → Finset V) (R : Finset V) (q : ℕ)
    (m : V → ℕ) (hm : ∀ r ∈ R, q ≤ ∑ v ∈ C r, m v) :
    ∀ r ∈ R, q ≤ ∑ v ∈ C r, keepCopies C R m v := by
  intro r hr
  have hsum :
      (∑ v ∈ C r, keepCopies C R m v) = ∑ v ∈ C r, m v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hva : v ∈ admissible C R :=
      Finset.mem_biUnion.mpr ⟨r, hr, hv⟩
    simp [keepCopies, hva]
  rw [hsum]
  exact hm r hr

/-- A q-fold multicover certificate measured against the optimum of the
actual arbitrary-list LP. The returned multiplicities vanish outside all
lists belonging to demands. No symmetry, self-incidence, or neighborhood-list
assumption beyond `C(r) ⊆ N_G[r]` is required. -/
theorem exists_optimum_certificate (C : V → Finset V)
    (hclosed : ∀ r, C r ⊆ closed G r) (R : Finset V)
    (hrows : ∀ r ∈ R, (C r).Nonempty) {a : ℕ}
    (O : HallOrientation.Orientation G a) (ha : 1 ≤ a) (q : ℕ)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    ∃ m : V → ℕ,
      (∀ r ∈ R, q ≤ ∑ v ∈ C r, m v) ∧
      (∀ v ∉ admissible C R, m v = 0) ∧
      (∑ v, c v * (m v : ℝ)) ≤
        (q + 2 * (a : ℝ)) * CoveringOptimum.number C R c := by
  obtain ⟨x, hx, _, hxsupp, hxopt⟩ :=
    CoveringSupport.exists_supported_optimum C R c hrows hc
  have hobjx : CoveringOptimum.objective (paddedCost C R c) x =
      CoveringOptimum.number C R c := by
    calc
      _ = CoveringOptimum.objective c x :=
        objective_eq_padded_of_supported C R c x hxsupp
      _ = CoveringOptimum.number C R c := hxopt
  obtain ⟨m, hmcovers, hmcost⟩ :=
    CoveringCertificate.exists_certificate G C hclosed R O ha q
      (paddedCost C R c) x hx.1 hx.2
  let m' := keepCopies C R m
  have hmcost' : CoveringOptimum.objective (paddedCost C R c) (fun v => (m v : ℝ)) ≤
      (q + 2 * (a : ℝ)) * CoveringOptimum.objective (paddedCost C R c) x := by
    simpa only [CoveringOptimum.objective] using hmcost
  refine ⟨m', keep_covers C R q m hmcovers, ?_, ?_⟩
  · intro v hv
    simp [m', keepCopies, hv]
  · calc
      (∑ v, c v * (m' v : ℝ)) =
          CoveringOptimum.objective (paddedCost C R c)
            (fun v => (m' v : ℝ)) :=
        by simpa only [m'] using objective_keep_eq_original C R c m
      _ ≤ CoveringOptimum.objective (paddedCost C R c) (fun v => (m v : ℝ)) :=
        objective_keep_le C R c hc m
      _ ≤ (q + 2 * (a : ℝ)) *
          CoveringOptimum.objective (paddedCost C R c) x := hmcost'
      _ = (q + 2 * (a : ℝ)) * CoveringOptimum.number C R c := by
        rw [hobjx]

end Paper.CoveringCertificateOptimum
