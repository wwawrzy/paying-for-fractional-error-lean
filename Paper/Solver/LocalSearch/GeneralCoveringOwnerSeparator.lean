import Paper.Solver.LocalSearch.GeneralCoveringOwnerPhysical
import Paper.Partitions.Separators.GuardedSeparator
import Paper.Preliminaries.MinorInheritance
import Paper.Partitions.Separators.SeparatorProfile

/-! Separator profiles for actual original-C optional/gated owners, derived
from their physical guarded routes and physical minor density. Constants
depend only on public a,h,L. This is analysis, not an executable routing or
partition endpoint, and no owner-density or separator oracle is assumed. -/
namespace Paper.GeneralCoveringOwnerSeparator

noncomputable def physicalFactor (a : ℝ) (L : ℕ) : ℝ := 1 + 6 * a * ((L + 1 : ℕ) : ℝ) ^ 4

noncomputable def constant (a : ℝ) (h L : ℕ) : ℝ :=
  2 * (h : ℝ) ^ 2 * L * Real.sqrt (physicalFactor a L)

theorem physicalFactor_nonneg (a : ℝ) (ha : 0 ≤ a) (L : ℕ) : 0 ≤ physicalFactor a L := by
  unfold physicalFactor
  positivity

theorem physicalFactor_pos (a : ℝ) (ha : 0 ≤ a) (L : ℕ) : 0 < physicalFactor a L := by
  unfold physicalFactor
  positivity

theorem constant_nonneg (a : ℝ) (h L : ℕ) : 0 ≤ constant a h L := by
  unfold constant
  positivity

theorem constant_pos (a : ℝ) (ha : 0 ≤ a) (h L : ℕ) (hh : 1 ≤ h) (hL : 1 ≤ L) :
    0 < constant a h L := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hL' : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hs := Real.sqrt_pos.mpr (physicalFactor_pos a ha L)
  unfold constant
  positivity

open SevenFoundation DeletionComponents GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type} [Fintype A] [DecidableEq A]

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringTaskGeometry.graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem physical_size (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (K : SimpleGraph A) [DecidableRel K.Adj] (e : A → V) (hinj : Function.Injective e)
    (heD : ∀ x, e x ∈ D)
    (hedge : ∀ x y, K.Adj x y → (ownerGraph G C D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    (Fintype.card ↥(GeneralCoveringOwnerPhysical.vertices G C D R L K e heD hedge : Set V) : ℝ) ≤
      physicalFactor a L * Fintype.card A := by
  have hs := GeneralCoveringOwnerPhysical.density_size G C D R L K e hinj heD hedge hlocal hL hden ha
  simpa only [physicalFactor, Finset.coe_sort_coe, Fintype.card_coe] using hs

theorem represented (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (K : SimpleGraph A) [DecidableRel K.Adj] (e : A → V) (hinj : Function.Injective e)
    (heD : ∀ x, e x ∈ D)
    (hedge : ∀ x y, K.Adj x y → (ownerGraph G C D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h : ℕ) (hh : 2 * a + 1 < (h : ℝ)) :
    ∃ X : Finset A, (X.card : ℝ) ≤ constant a h L * Real.sqrt (Fintype.card A) ∧
      ∀ U : (deleted K X).ConnectedComponent,
        ((physical K X U).card : ℝ) ≤ (Fintype.card A : ℝ) / 2 := by
  let W := GeneralCoveringOwnerPhysical.vertices G C D R L K e heD hedge
  let S := GeneralCoveringOwnerPhysical.restricted G C D R L K e hinj heD hedge hlocal
  have hlabels : ∀ v, (S.labels v).card ≤ L :=
    GeneralCoveringOwnerPhysical.restricted_labels G C D R L K e hinj heD hedge hlocal hL
  have hsize : (Fintype.card ↥(W : Set V) : ℝ) ≤ physicalFactor a L * Fintype.card A :=
    physical_size G C D R L hL K e hinj heD hedge hlocal hden ha
  exact GuardedSeparator.proportional S L hlabels (MinorInheritance.induced G hden W) ha h hh
    (physicalFactor a L) (physicalFactor_nonneg a ha L) hsize

theorem represented_profile (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (K : SimpleGraph A) [DecidableRel K.Adj] (e : A → V) (hinj : Function.Injective e)
    (heD : ∀ x, e x ∈ D)
    (hedge : ∀ x y, K.Adj x y → (ownerGraph G C D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h : ℕ) (hh : 2 * a + 1 < (h : ℝ)) : SeparatorProfile.Bound K (constant a h L) := by
  intro I
  let J := K.induce (I : Set A)
  let e' : ↥(I : Set A) → V := fun x => e x.val
  have hinj' : Function.Injective e' := fun _ _ he => Subtype.ext (hinj he)
  have heD' : ∀ x, e' x ∈ D := fun x => heD x.val
  have hedge' : ∀ x y, J.Adj x y → (ownerGraph G C D R L).Adj ⟨e' x, heD' x⟩ ⟨e' y, heD' y⟩ :=
    fun x y hxy => hedge x.val y.val hxy
  have hs := represented G C D R L hL J e' hinj' heD' hedge' hlocal hden ha h hh
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hs

theorem owner_profile (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h : ℕ) (hh : 2 * a + 1 < (h : ℝ)) :
    SeparatorProfile.Bound (ownerGraph G C D R L) (constant a h L) := by
  let e : D → V := fun x => x.val
  have hinj : Function.Injective e := fun _ _ he => Subtype.ext he
  have heD : ∀ x, e x ∈ D := fun x => x.property
  exact represented_profile G C D R L hL (ownerGraph G C D R L) e hinj heD
    (fun _ _ hxy => hxy) hlocal hden ha h hh

theorem low_profile (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (Q : Finset D)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h : ℕ) (hh : 2 * a + 1 < (h : ℝ)) :
    SeparatorProfile.Bound (GeneralCoveringTaskGeometry.graph G C D R L Q) (constant a h L) := by
  let K := GeneralCoveringTaskGeometry.graph G C D R L Q
  let e : Low D Q → V := fun x => x.val.val
  have hinj : Function.Injective e := fun _ _ he => Subtype.ext (Subtype.ext he)
  have heD : ∀ x, e x ∈ D := fun x => x.val.property
  exact represented_profile G C D R L hL K e hinj heD (fun _ _ hxy => hxy) hlocal hden ha h hh

end Paper.GeneralCoveringOwnerSeparator

#print axioms Paper.GeneralCoveringOwnerSeparator.physicalFactor_nonneg
#print axioms Paper.GeneralCoveringOwnerSeparator.physicalFactor_pos
#print axioms Paper.GeneralCoveringOwnerSeparator.constant_nonneg
#print axioms Paper.GeneralCoveringOwnerSeparator.constant_pos
#print axioms Paper.GeneralCoveringOwnerSeparator.physical_size
#print axioms Paper.GeneralCoveringOwnerSeparator.represented
#print axioms Paper.GeneralCoveringOwnerSeparator.represented_profile
#print axioms Paper.GeneralCoveringOwnerSeparator.owner_profile
#print axioms Paper.GeneralCoveringOwnerSeparator.low_profile
