import Paper.Optimality.LowerBounds.CycleBadPacking
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Realizing a global bad-word packing by one complete labeling

Every word is preserved in its original order. The remaining identifiers
fill the final positions. The resulting labeling is an equivalence, hence
uses every identifier exactly once. This justifies changing the labeling
when applying global maximality in the cycle lower-bound argument.
-/
noncomputable section
namespace Paper.CycleBadPackingPlacement

open Paper.CycleBadPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

abbrev Rest (P : Finset (Fin r → V)) := {v : V // v ∉ covered P}
abbrev Occurrences (P : Finset (Fin r → V)) := (P × Fin r) ⊕ Rest P

def label (P : Finset (Fin r → V)) : Occurrences P → V
  | .inl (w, i) => w.val i
  | .inr v => v.val

theorem label_injective {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) : Function.Injective (label P) := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      rcases x with ⟨w, i⟩
      rcases y with ⟨z, j⟩
      change w.val i = z.val j at hxy
      by_cases hwz : w = z
      · subst z
        have hij := (hP.1 w.val w.property).1 hxy
        subst j
        rfl
      · have hne : w.val ≠ z.val := fun h => hwz (Subtype.ext h)
        have hd := hP.2 w.property z.property hne
        have hi : w.val i ∈ support w.val := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        have hj : z.val j ∈ support z.val := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        exact False.elim (Finset.disjoint_left.mp hd hi (hxy.symm ▸ hj))
    | inr v =>
      rcases x with ⟨w, i⟩
      change w.val i = v.val at hxy
      have hi : w.val i ∈ covered P := Finset.mem_biUnion.mpr
        ⟨w.val, w.property, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      exact False.elim (v.property (hxy ▸ hi))
  | inr v =>
    cases y with
    | inl y =>
      rcases y with ⟨w, i⟩
      change v.val = w.val i at hxy
      have hi : w.val i ∈ covered P := Finset.mem_biUnion.mpr
        ⟨w.val, w.property, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      exact False.elim (v.property (hxy.symm ▸ hi))
    | inr u =>
      change v.val = u.val at hxy
      exact congrArg Sum.inr (Subtype.ext hxy)

theorem label_surjective (P : Finset (Fin r → V)) : Function.Surjective (label P) := by
  intro v
  by_cases hv : v ∈ covered P
  · obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i, _, hwi⟩ := Finset.mem_image.mp hvw
    exact ⟨.inl (⟨w, hw⟩, i), hwi⟩
  · exact ⟨.inr ⟨v, hv⟩, rfl⟩

def labelEquiv {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) : Occurrences P ≃ V :=
  Equiv.ofBijective (label P) ⟨label_injective hP, label_surjective P⟩

theorem count {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) : P.card * r + Fintype.card (Rest P) = Fintype.card V := by
  have hh := Fintype.card_congr (labelEquiv hP)
  simpa only [Occurrences, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fin] using hh

def position {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) : Occurrences P ≃ Fin (Fintype.card V) :=
  (((Equiv.sumCongr
    ((Equiv.prodCongr (Fintype.equivFin P) (Equiv.refl (Fin r))).trans finProdFinEquiv)
    (Fintype.equivFin (Rest P))).trans finSumFinEquiv).trans
      (Fin.castOrderIso (by simpa only [Fintype.card_coe] using count hP)).toEquiv)

def arrangement {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) : Fin (Fintype.card V) ≃ V :=
  (position hP).symm.trans (labelEquiv hP)

/-- Each packed word occupies one consecutive block of length r. -/
theorem position_block {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) (w : P) (i : Fin r) :
    ((position hP) (.inl (w, i))).val = (Fintype.equivFin P w).val * r + i.val := by
  simp [position, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- The permutation preserves the word's order, rather than sorting its IDs. -/
theorem arrangement_block {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) (w : P) (i : Fin r) :
    arrangement hP ((position hP) (.inl (w, i))) = w.val i := by
  change label P ((position hP).symm ((position hP) (.inl (w, i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem arrangement_injective {bad : (Fin r → V) → Prop} {P : Finset (Fin r → V)}
    (hP : Packing bad P) : Function.Injective (arrangement hP) := (arrangement hP).injective

theorem arrangement_uses_every_identifier {bad : (Fin r → V) → Prop}
    {P : Finset (Fin r → V)} (hP : Packing bad P) :
    Finset.univ.image (arrangement hP) = (Finset.univ : Finset V) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact (arrangement hP).surjective v

end Paper.CycleBadPackingPlacement

#print axioms Paper.CycleBadPackingPlacement.label_injective
#print axioms Paper.CycleBadPackingPlacement.label_surjective
#print axioms Paper.CycleBadPackingPlacement.count
#print axioms Paper.CycleBadPackingPlacement.position_block
#print axioms Paper.CycleBadPackingPlacement.arrangement_block
#print axioms Paper.CycleBadPackingPlacement.arrangement_uses_every_identifier
