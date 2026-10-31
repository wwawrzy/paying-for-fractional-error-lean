import Paper.Optimality.LowerBounds.CycleBadPackingPlacement
import Paper.Optimality.LowerBounds.CycleForcedSegments

/-!
# The global bad-word reservoir from actual cycle approximation guarantees

The output function may depend on the complete labeling. No locality or
coloring lower bound is assumed here. The conclusion is the bad-free large
identifier set used by the later smaller-cycle simulation, not a round bound.
-/
noncomputable section
namespace Paper.CycleBadReservoir

open SimpleGraph SevenFoundation CycleBadPacking CycleBadPackingPlacement CycleForcedSegments

abbrev Labeling (N : ℕ) := Fin N ≃ Fin N

def Bad {N : ℕ} (D : Labeling N → Finset (Fin N)) (T : ℕ) (w : Fin (4 * T) → Fin N) : Prop :=
  ∀ (labels : Labeling N) (a : ℕ) (hfit : a + 4 * T ≤ N),
    (∀ i : Fin (4 * T), labels ⟨a + i.val, by omega⟩ = w i) →
    ∀ j : Fin (2 * T), (⟨a + T + j.val, by omega⟩ : Fin N) ∈ D labels

def naturalPosition {N T : ℕ} {D : Labeling N → Finset (Fin N)}
    {P : Finset (Fin (4 * T) → Fin N)} (hP : Packing (Bad D T) P) :
    Occurrences P ≃ Fin N :=
  (position hP).trans (Fin.castOrderIso (Fintype.card_fin N)).toEquiv

def naturalArrangement {N T : ℕ} {D : Labeling N → Finset (Fin N)}
    {P : Finset (Fin (4 * T) → Fin N)} (hP : Packing (Bad D T) P) : Labeling N :=
  (naturalPosition hP).symm.trans (labelEquiv hP)

theorem naturalPosition_block {N T : ℕ} {D : Labeling N → Finset (Fin N)}
    {P : Finset (Fin (4 * T) → Fin N)} (hP : Packing (Bad D T) P) (w : P) (i : Fin (4 * T)) :
    (naturalPosition hP (.inl (w, i))).val = (Fintype.equivFin P w).val * (4 * T) + i.val := by
  change ((position hP) (.inl (w, i))).val = _
  exact position_block hP w i

theorem naturalArrangement_block {N T : ℕ} {D : Labeling N → Finset (Fin N)}
    {P : Finset (Fin (4 * T) → Fin N)} (hP : Packing (Bad D T) P) (w : P) (i : Fin (4 * T)) :
    naturalArrangement hP (naturalPosition hP (.inl (w, i))) = w.val i := by
  change label P ((naturalPosition hP).symm (naturalPosition hP (.inl (w, i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem packing_fits {N T : ℕ} {D : Labeling N → Finset (Fin N)}
    {P : Finset (Fin (4 * T) → Fin N)} (hP : Packing (Bad D T) P) :
    4 * T * Fintype.card P ≤ N := by
  have hc := Finset.card_le_univ (CycleBadPacking.covered P)
  rw [covered_card hP, Fintype.card_fin] at hc
  simpa only [Fintype.card_coe] using hc

/-- The middle intervals are selected in the single complete permutation
that realizes every word of this arbitrary global packing. -/
theorem middle_selected {N T : ℕ} {D : Labeling N → Finset (Fin N)}
    {P : Finset (Fin (4 * T) → Fin N)} (hP : Packing (Bad D T) P) :
    (Finset.univ : Finset (Fin (Fintype.card P))).biUnion
      (middle N T (Fintype.card P) (packing_fits hP)) ⊆ D (naturalArrangement hP) := by
  intro v hv
  obtain ⟨b, _, hvb⟩ := Finset.mem_biUnion.mp hv
  let w : P := (Fintype.equivFin P).symm b
  let a := 4 * T * b.val
  have hb := b.isLt
  have hm := Nat.mul_le_mul_left (4 * T) (show b.val + 1 ≤ Fintype.card P by omega)
  have hfit : a + 4 * T ≤ N := by
    have hf := packing_fits hP
    dsimp only [a]
    nlinarith only [hm, hf]
  have hwords (i : Fin (4 * T)) : naturalArrangement hP ⟨a + i.val, by omega⟩ = w.val i := by
    have he : naturalPosition hP (.inl (w, i)) = ⟨a + i.val, by omega⟩ := by
      apply Fin.ext
      rw [naturalPosition_block]
      simp only [w, Equiv.apply_symm_apply]
      dsimp only [a]
      ac_rfl
    rw [← he]
    exact naturalArrangement_block hP w i
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hvb
  have hbad := (hP.1 w.val w.property).2
  have hsel := hbad (naturalArrangement hP) a hfit hwords j
  have he : (⟨a + T + j.val, by omega⟩ : Fin N) = v := hj
  exact he ▸ hsel

/-- Half-cycle bad packings contradict the approximation guarantee. This
bound is proved for every global packing, not supplied as a conclusion. -/
theorem packing_less_than_half (n T : ℕ) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε)
    (hquarter : ε < 1 / 4) (hlarge : 8 * (1 + ε) / (1 - 4 * ε) < (n + 3 : ℕ))
    (D : Labeling (n + 3) → Finset (Fin (n + 3)))
    (hdom : ∀ labels, dominates (cycleGraph (n + 3)) (D labels))
    (happrox : ∀ labels, ((D labels).card : ℝ) ≤ (1 + ε) * (cycleGraph (n + 3)).dominationNumber)
    (P : Finset (Fin (4 * T) → Fin (n + 3))) (hP : Packing (Bad D T) P) :
    2 * ((4 * T) * P.card) < n + 3 := by
  by_contra hn
  let F := (Finset.univ : Finset (Fin (Fintype.card P))).biUnion
    (middle (n + 3) T (Fintype.card P) (packing_fits hP))
  have hhalf : n + 3 ≤ 8 * T * Fintype.card P := by
    rw [Fintype.card_coe]
    have hh := Nat.le_of_not_gt hn
    nlinarith only [hh]
  have hf : F.card = 2 * T * Fintype.card P := middle_union_card _ _ _ _
  have hb : (SevenFoundation.covered (cycleGraph (n + 3)) F \ F).card ≤ 2 * Fintype.card P :=
    middle_union_boundary n T (Fintype.card P) hT (packing_fits hP)
  have hbad := CycleForcedDomination.packed_not_approximate n T (Fintype.card P) hT
    (D (naturalArrangement hP)) F (hdom _) (middle_selected hP) hf hb hhalf ε hε hquarter hlarge
  exact (not_le_of_gt hbad) (happrox _)

/-- The large bad-free reservoir follows from actual guarantees on every
complete labeling, without an assumed packing or avoidance estimate. -/
theorem exists_reservoir (n T : ℕ) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε)
    (hquarter : ε < 1 / 4) (hlarge : 8 * (1 + ε) / (1 - 4 * ε) < (n + 3 : ℕ))
    (D : Labeling (n + 3) → Finset (Fin (n + 3)))
    (hdom : ∀ labels, dominates (cycleGraph (n + 3)) (D labels))
    (happrox : ∀ labels, ((D labels).card : ℝ) ≤ (1 + ε) * (cycleGraph (n + 3)).dominationNumber) :
    ∃ S : Finset (Fin (n + 3)), (n + 3) / 2 < S.card ∧
      ∀ w : Fin (4 * T) → Fin (n + 3), Function.Injective w → (∀ i, w i ∈ S) → ¬ Bad D T w := by
  have hr : 0 < 4 * T := by omega
  have hbound : ∀ P : Finset (Fin (4 * T) → Fin (n + 3)),
      Packing (Bad D T) P → 2 * (4 * T * P.card) < Fintype.card (Fin (n + 3)) := by
    simpa only [Fintype.card_fin] using
      packing_less_than_half n T hT ε hε hquarter hlarge D hdom happrox
  simpa only [Fintype.card_fin] using exists_large_bad_free (Bad D T) hr
    hbound

end Paper.CycleBadReservoir

#print axioms Paper.CycleBadReservoir.naturalArrangement_block
#print axioms Paper.CycleBadReservoir.packing_fits
#print axioms Paper.CycleBadReservoir.middle_selected
#print axioms Paper.CycleBadReservoir.packing_less_than_half
#print axioms Paper.CycleBadReservoir.exists_reservoir
