import Paper.Owners.Construction.SharpOwnerExperiment

namespace Paper.SharpOwnerSurvival
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyRepair OwnerExperiment
open FiniteMeanIncidence SharpOwnerExperiment
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem three_bits (i j o : V) (hij : i ≠ j) (hio : i ≠ o) (hjo : j ≠ o) :
    8*(Finset.univ.filter (fun β : Bits (V := V) => β i = 0 ∧ β j = 0 ∧ β o = 1)).card =
      Fintype.card (Bits (V := V)) := by
  let F : Finset V := {i,j,o}
  let target : V → Fin 2 := fun v => if v = i ∨ v = j then 0 else 1
  have he : FiniteCylinder.cylinder F target =
      Finset.univ.filter (fun β : Bits (V := V) => β i = 0 ∧ β j = 0 ∧ β o = 1) := by
    ext β
    simp [FiniteCylinder.cylinder, F, target, hij, hio, hjo, Ne.symm hio, Ne.symm hjo]
  have hh := FiniteCoordinateCount.exact_count F target
  rw [he] at hh
  simpa [F, hij, hio, hjo] using hh

theorem two_choices (L : ℕ) (v : V) (p q : Fin L) (hpq : p ≠ q) :
    L*(Finset.univ.filter (fun χ : Choices (V := V) L => χ v = p ∨ χ v = q)).card =
      2*Fintype.card (Choices (V := V) L) := by
  classical
  let P := Finset.univ.filter (fun χ : Choices (V := V) L => χ v = p)
  let Q := Finset.univ.filter (fun χ : Choices (V := V) L => χ v = q)
  have he : Finset.univ.filter (fun χ : Choices (V := V) L => χ v = p ∨ χ v = q) = P ∪ Q := by
    ext χ
    simp [P, Q]
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro χ hP hQ
    exact hpq ((Finset.mem_filter.mp hP).2.symm.trans (Finset.mem_filter.mp hQ).2)
  rw [he, Finset.card_union_of_disjoint hd, mul_add]
  rw [FiniteCoordinateCount.one, FiniteCoordinateCount.one]
  dsimp only [Choices]
  omega

/-- Every real owner edge survives on at least a 1/(4L) fraction of outcomes. -/
theorem count (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {i j : D} (hiI : i.val ∈ I) (hjI : j.val ∈ I)
    (hab : (OwnerInteraction.augmentedGraph G D R L).Adj i j) :
    Fintype.card (Outcomes (V := V) L) ≤ 4*L*
      (Finset.univ.filter (fun ω : Outcomes (V := V) L =>
        OwnerEdgeCylinder.Survives G D R L (lift I L hL ω) i.val j.val)).card := by
  classical
  letI : DecidableLE V := fun x y => Classical.propDecidable (x ≤ y)
  obtain ⟨hne, v, hi, hj⟩ := hab
  have hne' : i.val ≠ j.val := fun he => hne (Subtype.ext he)
  have hv : v ∉ heavy G D R L := by
    intro hv
    simp [OwnerInteraction.lightSupport, hv] at hi
  have hiW : i.val ∈ support G D R v := by simpa [OwnerInteraction.lightSupport, hv] using hi
  have hjW : j.val ∈ support G D R v := by simpa [OwnerInteraction.lightSupport, hv] using hj
  let E := Finset.univ.filter (fun ω : Outcomes (V := V) L =>
    OwnerEdgeCylinder.Survives G D R L (lift I L hL ω) i.val j.val)
  by_cases hown : owner G D v = i.val ∨ owner G D v = j.val
  · let B := Finset.univ.filter (fun β : Bits (V := V) => β i.val = 0 ∧ β j.val = 0)
    let C : Finset (Choices (V := V) L) := Finset.univ
    have hsub : B ×ˢ C ⊆ E := by
      intro ω hω
      have hb := (Finset.mem_filter.mp (Finset.mem_product.mp hω).1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        endpoint_owner_survives G D R I L hL ω hne' i.property j.property hiI hjI hiW hjW hown hb.1 hb.2⟩
    have hb : 4*B.card = Fintype.card (Bits (V := V)) := by
      simpa only [B, pow_succ, pow_zero, Nat.reduceMul] using
        (FiniteCoordinateCount.two i.val j.val hne' (0 : Fin 2) (0 : Fin 2))
    have hbudget : Fintype.card (Outcomes (V := V) L) ≤ 4*L*(B ×ˢ C).card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, ← hb]
      calc
        (4*B.card)*Fintype.card (Choices (V := V) L) ≤
            L*((4*B.card)*Fintype.card (Choices (V := V) L)) := Nat.le_mul_of_pos_left _ hL
        _ = _ := by ring
    exact hbudget.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))
  · have hoi : owner G D v ≠ i.val := fun he => hown (Or.inl he)
    have hoj : owner G D v ≠ j.val := fun he => hown (Or.inr he)
    have hsize : (support G D R v).card ≤ L := by
      by_contra hn
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
    obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp ((Finset.mem_sort (· ≤ ·)).mpr hiW)
    obtain ⟨qi, hqi⟩ := List.mem_iff_getElem?.mp ((Finset.mem_sort (· ≤ ·)).mpr hjW)
    have hpL : pi < L := by
      have hh := (List.getElem?_eq_some_iff.mp hpi).choose
      have hh' : pi < (support G D R v).card := by simpa only [Finset.length_sort] using hh
      omega
    have hqL : qi < L := by
      have hh := (List.getElem?_eq_some_iff.mp hqi).choose
      have hh' : qi < (support G D R v).card := by simpa only [Finset.length_sort] using hh
      omega
    let p : Fin L := ⟨pi, hpL⟩
    let q : Fin L := ⟨qi, hqL⟩
    have hpq : p ≠ q := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [p, q] at hv
      have hh : some i.val = some j.val := hpi.symm.trans (hv ▸ hqi)
      exact hne' (Option.some.inj hh)
    let B := Finset.univ.filter (fun β : Bits (V := V) =>
      β i.val = 0 ∧ β j.val = 0 ∧ β (owner G D v) = 1)
    let C := Finset.univ.filter (fun χ : Choices (V := V) L => χ v = p ∨ χ v = q)
    have hsub : B ×ˢ C ⊆ E := by
      intro ω hω
      have hb := (Finset.mem_filter.mp (Finset.mem_product.mp hω).1).2
      have hc := (Finset.mem_filter.mp (Finset.mem_product.mp hω).2).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, choice_survives G D R I L hL ω hne' i.property j.property hiI hjI hiW hjW hv hb.1 hb.2.1 hb.2.2 ?_⟩
      rcases hc with he | he
      · left
        simpa only [pick, lift, he, p] using hpi
      · right
        simpa only [pick, lift, he, q] using hqi
    have hb : 8*B.card = Fintype.card (Bits (V := V)) :=
      three_bits i.val j.val (owner G D v) hne' (Ne.symm hoi) (Ne.symm hoj)
    have hc : L*C.card = 2*Fintype.card (Choices (V := V) L) := two_choices L v p q hpq
    have he : 4*L*(B ×ˢ C).card = Fintype.card (Outcomes (V := V) L) := by
      rw [Finset.card_product]
      calc
        4*L*(B.card*C.card) = 4*B.card*(L*C.card) := by ring
        _ = 4*B.card*(2*Fintype.card (Choices (V := V) L)) := by rw [hc]
        _ = (8*B.card)*Fintype.card (Choices (V := V) L) := by ring
        _ = _ := by rw [hb, Fintype.card_prod]
    exact he.symm.le.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

end Paper.SharpOwnerSurvival
