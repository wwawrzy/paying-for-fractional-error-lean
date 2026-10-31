import Paper.Certificates.Counting.HallWithOverflow

/-! q-fold orientations whose per-vertex overload is charged to a single
shared overflow budget. This supplies the analytic threshold count without
assuming an orientation or invoking an unproved flow theorem. -/
namespace Paper.ApproximateOrientation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure MultiOrientation (q : Nat) where
  tail : G.edgeFinset × Fin q → V
  incident : ∀ e, tail e ∈ e.1.val

noncomputable def load {q : Nat} (O : MultiOrientation G q) (v : V) : Nat := by
  classical
  exact (Finset.univ.filter (fun e => O.tail e = v)).card

theorem exists_orientation (p s q : Nat)
    (hden : ∀ U : Finset V, q * G.inducedEdgeCount U ≤ p*U.card+s) :
    ∃ O : MultiOrientation G q, ∃ err : V → Nat,
      (∀ v, load G O v ≤ p + err v) ∧ (∑ v, err v) ≤ s := by
  classical
  obtain ⟨f,hfinj,hfmem⟩ := HallWithOverflow.exists_assignment G p s q hden
  let tail : G.edgeFinset × Fin q → V := fun e => match f e with
    | Sum.inl vi => vi.1
    | Sum.inr _ => e.1.val.out.1
  have hinc : ∀ e, tail e ∈ e.1.val := by
    intro e
    cases hfe : f e with
    | inl vi =>
      have hh := hfmem e
      rw [hfe] at hh
      have hi := (HallWithOverflow.inl_allowed G p s q e vi.1 vi.2).mp hh
      simpa only [tail,hfe] using (Sym2.mem_toFinset.mp hi)
    | inr i => simpa only [tail,hfe] using e.1.val.out_fst_mem
  let O : MultiOrientation G q := ⟨tail,hinc⟩
  let bad : Finset (G.edgeFinset × Fin q) := Finset.univ.filter (fun e => ∃ i, f e = Sum.inr i)
  let err : V → Nat := fun v => (bad.filter (fun e => tail e = v)).card
  have hb : bad.card ≤ s := by
    have hh : bad.card ≤ ((Finset.univ : Finset (Fin s)).image
        (Sum.inr : Fin s → (V × Fin p) ⊕ Fin s)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro e he
        obtain ⟨i,hi⟩ := (Finset.mem_filter.mp he).2
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
      · exact fun _ _ _ _ h => hfinj h
    simpa [Finset.card_image_of_injective _ Sum.inr_injective] using hh
  refine ⟨O,err,?_,?_⟩
  · intro v
    let localSlots : Finset (G.edgeFinset × Fin q) :=
      Finset.univ.filter (fun e => ∃ i, f e = Sum.inl (v,i))
    have hl : localSlots.card ≤ p := by
      have hh : localSlots.card ≤ ((Finset.univ : Finset (Fin p)).image
          (fun i => (Sum.inl (v,i) : (V × Fin p) ⊕ Fin s))).card := by
        apply Finset.card_le_card_of_injOn f
        · intro e he
          obtain ⟨i,hi⟩ := (Finset.mem_filter.mp he).2
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
        · exact fun _ _ _ _ h => hfinj h
      have hinj : Function.Injective (fun i : Fin p => (Sum.inl (v,i) : (V × Fin p) ⊕ Fin s)) := by
        intro i j h
        exact (Prod.mk.inj (Sum.inl.inj h)).2
      simpa [Finset.card_image_of_injective _ hinj] using hh
    have hs : Finset.univ.filter (fun e => tail e = v) ⊆ localSlots ∪ bad.filter (fun e => tail e = v) := by
      intro e he
      have ht := (Finset.mem_filter.mp he).2
      cases hfe : f e with
      | inl vi =>
        have hv : vi.1 = v := by simpa only [tail,hfe] using ht
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,vi.2,?_⟩
        exact hfe.trans (congrArg Sum.inl (Prod.ext hv rfl))
      | inr i =>
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hfe⟩,ht⟩
    have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    change (Finset.univ.filter (fun e => tail e = v)).card ≤ p + err v
    exact hh.trans (Nat.add_le_add_right hl _)
  · have hh := Finset.card_eq_sum_card_fiberwise (s := bad) (t := (Finset.univ : Finset V))
      (f := tail) (fun _ _ => Finset.mem_univ _)
    have hsum : (∑ v, err v) ≤ bad.card := by
      simpa only [err] using hh.symm.le
    exact hsum.trans hb

theorem exists_scaled (a η : Real) (q : Nat)
    (hden : ∀ U : Finset V, (G.inducedEdgeCount U:Real) ≤ a*U.card+η) :
    ∃ O : MultiOrientation G q, ∃ err : V → Nat,
      (∀ v, load G O v ≤ ⌈a*q⌉₊ + err v) ∧ (∑ v, err v) ≤ ⌈η*q⌉₊ :=
  exists_orientation G _ _ q (HallWithOverflow.scaled_density G a η q hden)

end Paper.ApproximateOrientation
#print axioms Paper.ApproximateOrientation.exists_orientation
#print axioms Paper.ApproximateOrientation.exists_scaled
