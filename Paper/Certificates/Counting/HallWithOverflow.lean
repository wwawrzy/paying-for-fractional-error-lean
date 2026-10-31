import Paper.Certificates.Counting.HallOrientation

/-! Capacitated Hall with q copies per graph edge and a shared overflow pool.
This is a finite certificate for approximate fractional orientations in
fv:imp:additive; no max-flow axiom is used. -/
namespace Paper.HallWithOverflow
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def allowed (p s q : Nat) (e : G.edgeFinset × Fin q) :
    Finset ((V × Fin p) ⊕ Fin s) := by
  classical
  exact ((e.1.val.toFinset ×ˢ Finset.univ).image Sum.inl) ∪
    (Finset.univ.image Sum.inr)

theorem inl_allowed (p s q : Nat) (e : G.edgeFinset × Fin q) (v : V) (i : Fin p) :
    Sum.inl (v,i) ∈ allowed G p s q e ↔ v ∈ e.1.val.toFinset := by
  classical
  simp [allowed]

theorem inr_allowed (p s q : Nat) (e : G.edgeFinset × Fin q) (i : Fin s) :
    Sum.inr i ∈ allowed G p s q e := by
  classical
  simp [allowed]

theorem exists_assignment (p s q : Nat)
    (hden : ∀ U : Finset V, q * G.inducedEdgeCount U ≤ p * U.card + s) :
    ∃ f : G.edgeFinset × Fin q → (V × Fin p) ⊕ Fin s,
      Function.Injective f ∧ ∀ e, f e ∈ allowed G p s q e := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective (allowed G p s q)).mp
  intro S
  by_cases hempty : S = ∅
  · simp [hempty]
  have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E := S.image Prod.fst
  let U := HallOrientation.endpoints G E
  have hsub : S ⊆ E ×ˢ (Finset.univ : Finset (Fin q)) := by
    intro e he
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨e,he,rfl⟩,Finset.mem_univ _⟩
  have hcount : S.card ≤ q * G.inducedEdgeCount U := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product,Finset.card_univ,Fintype.card_fin] at hh
    have he := HallOrientation.edge_family_card_le G E
    exact hh.trans (by simpa [mul_comm] using Nat.mul_le_mul_left q he)
  let N : Finset ((V × Fin p) ⊕ Fin s) :=
    ((U ×ˢ Finset.univ).image Sum.inl) ∪ (Finset.univ.image Sum.inr)
  have hN : N ⊆ S.biUnion (allowed G p s q) := by
    intro z hz
    cases z with
    | inl vi =>
      have hv : vi.1 ∈ U := by simpa [N] using hz
      obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨t,ht,heq⟩ := Finset.mem_image.mp he
      refine Finset.mem_biUnion.mpr ⟨t,ht,?_⟩
      apply (inl_allowed G p s q t vi.1 vi.2).mpr
      simpa only [heq] using hve
    | inr i =>
      obtain ⟨t,ht⟩ := hS
      exact Finset.mem_biUnion.mpr ⟨t,ht,inr_allowed G p s q t i⟩
  have hd : Disjoint ((U ×ˢ (Finset.univ : Finset (Fin p))).image
      (Sum.inl : V × Fin p → (V × Fin p) ⊕ Fin s))
      ((Finset.univ : Finset (Fin s)).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hz'
    cases ha.trans hb.symm
  have hc : N.card = p * U.card + s := by
    rw [Finset.card_union_of_disjoint hd]
    rw [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective,
      Finset.card_product,Finset.card_univ,Fintype.card_fin,
      Finset.card_univ,Fintype.card_fin]
    ring
  exact (hcount.trans (hden U)).trans (hc.symm.le.trans (Finset.card_le_card hN))

theorem scaled_density (a η : Real) (q : Nat)
    (hden : ∀ U : Finset V, (G.inducedEdgeCount U:Real) ≤ a*U.card+η)
    (U : Finset V) : q * G.inducedEdgeCount U ≤ ⌈a*q⌉₊ * U.card + ⌈η*q⌉₊ := by
  have h := mul_le_mul_of_nonneg_left (hden U) (Nat.cast_nonneg q : (0:Real) ≤ q)
  have hp := mul_le_mul_of_nonneg_right (Nat.le_ceil (a*q)) (Nat.cast_nonneg U.card : (0:Real) ≤ U.card)
  have hs := Nat.le_ceil (η*q)
  have hh : (q:Real) * G.inducedEdgeCount U ≤ (⌈a*q⌉₊:Real)*U.card + (⌈η*q⌉₊:Real) := by
    nlinarith only [h,hp,hs]
  exact_mod_cast hh

theorem exists_scaled_assignment (a η : Real) (q : Nat)
    (hden : ∀ U : Finset V, (G.inducedEdgeCount U:Real) ≤ a*U.card+η) :
    ∃ f : G.edgeFinset × Fin q → (V × Fin ⌈a*q⌉₊) ⊕ Fin ⌈η*q⌉₊,
      Function.Injective f ∧ ∀ e, f e ∈ allowed G ⌈a*q⌉₊ ⌈η*q⌉₊ q e :=
  exists_assignment G _ _ q (scaled_density G a η q hden)

end Paper.HallWithOverflow
#print axioms Paper.HallWithOverflow.exists_assignment

#print axioms Paper.HallWithOverflow.scaled_density
#print axioms Paper.HallWithOverflow.exists_scaled_assignment
