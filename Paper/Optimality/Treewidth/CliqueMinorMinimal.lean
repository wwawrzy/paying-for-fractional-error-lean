import Paper.Optimality.Treewidth.CliqueAffineCore

/-! A globally minimal affine counterexample. Unlike single-edge contraction
minimality, this controls every actual minor on fewer vertices and can be
used for separator projections. The selection is over natural vertex counts. -/
namespace Paper.CliqueMinorMinimal

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def BelowThreshold (k b B : ℕ) : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] (J : SimpleGraph U) [DecidableRel J.Adj],
    J.IsMinor G → B ≤ Fintype.card U → Fintype.card U < Fintype.card V →
      J.edgeFinset.card < k * Fintype.card U - b

theorem extract (k b B : ℕ) (hB : 0 < B) (hb : b ≤ k * B)
    (hboundary : B.choose 2 < k * B - b)
    (hV : B ≤ Fintype.card V) (hdense : k * Fintype.card V - b ≤ G.edgeFinset.card) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      B < Fintype.card W ∧ H.edgeFinset.card = k * Fintype.card W - b ∧
      (∀ v, 0 < H.degree v) ∧
      (∀ v w, H.Adj v w → k ≤ Fintype.card (H.commonNeighbors v w)) ∧
      H.IsMinor G ∧ BelowThreshold H k b B := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U)
      (J : SimpleGraph U) (_ : DecidableRel J.Adj),
      Fintype.card U = n ∧ B ≤ n ∧ k * n - b ≤ J.edgeFinset.card ∧ J.IsMinor G
  have hex : ∃ n, P n :=
    ⟨Fintype.card V, V, inferInstance, inferInstance, G, inferInstance,
      rfl, hV, hdense, IsMinor.refl G⟩
  obtain ⟨U, _, _, J, _, hcard, hU, hd, hm⟩ := Nat.find_spec hex
  have hU' : B ≤ Fintype.card U := by omega
  have hd' : k * Fintype.card U - b ≤ J.edgeFinset.card := by simpa only [hcard] using hd
  obtain ⟨W, _, _, H, _, hW, he, hp, hc, hHJ⟩ :=
    CliqueAffineCore.extract J k b B hB hb hboundary hU' hd'
  have hHW : Fintype.card W ≤ Nat.find hex := by
    obtain ⟨model⟩ := hHJ
    have hh := model.natCard_le
    simpa only [Nat.card_eq_fintype_card, hcard] using hh
  refine ⟨W, inferInstance, inferInstance, H, inferInstance,
    hW, he, hp, hc, hHJ.trans hm, ?_⟩
  intro A _ _ F _ hFH hA hless
  by_contra hnot
  have hP : P (Fintype.card A) :=
    ⟨A, inferInstance, inferInstance, F, inferInstance,
      rfl, hA, by omega, hFH.trans (hHJ.trans hm)⟩
  exact Nat.find_min hex (lt_of_lt_of_le hless hHW) hP

theorem degree_lower (k b B : ℕ) (hW : B < Fintype.card V)
    (hb : b ≤ k * B) (he : G.edgeFinset.card = k * Fintype.card V - b)
    (hminimal : BelowThreshold G k b B) (v : V) : k + 1 ≤ G.degree v := by
  classical
  let A := ({v}ᶜ : Set V)
  have hcard : Fintype.card A = Fintype.card V - 1 := by
    dsimp only [A]
    rw [Fintype.card_compl_set, Set.card_singleton]
  have hfloor : B ≤ Fintype.card A := by omega
  have hsmall : Fintype.card A < Fintype.card V := by omega
  have hbound := hminimal A (G.induce A) (IsMinor.of_induce G A) hfloor hsmall
  have hedge : (G.induce A).edgeFinset.card = G.edgeFinset.card - G.degree v := by
    dsimp only [A]
    rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
  have hpred : k * (Fintype.card V - 1) + k = k * Fintype.card V := by
    calc
      _ = k * (Fintype.card V - 1 + 1) := by simp only [Nat.mul_add, Nat.mul_one]
      _ = _ := by congr 1; omega
  have hb' : b ≤ k * (Fintype.card V - 1) :=
    hb.trans (Nat.mul_le_mul_left k (by omega))
  rw [hedge, hcard] at hbound
  omega

end Paper.CliqueMinorMinimal

#print axioms Paper.CliqueMinorMinimal.extract
#print axioms Paper.CliqueMinorMinimal.degree_lower
