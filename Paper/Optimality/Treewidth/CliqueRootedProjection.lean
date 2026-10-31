import Paper.Optimality.Treewidth.CliqueDegree
import Paper.Optimality.Treewidth.CliqueDenseCore
import Paper.Optimality.Treewidth.FiveCliqueSharp

/-! An apex extends an actual rooted minor. This applies to a simultaneous
separator projection even when absorbed branch sets leave the original
neighborhood. Disjointness from the apex and its edges into every branch
are retained explicitly. -/
namespace Paper.CliqueRootedProjection

open SimpleGraph

macro "existingConeGraph%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `GraphTheory.SimpleGraph.Minor.AverageDegree
    `SimpleGraph.kid2056Cone))

macro "existingConeMinorProof%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `GraphTheory.SimpleGraph.Minor.AverageDegree
    `SimpleGraph.kid2056Cone_isMinor_mono))

def Cone {U : Type} (H : SimpleGraph U) : SimpleGraph (Option U) := existingConeGraph% H

variable {V U : Type} {G : SimpleGraph V} {H : SimpleGraph U}

noncomputable def model (m : MinorModel H G) (v : V)
    (havoid : ∀ a, v ∉ m.branchSet a)
    (htouch : ∀ a, ∃ z ∈ m.branchSet a, G.Adj v z) : MinorModel (Cone H) G := by
  classical
  let B : Option U → Set V
    | none => {v}
    | some a => m.branchSet a
  refine {
    branchSet := B
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    adjacent := ?_
  }
  · intro a
    cases a with
    | none => exact ⟨v, rfl⟩
    | some a => exact m.nonempty a
  · intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some b =>
        rw [Set.disjoint_left]
        intro z hzv hzb
        exact havoid b ((show z = v from hzv) ▸ hzb)
    | some a =>
      cases b with
      | none =>
        rw [Set.disjoint_left]
        intro z hza hzv
        exact havoid a ((show z = v from hzv) ▸ hza)
      | some b => exact m.disjoint a b (fun hh => hab (congrArg some hh))
  · intro a
    cases a with
    | none => exact (MinorModel.refl G).connected v
    | some a => exact m.connected a
  · intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hab
      | some b =>
        obtain ⟨z, hz, hvz⟩ := htouch b
        exact ⟨v, rfl, z, hz, hvz⟩
    | some a =>
      cases b with
      | none =>
        obtain ⟨z, hz, hvz⟩ := htouch a
        exact ⟨z, hz, v, rfl, hvz.symm⟩
      | some b => exact m.adjacent a b hab

theorem excludes [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype U] [DecidableEq U] [DecidableRel H.Adj]
    (t : ℕ) (ht : 2 ≤ t) (hG : G.IsKMinorFree t)
    (m : MinorModel H G) (v : V) (havoid : ∀ a, v ∉ m.branchSet a)
    (htouch : ∀ a, ∃ z ∈ m.branchSet a, G.Adj v z) : H.IsKMinorFree (t - 1) := by
  classical
  intro hK
  have hcone : (Cone (completeGraph (Fin (t - 1)))).IsMinor (Cone H) :=
    existingConeMinorProof% hK
  have htop : Cone (completeGraph (Fin (t - 1))) = ⊤ := by
    ext a b
    cases a with
    | none =>
      cases b with
      | none =>
        change False ↔ (none : Option (Fin (t - 1))) ≠ none
        simp
      | some b =>
        change True ↔ (none : Option (Fin (t - 1))) ≠ some b
        simp
    | some a =>
      cases b with
      | none =>
        change True ↔ (some a : Option (Fin (t - 1))) ≠ none
        simp
      | some b =>
        change (completeGraph (Fin (t - 1))).Adj a b ↔
          (some a : Option (Fin (t - 1))) ≠ some b
        simp [completeGraph]
  have hcard : Fintype.card (Option (Fin (t - 1))) = t := by
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  have hfull : ∀ a : Option (Fin (t - 1)),
      t - 1 ≤ (Cone (completeGraph (Fin (t - 1)))).degree a := by
    intro a
    have hdeg : (Cone (completeGraph (Fin (t - 1)))).degree a =
        Nat.card ((Cone (completeGraph (Fin (t - 1)))).neighborSet a) := by
      rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
    rw [hdeg, htop]
    have hn : (⊤ : SimpleGraph (Option (Fin (t - 1)))).neighborSet a =
        ({a} : Set (Option (Fin (t - 1))))ᶜ := by
      ext b
      simp [neighborSet, ne_comm]
    rw [hn, Nat.card_eq_fintype_card, Fintype.card_compl_set, Set.card_singleton, hcard]
  have hk := CliqueDegree.complete_minor (Cone (completeGraph (Fin (t - 1)))) t hcard hfull
  exact hG ((hk.trans hcone).trans ⟨model m v havoid htouch⟩)

theorem edge_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype U] [DecidableEq U] [DecidableRel H.Adj]
    (hG : G.IsKMinorFree 6) (m : MinorModel H G) (v : V)
    (havoid : ∀ a, v ∉ m.branchSet a)
    (htouch : ∀ a, ∃ z ∈ m.branchSet a, G.Adj v z)
    (hU : 3 ≤ Fintype.card U) : H.edgeFinset.card ≤ 3 * Fintype.card U - 6 :=
  FiveCliqueSharp.edge_bound H (excludes 6 (by decide) hG m v havoid htouch) hU

end Paper.CliqueRootedProjection

#print axioms Paper.CliqueRootedProjection.model
#print axioms Paper.CliqueRootedProjection.excludes
#print axioms Paper.CliqueRootedProjection.edge_bound
