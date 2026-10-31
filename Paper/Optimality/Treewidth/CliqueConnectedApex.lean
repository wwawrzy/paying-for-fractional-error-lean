import Paper.Optimality.Treewidth.CliqueRootedProjection
import Paper.Optimality.Treewidth.CliqueFourElimination
namespace Paper.CliqueConnectedApex
open SimpleGraph
variable {V U : Type} {G : SimpleGraph V} {H : SimpleGraph U}
open Paper.CliqueRootedProjection
noncomputable def model_set (m : MinorModel H G) (X : Set V) (hne : X.Nonempty)
    (hconn : (G.induce X).Connected)
    (havoid : ∀ a, Disjoint X (m.branchSet a))
    (htouch : ∀ a, ∃ x ∈ X, ∃ z ∈ m.branchSet a, G.Adj x z) : MinorModel (Cone H) G := by
  classical
  let B : Option U → Set V
    | none => X
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
    | none => exact hne
    | some a => exact m.nonempty a
  · intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some b =>
        exact havoid b
    | some a =>
      cases b with
      | none =>
        exact (havoid a).symm
      | some b => exact m.disjoint a b (fun hh => hab (congrArg some hh))
  · intro a
    cases a with
    | none => exact hconn
    | some a => exact m.connected a
  · intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hab
      | some b =>
        obtain ⟨x, hx, z, hz, hvz⟩ := htouch b
        exact ⟨x, hx, z, hz, hvz⟩
    | some a =>
      cases b with
      | none =>
        obtain ⟨x, hx, z, hz, hvz⟩ := htouch a
        exact ⟨z, hz, x, hx, hvz.symm⟩
      | some b => exact m.adjacent a b hab

theorem excludes_set [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype U] [DecidableEq U] [DecidableRel H.Adj]
    (t : ℕ) (ht : 2 ≤ t) (hG : G.IsKMinorFree t)
    (m : MinorModel H G) (X : Set V) (hne : X.Nonempty) (hconn : (G.induce X).Connected)
    (havoid : ∀ a, Disjoint X (m.branchSet a))
    (htouch : ∀ a, ∃ x ∈ X, ∃ z ∈ m.branchSet a, G.Adj x z) : H.IsKMinorFree (t - 1) := by
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
  exact hG ((hk.trans hcone).trans ⟨model_set m X hne hconn havoid htouch⟩)


/-- A connected apex over a model of minimum degree three forces a K5 minor. -/
theorem forces_five [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype U] [DecidableEq U] [DecidableRel H.Adj] [Nonempty U]
    (m : MinorModel H G) (X : Set V) (hne : X.Nonempty)
    (hconn : (G.induce X).Connected)
    (havoid : ∀ a, Disjoint X (m.branchSet a))
    (htouch : ∀ a, ∃ x ∈ X, ∃ z ∈ m.branchSet a, G.Adj x z)
    (hdeg : ∀ a, 3 ≤ H.degree a) : ¬ G.IsKMinorFree 5 := by
  intro hG
  have hf : H.IsKMinorFree 4 := excludes_set 5 (by decide) hG m X hne hconn havoid htouch
  obtain ⟨a,ha⟩ := CliqueFourElimination.low_degree H hf
  have hd := hdeg a
  omega


noncomputable def cone_base_model : MinorModel H (Cone H) where
  branchSet a := {some a}
  nonempty a := Set.singleton_nonempty _
  disjoint a b hab := by
    rw [Set.disjoint_singleton]
    exact fun hh => hab (Option.some.inj hh)
  connected a := (MinorModel.refl (Cone H)).connected (some a)
  adjacent a b hab := ⟨some a, rfl, some b, rfl, hab⟩

theorem cone_free [Fintype U] [DecidableEq U] [DecidableRel H.Adj]
    (t : ℕ) (ht : 2 ≤ t) (hf : (Cone H).IsKMinorFree t) :
    H.IsKMinorFree (t-1) := by
  classical
  exact CliqueRootedProjection.excludes t ht hf cone_base_model none
    (by intro a; simp [cone_base_model])
    (by intro a; exact ⟨some a,rfl,True.intro⟩)

/-- Three disjoint connected apex sets, pairwise touching and each touching all
original model branches, reduce the excluded clique order by three. -/
theorem three_apices [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype U] [DecidableEq U] [DecidableRel H.Adj]
    (hG : G.IsKMinorFree 7) (m : MinorModel H G) (X Y Z : Set V)
    (hneX : X.Nonempty) (hneY : Y.Nonempty) (hneZ : Z.Nonempty)
    (hcX : (G.induce X).Connected) (hcY : (G.induce Y).Connected)
    (hcZ : (G.induce Z).Connected)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (haX : ∀ a, Disjoint X (m.branchSet a))
    (haY : ∀ a, Disjoint Y (m.branchSet a))
    (haZ : ∀ a, Disjoint Z (m.branchSet a))
    (htX : ∀ a, ∃ x ∈ X, ∃ z ∈ m.branchSet a, G.Adj x z)
    (htY : ∀ a, ∃ x ∈ Y, ∃ z ∈ m.branchSet a, G.Adj x z)
    (htZ : ∀ a, ∃ x ∈ Z, ∃ z ∈ m.branchSet a, G.Adj x z)
    (heYX : ∃ y ∈ Y, ∃ x ∈ X, G.Adj y x)
    (heZX : ∃ z ∈ Z, ∃ x ∈ X, G.Adj z x)
    (heZY : ∃ z ∈ Z, ∃ y ∈ Y, G.Adj z y) : H.IsKMinorFree 4 := by
  classical
  let mX := model_set m X hneX hcX haX htX
  have haYX : ∀ a, Disjoint Y (mX.branchSet a) := by
    intro a; cases a with
    | none => exact hXY.symm
    | some a => exact haY a
  have htYX : ∀ a, ∃ y ∈ Y, ∃ z ∈ mX.branchSet a, G.Adj y z := by
    intro a; cases a with
    | none => exact heYX
    | some a => exact htY a
  let mY := model_set mX Y hneY hcY haYX htYX
  have haZY : ∀ a, Disjoint Z (mY.branchSet a) := by
    intro a; cases a with
    | none => exact hYZ.symm
    | some a =>
      cases a with
      | none => exact hXZ.symm
      | some a => exact haZ a
  have htZY : ∀ a, ∃ z ∈ Z, ∃ w ∈ mY.branchSet a, G.Adj z w := by
    intro a; cases a with
    | none => exact heZY
    | some a =>
      cases a with
      | none => exact heZX
      | some a => exact htZ a
  have h6 : (Cone (Cone H)).IsKMinorFree 6 :=
    excludes_set 7 (by decide) hG mY Z hneZ hcZ haZY htZY
  have h5 : (Cone H).IsKMinorFree 5 := cone_free 6 (by decide) h6
  exact cone_free 5 (by decide) h5

end Paper.CliqueConnectedApex



