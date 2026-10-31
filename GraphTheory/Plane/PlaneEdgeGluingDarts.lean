import GraphTheory.Plane.PlaneEdgeGluingGraph

/-!
# The two deleted dart copies in an actual edge sum

The full disjoint dart sum is explicitly the surviving glued-dart domain plus
the two orientations of the duplicated right common edge. This equivalence
connects the generic erase/restrict permutation operations to the actual graph.
-/

namespace PlaneTopology.PlaneEdgeGluingDarts

open SimpleGraph PlaneTopology.PlaneEdgeGluingGraph

variable {A B : Type*}
variable (L : SimpleGraph (Fin 2 ⊕ A)) (R : SimpleGraph (Fin 2 ⊕ B))

/-- The two orientations of the right copy of the common edge. -/
def rightCommonDart (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) : Bool → R.Dart
  | false => ⟨(Sum.inl 0, Sum.inl 1), hR⟩
  | true => ⟨(Sum.inl 1, Sum.inl 0), hR.symm⟩

theorem rightCommonDart_injective (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Function.Injective (rightCommonDart R hR) := by
  intro b c h
  have hs := congrArg (fun d : R.Dart ↦ d.fst) h
  cases b <;> cases c <;> simp_all [rightCommonDart]

/-- The duplicated common-edge darts are exactly the right darts not retained. -/
theorem rightCommonDart_ne_survivor (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (b : Bool) (d : RightSurvivor R) : rightCommonDart R hR b ≠ d.1 := by
  intro h
  have hd := d.2
  rw [← h] at hd
  cases b <;> simp [rightCommonDart] at hd

/-- Every right dart survives or is one of the two deleted common orientations. -/
theorem rightDart_survivor_or_common (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) (d : R.Dart) :
    (∃ e : RightSurvivor R, e.1 = d) ∨ ∃ b : Bool, rightCommonDart R hR b = d := by
  classical
  by_cases hd : ¬(d.fst.isLeft ∧ d.snd.isLeft)
  · exact Or.inl ⟨⟨d, hd⟩, rfl⟩
  right
  have hb : d.fst.isLeft ∧ d.snd.isLeft := not_not.mp hd
  rcases d with ⟨⟨s, t⟩, h⟩
  cases s with
  | inr a => simp at hb
  | inl i =>
    cases t with
    | inr b => simp at hb
    | inl j =>
      fin_cases i <;> fin_cases j
      · exact (h.ne rfl).elim
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
      · exact (h.ne rfl).elim

/-- Restore the two duplicated darts to the disjoint original dart sum. -/
def expandedDart (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    GluedDart L R ⊕ Bool → L.Dart ⊕ R.Dart
  | Sum.inl (Sum.inl d) => Sum.inl d
  | Sum.inl (Sum.inr d) => Sum.inr d.1
  | Sum.inr b => Sum.inr (rightCommonDart R hR b)

theorem expandedDart_injective (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Function.Injective (expandedDart L R hR) := by
  intro x y h
  cases x with
  | inl x =>
    cases x with
    | inl d =>
      cases y with
      | inl y =>
        cases y with
        | inl e => exact congrArg (Sum.inl ∘ Sum.inl) (Sum.inl.inj h)
        | inr e => cases h
      | inr b => cases h
    | inr d =>
      cases y with
      | inl y =>
        cases y with
        | inl e => cases h
        | inr e => exact congrArg (Sum.inl ∘ Sum.inr) (Subtype.ext (Sum.inr.inj h))
      | inr b => exact (rightCommonDart_ne_survivor R hR b d (Sum.inr.inj h).symm).elim
  | inr b =>
    cases y with
    | inl y =>
      cases y with
      | inl e => cases h
      | inr e => exact (rightCommonDart_ne_survivor R hR b e (Sum.inr.inj h)).elim
    | inr c => exact congrArg Sum.inr (rightCommonDart_injective R hR (Sum.inr.inj h))

theorem expandedDart_surjective (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    Function.Surjective (expandedDart L R hR) := by
  intro d
  cases d with
  | inl d => exact ⟨Sum.inl (Sum.inl d), rfl⟩
  | inr d =>
    rcases rightDart_survivor_or_common R hR d with ⟨e, he⟩ | ⟨b, hb⟩
    · exact ⟨Sum.inl (Sum.inr e), congrArg Sum.inr he⟩
    · exact ⟨Sum.inr b, congrArg Sum.inr hb⟩

/-- Exact decomposition of full darts as glued darts plus one duplicated edge. -/
noncomputable def expandedDartEquiv (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    GluedDart L R ⊕ Bool ≃ L.Dart ⊕ R.Dart :=
  Equiv.ofBijective (expandedDart L R hR)
    ⟨expandedDart_injective L R hR, expandedDart_surjective L R hR⟩

theorem expandedDartEquiv_apply (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (d : GluedDart L R ⊕ Bool) : expandedDartEquiv L R hR d = expandedDart L R hR d := rfl

/-- Full reversal acts as glued reversal plus reversal of the duplicate edge. -/
theorem expandedDart_reversal (hR : R.Adj (Sum.inl 0) (Sum.inl 1))
    (d : GluedDart L R ⊕ Bool) :
    expandedDart L R hR (Equiv.sumCongr (gluedReversal L R) (Equiv.swap false true) d) =
      Equiv.sumCongr (dartSymmPerm L) (dartSymmPerm R) (expandedDart L R hR d) := by
  cases d with
  | inl d => cases d <;> rfl
  | inr b => cases b <;> rfl

section Finite

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

/-- The precise edge sum loses just the duplicated common edge. -/
theorem card_edges_gluedGraph (hL : L.Adj (Sum.inl 0) (Sum.inl 1))
    (hR : R.Adj (Sum.inl 0) (Sum.inl 1)) :
    (by classical exact (gluedGraph L R).edgeFinset.card) + 1 =
      L.edgeFinset.card + R.edgeFinset.card := by
  classical
  letI : Fintype (RightSurvivor R) := by unfold RightSurvivor; infer_instance
  have hfull := Fintype.card_congr (expandedDartEquiv L R hR)
  have hglue := Fintype.card_congr (gluedDartEquiv L R hL)
  simp only [Fintype.card_sum, Fintype.card_bool] at hfull hglue
  rw [L.dart_card_eq_twice_card_edges, R.dart_card_eq_twice_card_edges] at hfull
  rw [L.dart_card_eq_twice_card_edges] at hglue
  rw [(gluedGraph L R).dart_card_eq_twice_card_edges] at hglue
  omega

end Finite

#print axioms expandedDartEquiv
#print axioms expandedDart_reversal
#print axioms card_edges_gluedGraph

end PlaneTopology.PlaneEdgeGluingDarts
