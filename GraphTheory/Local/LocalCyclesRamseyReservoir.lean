import Mathlib

/-! A quantitative finite reservoir argument for the Ramsey step in LOCAL.
Colorings are defined on all finite sets; homogeneity only tests the required
uniform rank. All chosen identifiers remain in the original finite set. -/

noncomputable section

namespace LocalCyclesRamseyReservoir

open scoped BigOperators

def Homogeneous {q : ℕ} (f : Finset ℕ → Fin q) (s : ℕ) (T : Finset ℕ) : Prop :=
  ∃ color, ∀ A ⊆ T, A.card = s → f A = color

def Ordered (S U : Finset ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ U, a < b

/-- The color of an extension of a rank-k chosen set no longer depends on
the later identifier, including later identifiers already chosen. -/
def EndHomogeneous {q : ℕ} (k : ℕ) (f : Finset ℕ → Fin q)
    (S U : Finset ℕ) : Prop :=
  ∀ A ⊆ S, A.card = k → ∀ x ∈ S ∪ U, ∀ y ∈ S ∪ U,
    (∀ a ∈ A, a < x) → (∀ a ∈ A, a < y) → f (insert x A) = f (insert y A)

/-- Actual simultaneous thinning, with at most q^(2^|S|) color vectors. -/
theorem thin_extensions (q K : ℕ) (hq : 0 < q) (S U : Finset ℕ)
    (f : Finset ℕ → Fin q) (hU : q^(2^S.card)*K ≤ U.card) :
    ∃ V ⊆ U, K ≤ V.card ∧
      ∀ A ⊆ S, ∀ x ∈ V, ∀ y ∈ V, f (insert x A) = f (insert y A) := by
  classical
  let code : ℕ → (S.powerset → Fin q) := fun x A => f (insert x A.val)
  letI : Nonempty (S.powerset → Fin q) := ⟨fun _ => ⟨0, hq⟩⟩
  have hcard : (Finset.univ : Finset (S.powerset → Fin q)).card = q^(2^S.card) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, Finset.card_powerset]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := U) (t := Finset.univ) (f := code) (fun _ _ => Finset.mem_univ _)
    Finset.univ_nonempty (by simpa only [hcard] using hU)
  refine ⟨U.filter (fun x => code x = c), Finset.filter_subset _ _, hc, ?_⟩
  intro A hAS x hx y hy
  have heq := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  exact congrFun heq ⟨A, Finset.mem_powerset.mpr hAS⟩

theorem endHomogeneous_step {q k : ℕ} {f : Finset ℕ → Fin q}
    (S U V : Finset ℕ) (v : ℕ) (hv : v ∈ U)
    (horder : Ordered S U) (hVU : V ⊆ U)
    (hold : EndHomogeneous k f S U)
    (hnew : ∀ A ⊆ insert v S, ∀ x ∈ V, ∀ y ∈ V,
      f (insert x A) = f (insert y A)) :
    EndHomogeneous k f (insert v S) V := by
  classical
  intro A hAS hA x hx y hy hAx hAy
  by_cases hvA : v ∈ A
  · have hxV : x ∈ V := by
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact False.elim (lt_irrefl x (hAx x hvA))
        · exact False.elim (lt_asymm (hAx v hvA) (horder x hx v hv))
      · exact hx
    have hyV : y ∈ V := by
      rcases Finset.mem_union.mp hy with hy | hy
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact False.elim (lt_irrefl y (hAy y hvA))
        · exact False.elim (lt_asymm (hAy v hvA) (horder y hy v hv))
      · exact hy
    exact hnew A hAS x hxV y hyV
  · have hASold : A ⊆ S := by
      intro a ha
      rcases Finset.mem_insert.mp (hAS ha) with rfl | hs
      · contradiction
      · exact hs
    have hsub : insert v S ∪ V ⊆ S ∪ U := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_union_right _ hv
        · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_right _ (hVU ha)
    exact hold A hASold hA x (hsub hx) y (hsub hy) hAx hAy

/-- The full finite construction, not an assumed homogeneous-set oracle.
The initial budget is (q^(2^m)+1)^l for l further choices and at most m
chosen identifiers in total. One nonempty reservoir remains at the end. -/
theorem extend_reservoir (q m k l : ℕ) (hq : 0 < q) (f : Finset ℕ → Fin q)
    (S U : Finset ℕ) (hS : S.card+l ≤ m)
    (hU : (q^(2^m)+1)^l ≤ U.card)
    (horder : Ordered S U) (hend : EndHomogeneous k f S U) :
    ∃ S' U' : Finset ℕ,
      S ⊆ S' ∧ S' ∪ U' ⊆ S ∪ U ∧ S'.card = S.card+l ∧ U'.Nonempty ∧
      Ordered S' U' ∧ EndHomogeneous k f S' U' := by
  classical
  induction l generalizing S U with
  | zero =>
    refine ⟨S, U, Finset.Subset.refl S, Finset.Subset.refl _, by simp, ?_, horder, hend⟩
    exact Finset.card_pos.mp (by simpa using hU)
  | succ l ih =>
    let Q := q^(2^m)
    have hpow : 1 ≤ (Q+1)^l := Nat.one_le_pow _ _ (by omega)
    have hUne : U.Nonempty := Finset.card_pos.mp (by
      have hpos : 0 < (Q+1)^(l+1) := by positivity
      exact lt_of_lt_of_le hpos hU)
    let v := U.min' hUne
    have hv : v ∈ U := Finset.min'_mem _ _
    have hvS : v ∉ S := fun hvS => lt_irrefl v (horder v hvS v hv)
    have hnewCard : (insert v S).card = S.card+1 := Finset.card_insert_of_notMem hvS
    have hnewBound : (insert v S).card ≤ m := by omega
    have hcode : q^(2^(insert v S).card) ≤ Q := by
      dsimp [Q]
      gcongr <;> omega
    have herase : Q*(Q+1)^l ≤ (U.erase v).card := by
      have hU' : (Q+1)^l*(Q+1) ≤ U.card := by simpa only [pow_succ] using hU
      have he := Finset.card_erase_add_one hv
      nlinarith
    obtain ⟨V, hVUerase, hV, hstable⟩ := thin_extensions q ((Q+1)^l) hq
      (insert v S) (U.erase v) f
      ((Nat.mul_le_mul_right ((Q+1)^l) hcode).trans herase)
    have hVU : V ⊆ U := hVUerase.trans (Finset.erase_subset _ _)
    have hmin : ∀ x ∈ V, v < x := by
      intro x hx
      have hxU : x ∈ U := hVU hx
      have hvx : v ≤ x := Finset.min'_le U x hxU
      have hxv : x ≠ v := (Finset.mem_erase.mp (hVUerase hx)).1
      omega
    have horder' : Ordered (insert v S) V := by
      intro a ha x hx
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hmin x hx
      · exact horder a ha x (hVU hx)
    have hend' := endHomogeneous_step S U V v hv horder hVU hend hstable
    obtain ⟨S', U', hSS', htotal, hcard, hnonempty, horder'', hend''⟩ :=
      ih (insert v S) V (by omega) hV horder' hend'
    have hlocal : insert v S ∪ V ⊆ S ∪ U := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_union_right _ hv
        · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_right _ (hVU ha)
    exact ⟨S', U', (Finset.subset_insert _ _).trans hSS', htotal.trans hlocal,
      by omega, hnonempty, horder'', hend''⟩

theorem finite_reservoir (q m k : ℕ) (hq : 0 < q) (hk : 0 < k)
    (f : Finset ℕ → Fin q) (U : Finset ℕ) (hU : (q^(2^m)+1)^m ≤ U.card) :
    ∃ S T : Finset ℕ, S ∪ T ⊆ U ∧ S.card = m ∧ T.Nonempty ∧
      Ordered S T ∧ EndHomogeneous k f S T := by
  have he : EndHomogeneous k f ∅ U := by
    intro A hA hcard
    have hAe : A = ∅ := Finset.subset_empty.mp hA
    simp only [hAe, Finset.card_empty] at hcard
    omega
  obtain ⟨S, T, _, hsub, hcard, hnonempty, horder, hend⟩ :=
    extend_reservoir q m k m hq f ∅ U (by simp) hU (by simp [Ordered]) he
  exact ⟨S, T, by simpa using hsub, by simpa using hcard, hnonempty, horder, hend⟩

/-- Index k denotes rank k+1. This deliberately loose recurrence has a
constant tower-height increase per rank and an elementary reservoir proof. -/
def ramseyBound (q : ℕ) : ℕ → ℕ → ℕ
  | 0, L => q*(L-1)+1
  | k+1, L =>
      let m := ramseyBound q k (L-1)
      (q^(2^m)+1)^m

/-- Quantitative finite hypergraph Ramsey on the original set of IDs.
The theorem supplies both the subset and its homogeneous color. -/
theorem quantitative_ramsey (q k L : ℕ) (hq : 0 < q) (hL : k+1 ≤ L)
    (f : Finset ℕ → Fin q) (U : Finset ℕ) (hU : ramseyBound q k L ≤ U.card) :
    ∃ T ⊆ U, T.card = L ∧ Homogeneous f (k+1) T := by
  classical
  induction k generalizing L U f with
  | zero =>
    have hineq : (Finset.univ : Finset (Fin q)).card*(L-1) < U.card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      simp only [ramseyBound] at hU
      omega
    obtain ⟨col, _, hcol⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := U) (t := Finset.univ) (f := fun x => f {x})
      (fun _ _ => Finset.mem_univ _) hineq
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (show L ≤
      (U.filter (fun x => f {x} = col)).card by omega)
    refine ⟨T, hT.trans (Finset.filter_subset _ _), hcard, col, ?_⟩
    intro A hA hAc
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hAc
    exact (Finset.mem_filter.mp (hT (hA (Finset.mem_singleton_self a)))).2
  | succ k ih =>
    let m := ramseyBound q k (L-1)
    obtain ⟨S, R, hSR, hScard, hRne, horder, hend⟩ :=
      finite_reservoir q m (k+1) hq (by omega) f U hU
    obtain ⟨v, hv⟩ := hRne
    let g : Finset ℕ → Fin q := fun A => f (insert v A)
    obtain ⟨Y, hYS, hYcard, col, hYmono⟩ :=
      ih (L-1) (by omega) g S (by dsimp [m] at hScard; omega)
    have hvS : v ∉ S := fun hvS => lt_irrefl v (horder v hvS v hv)
    have hvY : v ∉ Y := fun hvY => hvS (hYS hvY)
    refine ⟨insert v Y, ?_, ?_, col, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hSR (Finset.mem_union_right _ hv)
      · exact hSR (Finset.mem_union_left _ (hYS ha))
    · rw [Finset.card_insert_of_notMem hvY, hYcard]
      omega
    · intro A hA hAcard
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      let x := A.max' hAne
      have hx : x ∈ A := Finset.max'_mem _ _
      have hxAV : x ∈ insert v Y := hA hx
      have hAY : A.erase x ⊆ Y := by
        intro a ha
        have haA := (Finset.mem_erase.mp ha).2
        have hax := (Finset.mem_erase.mp ha).1
        rcases Finset.mem_insert.mp (hA haA) with rfl | haY
        · rcases Finset.mem_insert.mp hxAV with hxeq | hxY
          · exact False.elim (hax hxeq.symm)
          · have hxv := horder x (hYS hxY) a hv
            have hvx := Finset.le_max' A a haA
            omega
        · exact haY
      have hsmall : (A.erase x).card = k+1 := by
        rw [Finset.card_erase_of_mem hx, hAcard]
        omega
      have hbeforeX : ∀ a ∈ A.erase x, a < x := by
        intro a ha
        have hax := (Finset.mem_erase.mp ha).1
        have hle := Finset.le_max' A a (Finset.mem_erase.mp ha).2
        omega
      have hxSR : x ∈ S ∪ R := by
        rcases Finset.mem_insert.mp hxAV with rfl | hxY
        · exact Finset.mem_union_right _ hv
        · exact Finset.mem_union_left _ (hYS hxY)
      have he := hend (A.erase x) (hAY.trans hYS) hsmall x hxSR v
        (Finset.mem_union_right _ hv) hbeforeX
        (fun a ha => horder a (hYS (hAY ha)) v hv)
      calc
        f A = f (insert x (A.erase x)) := by rw [Finset.insert_erase hx]
        _ = f (insert v (A.erase x)) := he
        _ = col := hYmono (A.erase x) hAY hsmall

#print axioms thin_extensions
#print axioms endHomogeneous_step
#print axioms extend_reservoir
#print axioms finite_reservoir
#print axioms quantitative_ramsey

end LocalCyclesRamseyReservoir
