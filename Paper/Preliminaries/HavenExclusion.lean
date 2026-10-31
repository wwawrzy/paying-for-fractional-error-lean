import Paper.Preliminaries.AmbientConnector
import Paper.Preliminaries.HavenReplace
import Paper.Preliminaries.HavenDrop

/-! Complete the finite covey/haven exchange argument. Physical minor
density excludes a haven of budget h*r whenever r²≥h*|V| and h>2a+1. -/
namespace Paper.HavenExclusion
attribute [local instance] Classical.propDecidable
open WeightedHaven Covey HavenConfig HavenExtension
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 3000000 in
theorem no_haven {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h r : ℕ) (hh : 2 * a + 1 < h) (hr : 1 ≤ r) (hsquare : h * Fintype.card V ≤ r * r) :
    ¬ Nonempty (Haven G (h * r)) := by
  classical
  rintro ⟨H⟩
  obtain ⟨C, X, good, hmin⟩ := HavenConfig.exists_min h r H
  have hless : C.card < h := CoveyBound.card_lt G hden ha h hh good.covey
  let U := H.region X
  let A : C → Finset V := fun S => U.filter (fun v => ∃ u ∈ S.val, G.Adj u v)
  have hA : ∀ S, A S ⊆ U := fun _ => Finset.filter_subset ..
  rcases AmbientConnector.dichotomy G U (H.nonempty X good.sizeX) A hA r hr with ht | hz
  · obtain ⟨T, hTU, hTcard, hTconn, hmeet⟩ := ht
    have hc : ∀ S ∈ C, Contacts G T S := by
      intro S hS
      obtain ⟨v, hv⟩ := hmeet ⟨S, hS⟩
      have hv' := Finset.mem_inter.mp hv
      obtain ⟨u, hu, ha⟩ := (Finset.mem_filter.mp hv'.2).2
      exact ⟨v, hv'.1, u, hu, ha.symm⟩
    obtain ⟨hgood, hscore⟩ := HavenGrow.grow H good hless T hTU hTcard hTconn hc
    have hm := hmin (insert T C) (X ∪ T) hgood
    omega
  · obtain ⟨Z, hZU, hZcount, hcut⟩ := hz
    have hUcard : U.card ≤ Fintype.card V := Finset.card_le_univ _
    have hb : (Fintype.card ↥C - 1) * U.card ≤ h * Fintype.card V := by
      rw [Fintype.card_coe]
      exact Nat.mul_le_mul (by omega) hUcard
    have hZ : Z.card ≤ r := Nat.le_of_mul_le_mul_left (c := r)
      (hZcount.trans (hb.trans hsquare)) (by omega)
    let Y := X ∪ Z
    have hY : Y.card ≤ h * r := union_budget good hless Z hZ
    have hBY : H.region Y ⊆ U := H.monotone X Y good.sizeX hY Finset.subset_union_left
    have hdis : Disjoint (H.region Y) Z := by
      apply Finset.disjoint_left.mpr
      intro v hvB hvZ
      exact Finset.disjoint_left.mp (H.avoids Y hY) hvB (Finset.mem_union_right X hvZ)
    have hnall := hcut (H.region Y) hBY (H.connected Y hY) hdis
    obtain ⟨S, hmiss⟩ := not_forall.mp hnall
    have hncontact : ¬ Contacts G S.val (H.region Y) := by
      rintro ⟨u, hu, v, hv, ha⟩
      exact hmiss ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_filter.mpr ⟨hBY hv, u, hu, ha⟩⟩⟩
    obtain ⟨T, hST, hTconn, hTF, hclosed⟩ := exists_extension H good hless Z hZ S.val S.property
    obtain ⟨hnew, hscore⟩ := HavenReplace.replace H good hless Z hZ hZU S.val S.property T hST hTconn hTF hclosed hncontact
    have hm := hmin (insert T (C.erase S.val)) (replacementX X S.val Z T) hnew
    have hzero : (X ∩ S.val).card = 0 := by omega
    obtain ⟨hdrop, hdropScore⟩ := HavenDrop.drop H good S.val S.property hzero
    have hmDrop := hmin (C.erase S.val) X hdrop
    omega

theorem balanced {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a)
    (h r : ℕ) (hh : 2 * a + 1 < h) (hr : 1 ≤ r) (hsquare : h * Fintype.card V ≤ r * r)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) : Balanced G w (h * r) := by
  by_contra hn
  exact no_haven G hden ha h r hh hr hsquare (haven_of_not_balanced G w hw (h * r) hn)
end Paper.HavenExclusion
