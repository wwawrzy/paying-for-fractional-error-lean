import Paper.Preliminaries.StarMap
import Paper.Preliminaries.StarCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-! Direct co-occurrence counting for physical short lists.  Each pair has one
supplier; external suppliers are contracted to their most frequent second end.
No incidence blowup or sunflower hierarchy is used. -/
namespace Paper.DirectListPairs
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def pairs (Λ : V → Finset V) (X Y : Finset V) : Finset (V × V) :=
  (X ×ˢ Y).filter (fun e => ∃ r, e.1 ∈ Λ r ∧ e.2 ∈ Λ r)

theorem mem_pairs (Λ : V → Finset V) (X Y : Finset V) (e : V × V) :
    e ∈ pairs Λ X Y ↔ e.1 ∈ X ∧ e.2 ∈ Y ∧ ∃ r, e.1 ∈ Λ r ∧ e.2 ∈ Λ r := by
  simp only [pairs, Finset.mem_filter, Finset.mem_product]
  tauto

/-- A largest fiber retains at least a reciprocal-image-size fraction;
the statement avoids division and its rounding cases. -/
theorem exists_large_fiber {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (g : A → B) (hS : S.Nonempty) (f : ℕ)
    (himage : (S.image g).card ≤ f) :
    ∃ y ∈ S.image g, S.card ≤ f * (S.filter (fun e => g e = y)).card := by
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (S.image g)
    (fun y => (S.filter (fun e => g e = y)).card) (hS.image g)
  refine ⟨y, hy, ?_⟩
  have hc := Finset.card_le_mul_card_image S
    (S.filter (fun e => g e = y)).card hmax
  exact hc.trans (by simpa only [mul_comm] using
    Nat.mul_le_mul_left (S.filter (fun e => g e = y)).card himage)

noncomputable def origin (Λ : V → Finset V) (e : V × V) : V :=
  if h : ∃ r, e.1 ∈ Λ r ∧ e.2 ∈ Λ r then h.choose else e.1

theorem origin_spec (Λ : V → Finset V) (X Y : Finset V) {e : V × V}
    (he : e ∈ pairs Λ X Y) : e.1 ∈ Λ (origin Λ e) ∧ e.2 ∈ Λ (origin Λ e) := by
  have hh := ((mem_pairs Λ X Y e).mp he).2.2
  simpa only [origin, dif_pos hh] using hh.choose_spec

noncomputable def fiber (Λ : V → Finset V) (X Y : Finset V) (r : V) : Finset (V × V) :=
  (pairs Λ X Y).filter (fun e => origin Λ e = r)

theorem fiber_subset (Λ : V → Finset V) (X Y : Finset V) (r : V) :
    fiber Λ X Y r ⊆ Λ r ×ˢ Λ r := by
  intro e he
  obtain ⟨hp, hr⟩ := Finset.mem_filter.mp he
  have hh := origin_spec Λ X Y hp
  rw [hr] at hh
  exact Finset.mem_product.mpr hh

noncomputable def majority (Λ : V → Finset V) (X Y : Finset V) (r : V) : V :=
  if h : (fiber Λ X Y r).Nonempty then
    (Finset.exists_max_image ((fiber Λ X Y r).image Prod.snd)
      (fun y => ((fiber Λ X Y r).filter (fun e => e.2 = y)).card)
      (h.image Prod.snd)).choose
  else r

theorem majority_spec (Λ : V → Finset V) (X Y : Finset V) (r : V)
    (hr : (fiber Λ X Y r).Nonempty) :
    majority Λ X Y r ∈ (fiber Λ X Y r).image Prod.snd ∧
      ∀ y ∈ (fiber Λ X Y r).image Prod.snd,
        ((fiber Λ X Y r).filter (fun e => e.2 = y)).card ≤
        ((fiber Λ X Y r).filter (fun e => e.2 = majority Λ X Y r)).card := by
  simpa only [majority, dif_pos hr] using
    (Finset.exists_max_image ((fiber Λ X Y r).image Prod.snd)
      (fun y => ((fiber Λ X Y r).filter (fun e => e.2 = y)).card)
      (hr.image Prod.snd)).choose_spec

theorem majority_mem (Λ : V → Finset V) (X Y : Finset V) (r : V)
    (hr : (fiber Λ X Y r).Nonempty) :
    majority Λ X Y r ∈ Y ∧ majority Λ X Y r ∈ Λ r := by
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (majority_spec Λ X Y r hr).1
  have hp := (Finset.mem_filter.mp he).1
  have hs := Finset.mem_product.mp (fiber_subset Λ X Y r he)
  exact heq ▸ ⟨((mem_pairs Λ X Y e).mp hp).2.1, hs.2⟩

theorem fiber_card_le (Λ : V → Finset V) (X Y : Finset V) (f : ℕ)
    (hrank : ∀ r, (Λ r).card ≤ f) (r : V) :
    (fiber Λ X Y r).card ≤ f *
      ((fiber Λ X Y r).filter (fun e => e.2 = majority Λ X Y r)).card := by
  by_cases hr : (fiber Λ X Y r).Nonempty
  · have hs : (fiber Λ X Y r).image Prod.snd ⊆ Λ r := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_product.mp (fiber_subset Λ X Y r he)).2
    have hc := Finset.card_le_mul_card_image (fiber Λ X Y r)
      (((fiber Λ X Y r).filter (fun e => e.2 = majority Λ X Y r)).card)
      (majority_spec Λ X Y r hr).2
    have hb := (Finset.card_le_card hs).trans (hrank r)
    exact hc.trans (by simpa only [mul_comm] using
      Nat.mul_le_mul_left (((fiber Λ X Y r).filter (fun e => e.2 = majority Λ X Y r)).card) hb)
  · have he : fiber Λ X Y r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hr
    simp [he]

/-- Ordered cross-pairs in a genuine minor are counted once, not twice. -/
theorem cross_pairs_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hdis : Disjoint X Y) (Q : Finset (V × V))
    (hQ : Q ⊆ X ×ˢ Y) (κ : V → V)
    (hfix : ∀ v ∈ X ∪ Y, κ v = v)
    (hstar : ∀ v, κ v = v ∨ G.Adj (κ v) v)
    (hlink : ∀ e ∈ Q, ∃ r, κ r = e.2 ∧ G.Adj e.1 r)
    {a : ℝ} (hden : MinorDensity.Bound G a) :
    (Q.card : ℝ) ≤ a * (X.card + Y.card) := by
  let U := X ∪ Y
  let J := StarMap.graph G κ U
  let X' := X.subtype (fun v => v ∈ U)
  let Y' := Y.subtype (fun v => v ∈ U)
  have hX : X'.card = X.card := StarCounting.subtype_card U X Finset.subset_union_left
  have hY : Y'.card = Y.card := StarCounting.subtype_card U Y Finset.subset_union_right
  have hdis' : Disjoint X' Y' := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp hdis (Finset.mem_subtype.mp hv) (Finset.mem_subtype.mp hw)
  have hedge : ∀ e ∈ Q, ∃ z ∈ J.interedges X' Y',
      z.1.val = e.1 ∧ z.2.val = e.2 := by
    intro e he
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hQ he)
    let x : U := ⟨e.1, Finset.mem_union_left Y hx⟩
    let y : U := ⟨e.2, Finset.mem_union_right X hy⟩
    obtain ⟨r, hr, ha⟩ := hlink e he
    refine ⟨(x,y), ?_, rfl, rfl⟩
    rw [SimpleGraph.mem_interedges_iff]
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_subtype.mpr hx
    · exact Finset.mem_subtype.mpr hy
    · refine ⟨?_, e.1, r, hfix e.1 x.property, hr, ha⟩
      intro hh
      have heq : e.1 = e.2 := congrArg Subtype.val hh
      exact Finset.disjoint_left.mp hdis hx (heq.symm ▸ hy)
  let liftPair : Q → J.interedges X' Y' := fun e =>
    ⟨(hedge e.val e.property).choose, (hedge e.val e.property).choose_spec.1⟩
  have hinj : Function.Injective liftPair := by
    intro e d hh
    have he := (hedge e.val e.property).choose_spec.2
    have hd := (hedge d.val d.property).choose_spec.2
    have hz := congrArg Subtype.val hh
    apply Subtype.ext
    apply Prod.ext
    · exact he.1.symm.trans ((congrArg (fun z => z.1.val) hz).trans hd.1)
    · exact he.2.symm.trans ((congrArg (fun z => z.2.val) hz).trans hd.2)
  have hlo : Q.card ≤ (J.interedges X' Y').card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective liftPair hinj
  have hup := Incidence.card_interedges_le J X' Y'
  have hempty : J.inducedEdgeCount ∅ = 0 := by
    have hz := InducedCounting.sum_inducedDegree_eq_two_mul J (∅ : Finset U)
    simp only [Finset.sum_empty] at hz
    omega
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdis', hempty, add_zero] at hup
  have hm : SimpleGraph.IsMinor J G :=
    ⟨(StarMap.model G κ U hfix hstar).toMinorModel⟩
  have hd := MinorDensity.minor_induced_bound G J hden hm (X' ∪ Y')
  rw [Finset.card_union_of_disjoint hdis', hX, hY] at hd
  have hc : (Q.card : ℝ) ≤ J.inducedEdgeCount (X' ∪ Y') := by exact_mod_cast hlo.trans hup
  push_cast at hd
  exact hc.trans hd

/-- The direct short-list pair bound, with the physical minor-density parameter. -/
theorem card_pairs_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (Λ : V → Finset V) (f : ℕ) (hf : 1 ≤ f)
    (hrank : ∀ r, (Λ r).card ≤ f)
    (hlocal : ∀ r v, v ∈ Λ r → v = r ∨ G.Adj v r)
    {a : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (X Y : Finset V) (hdis : Disjoint X Y) :
    ((pairs Λ X Y).card : ℝ) ≤ (f : ℝ) * (a + f) * (X.card + Y.card) := by
  let U := X ∪ Y
  let P := pairs Λ X Y
  let I := P.filter (fun e => origin Λ e ∈ U)
  let E := P.filter (fun e => origin Λ e ∉ U)
  let Q := E.filter (fun e => e.2 = majority Λ X Y (origin Λ e))
  have hsplit : I.card + E.card = P.card := Finset.card_filter_add_card_filter_not _
  have hinside : I.card ≤ (f*f) * U.card := by
    apply Finset.card_le_mul_card_image_of_maps_to
      (fun e he => (Finset.mem_filter.mp he).2) (f*f)
    intro r hr
    have hs : I.filter (fun e => origin Λ e = r) ⊆ Λ r ×ˢ Λ r := by
      intro e he
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp he
      exact fiber_subset Λ X Y r (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, heq⟩)
    have hc := Finset.card_le_card hs
    rw [Finset.card_product] at hc
    exact hc.trans (Nat.mul_le_mul (hrank r) (hrank r))
  have houtside : E.card ≤ f * Q.card := by
    have hE := Finset.card_eq_sum_card_fiberwise
      (s := E) (t := Finset.univ) (f := origin Λ) (fun _ _ => Finset.mem_univ _)
    have hQsum := Finset.card_eq_sum_card_fiberwise
      (s := Q) (t := Finset.univ) (f := origin Λ) (fun _ _ => Finset.mem_univ _)
    rw [hE, hQsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : r ∈ U
    · have hz : E.filter (fun e => origin Λ e = r) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨heE, heq⟩ := Finset.mem_filter.mp he
        have hout := (Finset.mem_filter.mp heE).2
        exact hout (heq.symm ▸ hr)
      simp only [hz, Finset.card_empty, Nat.zero_le]
    · have heq : E.filter (fun e => origin Λ e = r) = fiber Λ X Y r := by
        ext e
        simp only [E, P, fiber, Finset.mem_filter]
        constructor
        · exact fun h => ⟨h.1.1,h.2⟩
        · exact fun h => ⟨⟨h.1, fun hh => hr (h.2 ▸ hh)⟩,h.2⟩
      have hqq : Q.filter (fun e => origin Λ e = r) =
          (fiber Λ X Y r).filter (fun e => e.2 = majority Λ X Y r) := by
        ext e
        simp only [Q, E, P, fiber, Finset.mem_filter]
        constructor
        · rintro ⟨⟨⟨hp, _⟩, hm⟩, ho⟩
          exact ⟨⟨hp,ho⟩, by simpa only [ho] using hm⟩
        · rintro ⟨⟨hp,ho⟩, hm⟩
          exact ⟨⟨⟨hp, fun hh => hr (ho ▸ hh)⟩, by simpa only [ho] using hm⟩,ho⟩
      rw [heq, hqq]
      exact fiber_card_le Λ X Y f hrank r
  let κ : V → V := fun r =>
    if r ∉ U ∧ (fiber Λ X Y r).Nonempty then majority Λ X Y r else r
  have hfix : ∀ v ∈ U, κ v = v := by
    intro v hv
    have hn : ¬ (v ∉ U ∧ (fiber Λ X Y v).Nonempty) := fun h => h.1 hv
    simp only [κ, if_neg hn]
  have hstar : ∀ v, κ v = v ∨ G.Adj (κ v) v := by
    intro r
    by_cases hr : r ∉ U ∧ (fiber Λ X Y r).Nonempty
    · have hy := majority_mem Λ X Y r hr.2
      have hne : majority Λ X Y r ≠ r := by
        intro he
        exact hr.1 (Finset.mem_union_right X (he ▸ hy.1))
      have hadj := (hlocal r _ hy.2).resolve_left hne
      exact Or.inr (by simpa only [κ, if_pos hr] using hadj)
    · exact Or.inl (by simp only [κ, if_neg hr])
  have hQlocal : Q ⊆ X ×ˢ Y := by
    intro e he
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    exact Finset.mem_product.mpr ⟨((mem_pairs Λ X Y e).mp hp).1,
      ((mem_pairs Λ X Y e).mp hp).2.1⟩
  have hlink : ∀ e ∈ Q, ∃ r, κ r = e.2 ∧ G.Adj e.1 r := by
    intro e he
    obtain ⟨heE, hmajor⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, ho⟩ := Finset.mem_filter.mp heE
    have hfib : (fiber Λ X Y (origin Λ e)).Nonempty :=
      ⟨e, Finset.mem_filter.mpr ⟨hp,rfl⟩⟩
    refine ⟨origin Λ e, ?_, ?_⟩
    · have hr : origin Λ e ∉ U ∧ (fiber Λ X Y (origin Λ e)).Nonempty := ⟨ho,hfib⟩
      simp only [κ, if_pos hr]
      exact hmajor.symm
    · have hh := (origin_spec Λ X Y hp).1
      apply (hlocal (origin Λ e) e.1 hh).resolve_left
      intro heq
      exact ho (heq ▸ Finset.mem_union_left Y ((mem_pairs Λ X Y e).mp hp).1)
  have hminor := cross_pairs_le G X Y hdis Q hQlocal κ hfix hstar hlink hden
  have hUc : U.card = X.card + Y.card := Finset.card_union_of_disjoint hdis
  have hi : (I.card : ℝ) ≤ (f : ℝ)^2 * (X.card + Y.card) := by
    rw [hUc] at hinside
    have hh : (I.card : ℝ) ≤ ((f*f : ℕ) : ℝ) * ((X.card + Y.card : ℕ) : ℝ) := by
      exact_mod_cast hinside
    simpa only [Nat.cast_mul, Nat.cast_add, pow_two] using hh
  have he : (E.card : ℝ) ≤ (f : ℝ) * Q.card := by exact_mod_cast houtside
  have hs : (I.card : ℝ) + E.card = P.card := by exact_mod_cast hsplit
  have hm := mul_le_mul_of_nonneg_left hminor (Nat.cast_nonneg f)
  change (P.card : ℝ) ≤ _
  nlinarith

#print axioms card_pairs_le
#print axioms cross_pairs_le
#print axioms exists_large_fiber

end Paper.DirectListPairs
