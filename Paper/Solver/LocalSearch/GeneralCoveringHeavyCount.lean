import Paper.Solver.LocalSearch.GeneralCoveringHeavyMinor

/-! Count the actual admissible heavy set from its physical star minor.
Optional labels distinguish neighbors. Only a center's own label is erased;
heavy noncenters contribute one extra degree charge. No cover, minor or
heavy-cardinality oracle is assumed, and no runtime is changed. -/
namespace Paper.GeneralCoveringHeavyCount
open SevenFoundation GeneralCoveringHeavyMinor
open GeneralCoveringOwnerSupport (support heavy)
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance minorAdj (C : V → Finset V) (D R P : Finset V) :
    DecidableRel (graph G C D R P).Adj := fun _ _ => Classical.propDecidable _

theorem labels_le_degree (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {v : V} (hv : v ∈ P)
    (F : Finset V) (hF : F ⊆ support G C D R v)
    (hneq : ∀ d ∈ F, v ∈ D → d ≠ v) :
    F.card ≤ (graph G C D R P).degree ⟨v, Finset.mem_union_right D hv⟩ := by
  let K := graph G C D R P
  let r : ↥(D ∪ P) := ⟨v, Finset.mem_union_right D hv⟩
  have hw : ∀ d : F, ∃ y : ↥(D ∪ P), K.Adj r y ∧
      GeneralCoveringOwners.owner C D R y.val = some d.val :=
    fun d => support_neighbor G C D R P hlocal hv (hF d.property) (hneq d.val d.property)
  let f := fun d : F => (hw d).choose
  have hf : ∀ d : F, K.Adj r (f d) ∧
      GeneralCoveringOwners.owner C D R (f d).val = some d.val := fun d => (hw d).choose_spec
  have hinj : Function.Injective f := by
    intro d e he
    apply Subtype.ext
    apply Option.some.inj
    exact (hf d).2.symm.trans
      ((congrArg (fun y : ↥(D ∪ P) => GeneralCoveringOwners.owner C D R y.val) he).trans (hf e).2)
  have hs : Finset.univ.image f ⊆ K.neighborFinset r := by
    intro y hy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
    exact (K.mem_neighborFinset r (f d)).mpr (hf d).1
  have hc := Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe,
    SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem support_le_degree (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {v : V} (hv : v ∈ P) (hvD : v ∉ D) :
    (support G C D R v).card ≤ (graph G C D R P).degree ⟨v, Finset.mem_union_right D hv⟩ :=
  labels_le_degree G C D R P hlocal hv _ (fun _ h => h) (fun _ _ h => False.elim (hvD h))

theorem support_erase_le_degree (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {v : V} (hv : v ∈ P) :
    ((support G C D R v).erase v).card ≤
      (graph G C D R P).degree ⟨v, Finset.mem_union_right D hv⟩ :=
  labels_le_degree G C D R P hlocal hv _ (Finset.erase_subset ..)
    (fun _ hd _ => (Finset.mem_erase.mp hd).1)

theorem heavy_admissible (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    heavy G C D R L ⊆ CoveringSupport.admissible C R := Finset.filter_subset _ _

theorem degree_lower (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {v : V} (hv : v ∈ heavy G C D R L) :
    L + (if v ∈ D then 0 else 1) ≤
      (graph G C D R (heavy G C D R L)).degree ⟨v, Finset.mem_union_right D hv⟩ := by
  have hm := (Finset.mem_filter.mp hv).2
  by_cases hvD : v ∈ D
  · rw [if_pos hvD, add_zero]
    have he := support_erase_le_degree G C D R (heavy G C D R L) hlocal hv
    have hc := Finset.card_erase_add_one (GeneralCoveringOwnerSupport.center_in_support G C D R hvD)
    omega
  · rw [if_neg hvD]
    have he := support_le_degree G C D R (heavy G C D R L) hlocal hv hvD
    omega

def marked (D P : Finset V) : Finset ↥(D ∪ P) := P.subtype (fun v => v ∈ D ∪ P)

theorem marked_card (D P : Finset V) : (marked D P).card = P.card := by
  rw [marked, Finset.card_subtype, Finset.filter_true_of_mem Finset.subset_union_right]

theorem marked_outside_card (D P : Finset V) :
    ((marked D P).filter (fun v => v.val ∉ D)).card = (P \ D).card := by
  have he : (marked D P).filter (fun v => v.val ∉ D) =
      (P \ D).subtype (fun v => v ∈ D ∪ P) := by
    ext v
    simp only [marked, Finset.mem_filter, Finset.mem_subtype, Finset.mem_sdiff]
  rw [he, Finset.card_subtype,
    Finset.filter_true_of_mem (Finset.sdiff_subset.trans Finset.subset_union_right)]

theorem retained_card (D P : Finset V) : Fintype.card ↥(D ∪ P) = D.card + (P \ D).card := by
  rw [Fintype.card_coe]
  have hu := Finset.card_union_add_card_inter D P
  have hs := Finset.card_sdiff_add_card_inter P D
  rw [Finset.inter_comm P D] at hs
  omega

theorem charge_sum (D P : Finset V) (L : ℕ) :
    (∑ v ∈ marked D P, (L + if v.val ∈ D then 0 else 1)) = L * P.card + (P \ D).card := by
  rw [Finset.sum_add_distrib]
  have ht : (∑ v ∈ marked D P, if v.val ∈ D then 0 else 1) =
      ((marked D P).filter (fun v => v.val ∉ D)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hD : v.val ∈ D <;> simp [hD]
  rw [ht, marked_outside_card]
  simp [marked_card, mul_comm]

theorem incidence_lower (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    L * (heavy G C D R L).card + (heavy G C D R L \ D).card ≤
      ((graph G C D R (heavy G C D R L)).interedges (marked D (heavy G C D R L)) Finset.univ).card := by
  let P := heavy G C D R L
  let K := graph G C D R P
  change L * P.card + (P \ D).card ≤ (K.interedges (marked D P) Finset.univ).card
  rw [Incidence.card_interedges_eq_sum, ← charge_sum D P L]
  apply Finset.sum_le_sum
  intro v hv
  have hmem : v.val ∈ P := Finset.mem_subtype.mp hv
  have hh := degree_lower G C D R L hlocal hmem
  have hvEq : (⟨v.val, Finset.mem_union_right D hmem⟩ : ↥(D ∪ P)) = v := Subtype.ext rfl
  rw [hvEq] at hh
  simpa only [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] using hh

theorem incidence_upper (C : V → Finset V) (D R P : Finset V)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) :
    (((graph G C D R P).interedges (marked D P) Finset.univ).card : ℝ) ≤
      a * ((D.card : ℝ) + (P \ D).card) + a * P.card := by
  let K := graph G C D R P
  have hup := Incidence.card_interedges_le K (marked D P) Finset.univ
  rw [Finset.union_eq_right.mpr (Finset.subset_univ (marked D P)),
    Finset.inter_eq_left.mpr (Finset.subset_univ (marked D P))] at hup
  have hdensity := MinorDensity.minor_induced_bound G K hden ⟨(model G C D R P hlocal).toMinorModel⟩
  have hwhole := hdensity Finset.univ
  have hpart := hdensity (marked D P)
  rw [Finset.card_univ, retained_card D P] at hwhole
  rw [marked_card] at hpart
  have hr : ((K.interedges (marked D P) Finset.univ).card : ℝ) ≤
      (K.inducedEdgeCount Finset.univ : ℝ) + K.inducedEdgeCount (marked D P) := by exact_mod_cast hup
  push_cast at hwhole ⊢
  exact hr.trans (add_le_add hwhole hpart)

theorem charge (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ} (hden : MinorDensity.Bound G a) :
    (L : ℝ) * (heavy G C D R L).card + (heavy G C D R L \ D).card ≤
      a * ((D.card : ℝ) + (heavy G C D R L \ D).card) + a * (heavy G C D R L).card := by
  have hlo := incidence_lower G C D R L hlocal
  have hlo' : (L : ℝ) * (heavy G C D R L).card + (heavy G C D R L \ D).card ≤
      (((graph G C D R (heavy G C D R L)).interedges
        (marked D (heavy G C D R L)) Finset.univ).card : ℝ) := by exact_mod_cast hlo
  exact hlo'.trans (incidence_upper G C D R (heavy G C D R L) hlocal hden)

/-- The final scalar step is isolated from graph/cardinality elaboration. -/
theorem charge_to_count {p n d L : ℕ} {a : ℝ} (ha : 1 ≤ a) (hL : 4 * a ≤ (L : ℝ))
    (hn : n ≤ p)
    (hc : (L : ℝ) * (p : ℝ) + (n : ℝ) ≤
      a * ((d : ℝ) + (n : ℝ)) + a * (p : ℝ)) :
    (L : ℝ) * (p : ℝ) ≤ 2 * a * (d : ℝ) := by
  have hs : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast hn
  have hnonneg := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hs)
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have hl := mul_nonneg (sub_nonneg.mpr hL) hp
  nlinarith

theorem count (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ}
    (ha : 1 ≤ a) (hL : 4 * a ≤ (L : ℝ)) (hden : MinorDensity.Bound G a) :
    (L : ℝ) * (GeneralCoveringOwnerSupport.heavy G C D R L).card ≤ 2 * a * D.card :=
  charge_to_count (p := (heavy G C D R L).card) (n := (heavy G C D R L \ D).card)
    (d := D.card) ha hL (Finset.card_le_card Finset.sdiff_subset) (charge G C D R L hlocal hden)

theorem count_div (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) {a : ℝ}
    (ha : 1 ≤ a) (hL : 4 * a ≤ (L : ℝ)) (hden : MinorDensity.Bound G a) :
    ((GeneralCoveringOwnerSupport.heavy G C D R L).card : ℝ) ≤ 2 * a * D.card / L := by
  have hLp : (0 : ℝ) < L := by linarith
  apply (le_div_iff₀ hLp).mpr
  simpa only [mul_comm] using count G C D R L hlocal ha hL hden

end Paper.GeneralCoveringHeavyCount

#print axioms Paper.GeneralCoveringHeavyCount.labels_le_degree
#print axioms Paper.GeneralCoveringHeavyCount.support_le_degree
#print axioms Paper.GeneralCoveringHeavyCount.support_erase_le_degree
#print axioms Paper.GeneralCoveringHeavyCount.heavy_admissible
#print axioms Paper.GeneralCoveringHeavyCount.degree_lower
#print axioms Paper.GeneralCoveringHeavyCount.marked_card
#print axioms Paper.GeneralCoveringHeavyCount.marked_outside_card
#print axioms Paper.GeneralCoveringHeavyCount.retained_card
#print axioms Paper.GeneralCoveringHeavyCount.charge_sum
#print axioms Paper.GeneralCoveringHeavyCount.incidence_lower
#print axioms Paper.GeneralCoveringHeavyCount.incidence_upper
#print axioms Paper.GeneralCoveringHeavyCount.charge
#print axioms Paper.GeneralCoveringHeavyCount.charge_to_count
#print axioms Paper.GeneralCoveringHeavyCount.count
#print axioms Paper.GeneralCoveringHeavyCount.count_div
