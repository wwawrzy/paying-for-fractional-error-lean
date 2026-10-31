import Paper.Preliminaries.CoreIncidence
import Paper.Preliminaries.StarCounting

/-! Actual simple star-minor counts for disjoint sunflower cores. -/
namespace Paper.CoreMinorCounting
attribute [local instance] Classical.propDecidable
open SevenFoundation CoreIncidence
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cross_degree_count (G : SimpleGraph V) [DecidableRel G.Adj] {a : ℝ}
    (hden : Incidence.InducedDensityBound G a) (R W : Finset V) (hdis : Disjoint R W)
    (q : ℕ) (hdeg : ∀ r ∈ R, q ≤ (W.filter (G.Adj r)).card) :
    ((q : ℝ) - a) * R.card ≤ a * W.card := by
  have hlow : q * R.card ≤ (G.interedges R W).card := by
    rw [Incidence.card_interedges_eq_sum]
    calc
      _ = ∑ _r ∈ R, q := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hdeg
  have hu := Incidence.card_interedges_le G R W
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdis] at hu
  have he : G.inducedEdgeCount ∅ = 0 := by
    have hz := InducedCounting.sum_inducedDegree_eq_two_mul G (∅ : Finset V)
    simp only [Finset.sum_empty] at hz
    omega
  rw [he, add_zero] at hu
  have hreal : (q : ℝ) * R.card ≤ G.inducedEdgeCount (R ∪ W) := by
    exact_mod_cast hlow.trans hu
  have hupper := hden (R ∪ W)
  rw [Finset.card_union_of_disjoint hdis] at hupper
  push_cast at hupper
  nlinarith

theorem core_degree (H F : Finset (Finset V)) (O X C : Finset V) (q : ℕ)
    (hq : 2 ≤ q) (hF : F ⊆ H) (hcard : F.card = q)
    (hsun : Sunflower.IsSunflower F C) (hCO : Disjoint C O)
    (hO : ∀ s ∈ H, (s ∩ O).Nonempty) (hXO : Disjoint X O)
    (r : {v // v ∈ centers H O ∪ markers H X}) (x : V) (hr : r.val = Sum.inl x) (hx : x ∈ C) :
    q ≤ (((centers H O).subtype (fun v => v ∈ centers H O ∪ markers H X)).filter
      ((StarMinor.graph (graph H) (centers H O) (markers H X)).Adj r)).card := by
  classical
  let W := centers H O
  let R := markers H X
  let K := StarMinor.graph (graph H) W R
  let A := W ∪ R
  let T := F.subtype (fun s => s ∈ H)
  let f := fun s : H => StarMinor.owner (graph H) W (Sum.inr s)
  let D := T.image f
  have hdis := markers_disjoint_covered H O X hXO
  have hDc : D.card = q := by
    rw [Finset.card_image_of_injOn]
    · exact (StarCounting.subtype_card H F hF).trans hcard
    · intro s hs t ht he
      exact owners_injective H F O C hO hF hsun hCO
        (Finset.mem_subtype.mp hs) (Finset.mem_subtype.mp ht) he
  have hDW : D ⊆ W := by
    intro w hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    exact StarMinor.owner_covered (graph H) W (set_covered H O hO s)
  have hDA : D ⊆ A := hDW.trans Finset.subset_union_left
  have hDcard : (D.subtype (fun v => v ∈ A)).card = q :=
    (StarCounting.subtype_card A D hDA).trans hDc
  have hsub : D.subtype (fun v => v ∈ A) ⊆
      (W.subtype (fun v => v ∈ A)).filter (K.Adj r) := by
    intro w hw
    have hwD := Finset.mem_subtype.mp hw
    obtain ⟨s, hs, hsown⟩ := Finset.mem_image.mp hwD
    refine Finset.mem_filter.mpr ⟨Finset.mem_subtype.mpr (hDW hwD), ?_⟩
    have hsF : s.val ∈ F := Finset.mem_subtype.mp hs
    have hxS : x ∈ s.val := CoreHierarchy.core_subset_member F C (by omega) hsun hsF hx
    have hown : f s = w.val := hsown
    refine ⟨?_, Sum.inl x, Sum.inr s, ?_, hown, hxS⟩
    · intro heq
      obtain ⟨d, hd, hsown', _⟩ := owner_set H O hO s
      have hlabel : Sum.inl x = Sum.inl d := hr.symm.trans
        ((congrArg Subtype.val heq).trans (hown.symm.trans hsown'))
      have he : x = d := Sum.inl.inj hlabel
      exact Finset.disjoint_left.mp hCO hx (he.symm ▸ hd)
    · rw [← hr]
      exact StarMinor.owner_retained (graph H) W R hdis r
  have hc := Finset.card_le_card hsub
  rw [hDcard] at hc
  exact hc
end Paper.CoreMinorCounting
