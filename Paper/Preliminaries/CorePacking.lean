import Paper.Preliminaries.CoreMinorCounting

/-! Density bounds the actual number of disjoint sunflower cores avoiding
an original hitting set. The minor is explicitly a radius-one star minor. -/
namespace Paper.CorePacking
attribute [local instance] Classical.propDecidable
open SevenFoundation CoreIncidence CoreHierarchy
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
theorem packing_bound (H P : Finset (Finset V)) (O : Finset V) (q : ℕ) (hq : 2 ≤ q)
    (hP : P ⊆ cores H q) (hpack : Sunflower.Packing P)
    (hPO : ∀ C ∈ P, Disjoint C O) (hO : ∀ s ∈ H, (s ∩ O).Nonempty)
    {a : ℝ} (hden : DepthOne.Bound (graph H) a) :
    ((q : ℝ) - a) * P.card ≤ a * O.card := by
  classical
  let point := fun C : P => ((mem_cores H q C.val).mp (hP C.property)).1.choose
  have hpoint : ∀ C : P, point C ∈ C.val := fun C =>
    ((mem_cores H q C.val).mp (hP C.property)).1.choose_spec
  have hinj : Function.Injective point := by
    intro C D he
    by_contra hn
    have hne : C.val ≠ D.val := fun hv => hn (Subtype.ext hv)
    have hd := hpack C.val C.property D.val D.property hne
    exact Finset.disjoint_left.mp hd (hpoint C) (he.symm ▸ hpoint D)
  let X := Finset.univ.image point
  have hXcard : X.card = P.card := by
    rw [Finset.card_image_of_injective _ hinj]
    exact Fintype.card_coe P
  have hXO : Disjoint X O := by
    apply Finset.disjoint_left.mpr
    intro x hx hxO
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.disjoint_left.mp (hPO C.val C.property) (hpoint C) hxO
  let W := centers H O
  let R := markers H X
  let A := W ∪ R
  let K := StarMinor.graph (graph H) W R
  let W' := W.subtype (fun v => v ∈ A)
  let R' := R.subtype (fun v => v ∈ A)
  have hR := markers_disjoint_covered H O X hXO
  have hdis : Disjoint R' W' := by
    apply Finset.disjoint_left.mpr
    intro r hr hw
    exact Finset.disjoint_left.mp hR (Finset.mem_subtype.mp hr)
      (subset_covered (graph H) W (Finset.mem_subtype.mp hw))
  have hdegrees : ∀ r ∈ R', q ≤ (W'.filter (K.Adj r)).card := by
    intro r hr
    have hrR := Finset.mem_subtype.mp hr
    obtain ⟨x, hx, hxlab⟩ := Finset.mem_image.mp hrR
    obtain ⟨C, _, hCx⟩ := Finset.mem_image.mp hx
    obtain ⟨_, F, hF, hqF, hsun⟩ := (mem_cores H q C.val).mp (hP C.property)
    have hxC : x ∈ C.val := hCx ▸ hpoint C
    exact CoreMinorCounting.core_degree H F O X C.val q hq hF hqF hsun
      (hPO C.val C.property) hO hXO r x hxlab.symm hxC
  have hdensity := DepthOne.induced_bound (graph H) K
    (DepthOne.ofStars (graph H) W R hR) hden
  have hcount := CoreMinorCounting.cross_degree_count K hdensity R' W' hdis q hdegrees
  have hRc : R'.card = P.card := by
    rw [StarCounting.subtype_card A R Finset.subset_union_right]
    change (X.image Sum.inl).card = P.card
    rw [Finset.card_image_of_injective _ Sum.inl_injective, hXcard]
  have hWc : W'.card = O.card := by
    rw [StarCounting.subtype_card A W Finset.subset_union_left]
    change (O.image Sum.inl).card = O.card
    exact Finset.card_image_of_injective _ Sum.inl_injective
  simpa only [hRc, hWc] using hcount
end Paper.CorePacking
