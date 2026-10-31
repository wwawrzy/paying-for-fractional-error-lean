import Paper.Owners.Construction.OwnerDensity
import Paper.Preliminaries.HighDegreeCut

/-! The second actual repair selects the physical high-degree owners.
Their count and the bounded degree of the remaining owner graph are proved. -/
namespace Paper.OwnerHighRepair
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def selected (D R : Finset V) (L Δ : ℕ) : Finset V :=
  (HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ).image Subtype.val

theorem selected_subset (D R : Finset V) (L Δ : ℕ) : selected G D R L Δ ⊆ D := by
  intro d hd
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hd
  exact v.property

theorem count (D R : Finset V) (L Δ : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    (Δ : ℝ) * (selected G D R L Δ).card ≤ 2 * (a * ((L + 1 : ℕ) : ℝ) ^ 4) * D.card := by
  classical
  let J := OwnerInteraction.graph G D R L
  have hh := OwnerGraphCount.count G D R L hL J (fun v : D => v.val) Subtype.val_injective
    (fun v => v.property) (fun _ _ h => OwnerInteraction.graph_le_augmented G D R L h) hden ha
  have hc := HighDegreeCut.count J Δ hh
  have hcard : (selected G D R L Δ).card = (HighDegreeCut.high J Δ).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  simpa only [hcard, Fintype.card_coe] using hc

theorem class_covered (D R : Finset V) (hcover : R ⊆ covered G D) (L Δ : ℕ) {r : V}
    (hr : r ∈ R) (hm : owner G D r ∈ selected G D R L Δ) : r ∈ covered G (selected G D R L Δ) := by
  have ho := (owner_owned G D R hcover (Finset.mem_union_left D hr)).2
  refine Finset.mem_biUnion.mpr ⟨owner G D r, hm, ?_⟩
  exact (mem_closed G r (owner G D r)).mpr (ho.elim (fun he => Or.inl he.symm) Or.inr)

theorem remaining_degree (D R : Finset V) (L Δ : ℕ)
    (v : {v // v ∉ HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ}) :
    (HighDegreeCut.pruned (OwnerInteraction.graph G D R L) Δ).degree v ≤ Δ :=
  HighDegreeCut.degree_bound _ Δ v
end Paper.OwnerHighRepair
