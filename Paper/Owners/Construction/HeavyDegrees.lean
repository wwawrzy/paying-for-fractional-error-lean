import Paper.Owners.Construction.HeavyMinor

/-! Different owner support labels give different actual minor neighbors,
including the own label of a retained nonowner. -/
namespace Paper.HeavyDegrees
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyMinor
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem labels_le_degree (D R P : Finset V) (hcover : R ⊆ covered G D) {v : V} (hv : v ∈ P)
    (F : Finset V) (hF : F ⊆ support G D R v) (hneq : ∀ d ∈ F, v ∈ D → d ≠ v) :
    F.card ≤ (StarMap.graph G (contract G D R P) (D ∪ P)).degree ⟨v, Finset.mem_union_right D hv⟩ := by
  classical
  let K := StarMap.graph G (contract G D R P) (D ∪ P)
  let r : ↥(D ∪ P) := ⟨v, Finset.mem_union_right D hv⟩
  have hw : ∀ d : F, ∃ y : ↥(D ∪ P), K.Adj r y ∧ owner G D y.val = d.val :=
    fun d => support_neighbor G D R P hcover hv (hF d.property) (hneq d.val d.property)
  let f := fun d : F => (hw d).choose
  have hf : ∀ d : F, K.Adj r (f d) ∧ owner G D (f d).val = d.val := fun d => (hw d).choose_spec
  have hinj : Function.Injective f := by
    intro d e he
    exact Subtype.ext ((hf d).2.symm.trans ((congrArg (fun y : ↥(D ∪ P) => owner G D y.val) he).trans (hf e).2))
  have hs : Finset.univ.image f ⊆ K.neighborFinset r := by
    intro y hy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
    exact (K.mem_neighborFinset r (f d)).mpr (hf d).1
  have hc := Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe,
    SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem support_le_degree (D R P : Finset V) (hcover : R ⊆ covered G D) {v : V}
    (hv : v ∈ P) (hvD : v ∉ D) : (support G D R v).card ≤
    (StarMap.graph G (contract G D R P) (D ∪ P)).degree ⟨v, Finset.mem_union_right D hv⟩ :=
  labels_le_degree G D R P hcover hv _ (fun _ h => h) (fun _ _ h => False.elim (hvD h))

theorem support_erase_le_degree (D R P : Finset V) (hcover : R ⊆ covered G D) {v : V}
    (hv : v ∈ P) : ((support G D R v).erase v).card ≤
    (StarMap.graph G (contract G D R P) (D ∪ P)).degree ⟨v, Finset.mem_union_right D hv⟩ :=
  labels_le_degree G D R P hcover hv _ (Finset.erase_subset ..)
    (fun _ hd _ => (Finset.mem_erase.mp hd).1)
end Paper.HeavyDegrees
