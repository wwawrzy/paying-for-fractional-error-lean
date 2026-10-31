import Paper.Owners.Construction.OwnerInteraction

/-! Labels that must be lifted at a physical separator vertex: all support
labels at light vertices, and just the own label at heavy owned vertices. -/
namespace Paper.OwnerRouteLabels
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyRepair
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def labels (D R : Finset V) (L : ℕ) (v : V) : Finset V :=
  if v ∈ heavy G D R L then if v ∈ R ∪ D then {owner G D v} else ∅ else support G D R v

theorem card_bound (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (v : V) : (labels G D R L v).card ≤ L := by
  by_cases hv : v ∈ heavy G D R L
  · by_cases ho : v ∈ R ∪ D <;> simp [labels, hv, ho, hL]
  · have hn : ¬ L < (support G D R v).card := fun hh => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    simpa only [labels, if_neg hv] using (show (support G D R v).card ≤ L by omega)

theorem owner_label (D R : Finset V) (L : ℕ) {v : V} (hv : v ∈ R ∪ D) :
    owner G D v ∈ labels G D R L v := by
  by_cases hp : v ∈ heavy G D R L
  · simp [labels, hp, hv]
  · simpa only [labels, if_neg hp] using OwnerSupport.self_label G D R hv

theorem root_label (D R : Finset V) (L : ℕ) {d : V} (hd : d ∈ D) : d ∈ labels G D R L d := by
  have hh := owner_label G D R L (Finset.mem_union_right R hd)
  simpa only [OwnerSupport.owner_center G D hd] using hh

theorem light_label (D R : Finset V) (L : ℕ) {v d : V} (hv : v ∉ heavy G D R L)
    (hd : d ∈ support G D R v) : d ∈ labels G D R L v := by simpa only [labels, if_neg hv] using hd

noncomputable def indexed {A : Type*} [Fintype A] (D R : Finset V) (L : ℕ) (e : A → V) (v : V) : Finset A :=
  Finset.univ.filter (fun a => e a ∈ labels G D R L v)

theorem mem_indexed {A : Type*} [Fintype A] (D R : Finset V) (L : ℕ) (e : A → V) (v : V) (a : A) :
    a ∈ indexed G D R L e v ↔ e a ∈ labels G D R L v := by simp only [indexed, Finset.mem_filter, Finset.mem_univ, true_and]

theorem indexed_bound {A : Type*} [Fintype A] (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (e : A → V) (hinj : Function.Injective e) (v : V) : (indexed G D R L e v).card ≤ L := by
  have hc := Finset.card_le_card_of_injOn e (s := indexed G D R L e v) (t := labels G D R L v)
    (fun a ha => (mem_indexed G D R L e v a).mp ha) (fun _ _ _ _ h => hinj h)
  exact hc.trans (card_bound G D R L hL v)
end Paper.OwnerRouteLabels
