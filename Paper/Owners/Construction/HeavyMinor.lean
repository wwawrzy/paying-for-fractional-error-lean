import Paper.Owners.Construction.OwnerSupport
import Paper.Preliminaries.StarMap

/-! Keep marked vertices and all owners, contracting other owned vertices.
The retained heavy representatives continue to carry their original label. -/
namespace Paper.HeavyMinor
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def contract (D R P : Finset V) (u : V) : V :=
  if u ∈ P then u else if u ∈ R ∪ D then owner G D u else u

theorem fixed (D R P : Finset V) {u : V} (hu : u ∈ D ∪ P) : contract G D R P u = u := by
  by_cases hp : u ∈ P
  · simp [contract, hp]
  · have hd : u ∈ D := (Finset.mem_union.mp hu).resolve_right hp
    simp [contract, hp, Finset.mem_union_right R hd, owner_center G D hd]

theorem star (D R P : Finset V) (hcover : R ⊆ covered G D) (u : V) :
    contract G D R P u = u ∨ G.Adj (contract G D R P u) u := by
  by_cases hp : u ∈ P
  · exact Or.inl (by simp [contract, hp])
  by_cases ho : u ∈ R ∪ D
  · simpa only [contract, if_neg hp, if_pos ho] using (owner_owned G D R hcover ho).2
  · exact Or.inl (by simp [contract, hp, ho])

noncomputable def model (D R P : Finset V) (hcover : R ⊆ covered G D) :
    DepthOne.StarModel (StarMap.graph G (contract G D R P) (D ∪ P)) G :=
  StarMap.model G _ _ (fun _ hu => fixed G D R P hu) (star G D R P hcover)

theorem contract_owned (D R P : Finset V) (hcover : R ⊆ covered G D) {u : V} (hu : u ∈ R ∪ D) :
    contract G D R P u ∈ R ∪ D ∧ owner G D (contract G D R P u) = owner G D u := by
  by_cases hp : u ∈ P
  · simpa only [contract, if_pos hp] using (And.intro hu (rfl : owner G D u = owner G D u))
  · simp only [contract, if_neg hp, if_pos hu]
    exact ⟨Finset.mem_union_right R (owner_owned G D R hcover hu).1, label_idempotent G D R hcover hu⟩

theorem contract_retained (D R P : Finset V) (hcover : R ⊆ covered G D) {u : V} (hu : u ∈ R ∪ D) :
    contract G D R P u ∈ D ∪ P := by
  by_cases hp : u ∈ P
  · simpa only [contract, if_pos hp] using Finset.mem_union_right D hp
  · simpa only [contract, if_neg hp, if_pos hu] using
      Finset.mem_union_left P (owner_owned G D R hcover hu).1

theorem support_neighbor (D R P : Finset V) (hcover : R ⊆ covered G D) {v d : V}
    (hv : v ∈ P) (hd : d ∈ support G D R v) (hneq : v ∈ D → d ≠ v) :
    ∃ y : ↥(D ∪ P), (StarMap.graph G (contract G D R P) (D ∪ P)).Adj
      ⟨v, Finset.mem_union_right D hv⟩ y ∧ owner G D y.val = d := by
  classical
  have hfixv := fixed G D R P (Finset.mem_union_right D hv)
  by_cases hself : v ∈ R ∪ D ∧ d = owner G D v
  · have hvD : v ∉ D := by
      intro hvD
      exact hneq hvD (hself.2.trans (owner_center G D hvD))
    have ho := owner_owned G D R hcover hself.1
    have hne : owner G D v ≠ v := fun he => hvD (he ▸ ho.1)
    have ha : G.Adj v (owner G D v) := (ho.2.resolve_left hne).symm
    refine ⟨⟨owner G D v, Finset.mem_union_left P ho.1⟩, ?_, ?_⟩
    · exact ⟨fun he => hne (congrArg Subtype.val he).symm, v, owner G D v,
        hfixv, fixed G D R P (Finset.mem_union_left P ho.1), ha⟩
    · exact (owner_center G D ho.1).trans hself.2.symm
  · obtain ⟨u, hu, hud⟩ := Finset.mem_image.mp hd
    have hu' := Finset.mem_inter.mp hu
    let y := contract G D R P u
    have hy := contract_retained G D R P hcover hu'.2
    have hown := contract_owned G D R P hcover hu'.2
    have hylab : owner G D y = d := hown.2.trans hud
    have hyne : y ≠ v := by
      intro he
      exact hself ⟨he ▸ hown.1, (he ▸ hylab).symm⟩
    have huv : G.Adj v u := by
      rcases (mem_closed G u v).mp hu'.1 with he | ha
      · exact False.elim (hself ⟨he ▸ hu'.2, (he ▸ hud).symm⟩)
      · exact ha
    refine ⟨⟨y, hy⟩, ?_, hylab⟩
    exact ⟨fun he => hyne (congrArg Subtype.val he).symm, v, u, hfixv, rfl, huv⟩
end Paper.HeavyMinor
