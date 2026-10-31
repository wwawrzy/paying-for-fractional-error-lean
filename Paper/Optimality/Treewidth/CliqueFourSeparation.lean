import GraphTheory.Plane.WagnerSeparation
import GraphTheory.Plane.WagnerSeparatorSides

/-! Graph-theoretic separator filling. The filled side is a proved minor,
and every vertex outside its separator keeps its actual original degree. -/
namespace Paper.CliqueFourSeparation

open SimpleGraph PlaneTopology.WagnerSeparation
  PlaneTopology.WagnerSeparatorSides PlaneTopology.WagnerSeparatorPaths
  PlaneTopology.WagnerSeparatorMinor

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def fill (A : Set V) (S : Finset V) : SimpleGraph A where
  Adj a b := G.Adj a.val b.val ∨ (a ≠ b ∧ a.val ∈ S ∧ b.val ∈ S)
  symm _ _ h := h.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr ⟨h.1.symm, h.2.2, h.2.1⟩)
  loopless := ⟨fun a h => h.elim (G.loopless.irrefl a.val) (fun h => h.1 rfl)⟩

noncomputable instance fill_decidable (A : Set V) (S : Finset V) :
    DecidableRel (fill G A S).Adj := by
  classical
  exact fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def flip {S : Finset V} (s : Separation G S) : Separation G S where
  left := s.right
  right := s.left
  cover := by rw [Set.union_comm, s.cover]
  overlap := by rw [Set.inter_comm, s.overlap]
  left_private := s.right_private
  right_private := s.left_private
  no_cross a ha b hb hab := s.no_cross b hb a ha hab.symm

/-- A clique cannot meet both private sides of a separation. -/
theorem choose_side {S : Finset V} (s : Separation G S) (K : Finset V)
    (hK : G.IsClique (K : Set V)) :
    ∃ q : Separation G S, ∀ x ∈ q.left \ q.right, x ∉ K := by
  classical
  by_cases hx : ∃ x ∈ s.left \ s.right, x ∈ K
  · obtain ⟨x, hx, hxK⟩ := hx
    refine ⟨flip G s, ?_⟩
    intro y hy hyK
    exact s.no_cross x hx y hy (hK hxK hyK (fun he => hx.2 (he.symm ▸ hy.1)))
  · refine ⟨s, ?_⟩
    intro x hxS hxK
    exact hx ⟨x, hxS, hxK⟩

theorem fill_minor (S : Finset V) (hS : S.card ≤ 2)
    (hconn : G.IsKConnected S.card) (s : Separation G S) :
    (fill G s.left S).IsMinor G := by
  classical
  by_cases hsmall : S.card ≤ 1
  · have hsub : fill G s.left S ≤ G.induce s.left := by
      intro a b hab
      rcases hab with hab | ⟨hne, ha, hb⟩
      · exact hab
      · exact False.elim (hne (Subtype.ext ((Finset.card_le_one.mp hsmall) _ ha _ hb)))
    exact (IsMinor.of_subgraph hsub).trans (IsMinor.of_induce G _)
  · have htwo : S.card = 2 := by omega
    obtain ⟨u, v, huv, hSuv⟩ := Finset.card_eq_two.mp htwo
    have hinter : s.left ∩ s.right = {u, v} := by
      simpa only [hSuv, Finset.coe_insert, Finset.coe_singleton] using s.overlap
    have hu : u ∈ s.left ∩ s.right := by rw [hinter]; simp
    have hv : v ∈ s.left ∩ s.right := by rw [hinter]; simp
    let uA : s.left := ⟨u, hu.1⟩
    let vA : s.left := ⟨v, hv.1⟩
    have hne : uA ≠ vA := fun he => huv (congrArg Subtype.val he)
    have h2 : G.IsKConnected 2 := by simpa only [htwo] using hconn
    obtain ⟨C, hC⟩ := exists_outside_component_of_separation G s.left s.right u v
      s.cover hinter s.no_cross s.right_private
    obtain ⟨p, hp, hout⟩ := exists_outsidePath_of_two_connected_branch G h2 s.left uA vA hne
      (separatorComponentSet G u v C) hC (separatorComponentSet_connected G u v C)
      (separatorComponentSet_boundary G u v C)
    have hm := filledSide_minor_of_outsidePath G s.left uA vA hne p hp hout
    have hletters (w : V) (hw : w ∈ S) : w = u ∨ w = v := by
      simpa only [hSuv, Finset.mem_insert, Finset.mem_singleton] using hw
    have hsub : fill G s.left S ≤ (G.induce s.left) ⊔ edge uA vA := by
      intro a b hab
      rcases hab with hab | ⟨hneab, ha, hb⟩
      · exact Or.inl hab
      · have ha' : a = uA ∨ a = vA := by
          rcases hletters a.val ha with ha | ha
          · exact Or.inl (Subtype.ext ha)
          · exact Or.inr (Subtype.ext ha)
        have hb' : b = uA ∨ b = vA := by
          rcases hletters b.val hb with hb | hb
          · exact Or.inl (Subtype.ext hb)
          · exact Or.inr (Subtype.ext hb)
        have hor : (a = uA ∧ b = vA) ∨ (a = vA ∧ b = uA) := by
          rcases ha' with ha | ha
          · rcases hb' with hb | hb
            · exact (hneab (ha.trans hb.symm)).elim
            · exact Or.inl ⟨ha, hb⟩
          · rcases hb' with hb | hb
            · exact Or.inr ⟨ha, hb⟩
            · exact (hneab (ha.trans hb.symm)).elim
        exact Or.inr ((edge_adj uA vA a b).mpr ⟨hor, hneab⟩)
    exact (IsMinor.of_subgraph hsub).trans hm

noncomputable def boundary (A : Set V) (S : Finset V) : Finset A :=
  by classical exact Finset.univ.filter (fun a => a.val ∈ S)

theorem boundary_card (A : Set V) (S : Finset V) : (boundary A S).card ≤ S.card := by
  classical
  have hsub : (boundary A S).image Subtype.val ⊆ S := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp ha).2
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hc

theorem boundary_clique (A : Set V) (S : Finset V) :
    (fill G A S).IsClique (boundary A S : Set A) := by
  classical
  intro a ha b hb hab
  exact Or.inr ⟨hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩

theorem degree_preserved {S : Finset V} (s : Separation G S) [Fintype s.left] (v : s.left)
    (hv : v.val ∉ S) : (fill G s.left S).degree v = G.degree v.val := by
  classical
  have hvR : v.val ∉ s.right := fun h => hv (by
    change v.val ∈ (S : Set V)
    rw [← s.overlap]
    exact ⟨v.property, h⟩)
  have hall (w : V) (hadj : G.Adj v.val w) : w ∈ s.left := by
    by_contra hw
    have hu : w ∈ s.left ∪ s.right := by rw [s.cover]; exact Set.mem_univ _
    have hwR : w ∈ s.right := hu.resolve_left hw
    exact s.no_cross v.val ⟨v.property, hvR⟩ w ⟨hwR, hw⟩ hadj
  have he : ((fill G s.left S).neighborFinset v).image Subtype.val = G.neighborFinset v.val := by
    ext w
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      have hadj := ((fill G s.left S).mem_neighborFinset v z).mp hz
      exact (G.mem_neighborFinset _ _).mpr (hadj.resolve_right (fun h => hv h.2.1))
    · intro hw
      have hadj := (G.mem_neighborFinset _ _).mp hw
      exact Finset.mem_image.mpr ⟨⟨w, hall w hadj⟩,
        ((fill G s.left S).mem_neighborFinset _ _).mpr (Or.inl hadj), rfl⟩
  have hc := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

end Paper.CliqueFourSeparation

#print axioms Paper.CliqueFourSeparation.choose_side
#print axioms Paper.CliqueFourSeparation.fill_minor
#print axioms Paper.CliqueFourSeparation.degree_preserved
