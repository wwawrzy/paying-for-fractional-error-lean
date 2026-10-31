import Paper.Preliminaries.SevenFoundation

/-! Radius-two counting around degree defects, including the factor 1+d². -/
namespace Paper.RadiusTwo
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def shell (S : Finset V) : Finset V := covered G S \ S

def second (S : Finset V) : Finset V := covered G (shell G S) \ (S ∪ shell G S)

theorem shell_card_le (S : Finset V) :
    (shell G S).card ≤ ∑ s ∈ S, G.degree s := by
  have hs : shell G S ⊆ S.biUnion (fun v => G.neighborFinset v) := by
    intro v hv
    obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1
    have hne : v ≠ s := fun he => (Finset.mem_sdiff.mp hv).2 (he ▸ hs)
    exact Finset.mem_biUnion.mpr ⟨s, hs, (G.mem_neighborFinset s v).mpr
      (((mem_closed G v s).mp hvs).resolve_left hne)⟩
  exact (Finset.card_le_card hs).trans (by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      (Finset.card_biUnion_le : (S.biUnion (fun v => G.neighborFinset v)).card ≤
        ∑ s ∈ S, (G.neighborFinset s).card))

theorem shell_has_neighbor (S : Finset V) {v : V} (hv : v ∈ shell G S) :
    (G.neighborFinset v ∩ S).Nonempty := by
  obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1
  have hne : v ≠ s := fun he => (Finset.mem_sdiff.mp hv).2 (he ▸ hs)
  exact ⟨s, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v s).mpr
    ((((mem_closed G v s).mp hvs).resolve_left hne).symm), hs⟩⟩

theorem second_card_le (S : Finset V) (d : ℕ)
    (hregular : ∀ v ∉ S, G.degree v = d) :
    (second G S).card ≤ (d - 1) * (shell G S).card := by
  have hs : second G S ⊆ (shell G S).biUnion (fun v => G.neighborFinset v \ S) := by
    intro u hu
    obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hu).1
    have huS : u ∉ S := fun h => (Finset.mem_sdiff.mp hu).2 (Finset.mem_union_left _ h)
    have hne : u ≠ v := fun he => (Finset.mem_sdiff.mp hu).2
      (Finset.mem_union_right _ (he ▸ hv))
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v u).mpr
        (((mem_closed G u v).mp huv).resolve_left hne), huS⟩⟩
  calc
    (second G S).card ≤ ((shell G S).biUnion (fun v => G.neighborFinset v \ S)).card :=
      Finset.card_le_card hs
    _ ≤ ∑ v ∈ shell G S, (G.neighborFinset v \ S).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ shell G S, (d - 1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hcard := Finset.card_sdiff_add_card_inter (G.neighborFinset v) S
      have hpos := Finset.card_pos.mpr (shell_has_neighbor G S hv)
      rw [SimpleGraph.card_neighborFinset_eq_degree,
        hregular v (Finset.mem_sdiff.mp hv).2] at hcard
      omega
    _ = (d - 1) * (shell G S).card := by simp [mul_comm]

theorem card_le_of_degree_sum (S : Finset V) (d : ℕ) (hd : 1 ≤ d)
    (hregular : ∀ v ∉ S, G.degree v = d)
    (hcover : ∀ v, v ∈ covered G (covered G S))
    (hsum : ∑ s ∈ S, G.degree s ≤ d * S.card) :
    Fintype.card V ≤ (1 + d ^ 2) * S.card := by
  have hsub : (Finset.univ : Finset V) ⊆ S ∪ shell G S ∪ second G S := by
    intro v _
    by_cases hfirst : v ∈ S ∪ shell G S
    · exact Finset.mem_union_left _ hfirst
    apply Finset.mem_union_right
    refine Finset.mem_sdiff.mpr ⟨?_, hfirst⟩
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (hcover v)
    have huS : u ∉ S := by
      intro huS
      have hv : v ∈ covered G S := Finset.mem_biUnion.mpr ⟨u, huS, hvu⟩
      by_cases hvS : v ∈ S
      · exact hfirst (Finset.mem_union_left _ hvS)
      · exact hfirst (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hvS⟩))
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, huS⟩, hvu⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' := Finset.card_union_le S (shell G S)
  have h1 := (shell_card_le G S).trans hsum
  have h2 := second_card_le G S d hregular
  have hm := Nat.mul_le_mul_left d h1
  have heq : (shell G S).card + (d - 1) * (shell G S).card = d * (shell G S).card := by
    have he : 1 + (d - 1) = d := by omega
    calc
      _ = (1 + (d - 1)) * (shell G S).card := by ring
      _ = _ := by rw [he]
  simp only [Finset.card_univ] at hcard
  nlinarith [heq]

/-- Handshaking bounds the total degree of defects without a maximum-degree
assumption at the defects themselves. -/
theorem defect_degree_sum_le (S : Finset V) (d : ℕ)
    (hregular : ∀ v ∉ S, G.degree v = d)
    (hdensity : 2 * G.edgeFinset.card ≤ d * Fintype.card V) :
    ∑ s ∈ S, G.degree s ≤ d * S.card := by
  have hsplit := Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset V))
    (f := fun v => G.degree v) (Finset.subset_univ S)
  have hreg : ∑ v ∈ (Finset.univ : Finset V) \ S, G.degree v =
      d * ((Finset.univ : Finset V) \ S).card := by
    rw [Finset.sum_congr rfl (fun v hv => hregular v (Finset.mem_sdiff.mp hv).2)]
    simp [mul_comm]
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [hreg, G.sum_degrees_eq_twice_card_edges] at hsplit
  simp only [Finset.card_univ] at hc
  nlinarith

theorem card_le (S : Finset V) (d : ℕ) (hd : 1 ≤ d)
    (hregular : ∀ v ∉ S, G.degree v = d)
    (hcover : ∀ v, v ∈ covered G (covered G S))
    (hdensity : 2 * G.edgeFinset.card ≤ d * Fintype.card V) :
    Fintype.card V ≤ (1 + d ^ 2) * S.card :=
  card_le_of_degree_sum G S d hd hregular hcover
    (defect_degree_sum_le G S d hregular hdensity)
end Paper.RadiusTwo
