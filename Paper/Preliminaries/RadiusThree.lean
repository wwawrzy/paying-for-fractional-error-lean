import Paper.Preliminaries.RadiusTwo

namespace Paper.RadiusThree
open SevenFoundation RadiusTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shell_growth (S : Finset V) (d : ℕ)
    (hregular : ∀ v ∉ S, G.degree v = d) :
    (shell G (covered G S)).card ≤ (d-1)*(shell G S).card := by
  have hs : shell G (covered G S) ⊆ (shell G S).biUnion (fun v => G.neighborFinset v \ S) := by
    intro u hu
    obtain ⟨v,hv,huv⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hu).1
    have hn : u ∉ covered G S := (Finset.mem_sdiff.mp hu).2
    have hvS : v ∉ S := by
      intro hvS
      exact hn (Finset.mem_biUnion.mpr ⟨v,hvS,huv⟩)
    have hne : u ≠ v := fun he => hn (he ▸ hv)
    have ha := ((mem_closed G u v).mp huv).resolve_left hne
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_sdiff.mpr ⟨hv,hvS⟩,
      Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset v u).mpr ha,
        fun huS => hn (subset_covered G S huS)⟩⟩
  calc
    _ ≤ ((shell G S).biUnion (fun v => G.neighborFinset v \ S)).card := Finset.card_le_card hs
    _ ≤ ∑ v ∈ shell G S, (G.neighborFinset v \ S).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ shell G S, (d-1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hc := Finset.card_sdiff_add_card_inter (G.neighborFinset v) S
      have hp := Finset.card_pos.mpr (shell_has_neighbor G S hv)
      rw [SimpleGraph.card_neighborFinset_eq_degree,hregular v (Finset.mem_sdiff.mp hv).2] at hc
      omega
    _ = _ := by simp [mul_comm]

theorem covered_card (S : Finset V) : (covered G S).card = S.card+(shell G S).card := by
  have h := Finset.card_sdiff_add_card_eq_card (subset_covered G S)
  change (shell G S).card+S.card = _ at h
  omega

theorem card_le_of_degree_sum (S : Finset V) (d : ℕ)
    (hregular : ∀ v ∉ S, G.degree v = d)
    (hcover : ∀ v, v ∈ covered G (covered G (covered G S)))
    (hsum : ∑ v ∈ S, G.degree v ≤ d*S.card) :
    Fintype.card V ≤ (1+d+d*(d-1)+d*(d-1)^2)*S.card := by
  have h1 := (shell_card_le G S).trans hsum
  have h2 := shell_growth G S d hregular
  have hreg : ∀ v ∉ covered G S, G.degree v = d := fun v hv =>
    hregular v (fun hs => hv (subset_covered G S hs))
  have h3 := shell_growth G (covered G S) d hreg
  have h2' := h2.trans (Nat.mul_le_mul_left (d-1) h1)
  have h3' := h3.trans (Nat.mul_le_mul_left (d-1) h2')
  have htop : Fintype.card V ≤ (covered G (covered G (covered G S))).card := by
    simpa only [Finset.card_univ] using Finset.card_le_card (show Finset.univ ⊆ covered G (covered G (covered G S)) from fun v _ => hcover v)
  rw [covered_card G (covered G (covered G S)),covered_card G (covered G S),covered_card G S] at htop
  nlinarith only [htop,h1,h2',h3']

theorem card_le (S : Finset V) (d : ℕ)
    (hregular : ∀ v ∉ S, G.degree v = d)
    (hcover : ∀ v, v ∈ covered G (covered G (covered G S)))
    (hden : 2*G.edgeFinset.card ≤ d*Fintype.card V) :
    Fintype.card V ≤ (1+d+d*(d-1)+d*(d-1)^2)*S.card :=
  card_le_of_degree_sum G S d hregular hcover (defect_degree_sum_le G S d hregular hden)

end Paper.RadiusThree
