import Paper.Endpoints.Rounding.CurrentCountBound
namespace Paper.SurfaceRounding
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem defect_degree_sum_le (S : Finset V) (d : ℕ) (η : ℝ)
    (hregular : ∀ v ∉ S, G.degree v=d)
    (hdensity : 2*(G.edgeFinset.card:ℝ) ≤ d*Fintype.card V+η) :
    (∑ s ∈ S, (G.degree s:ℝ)) ≤ d*S.card+η := by
  classical
  have hsplit := Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset V))
    (f := fun v => G.degree v) (Finset.subset_univ S)
  have hreg : ∑ v ∈ (Finset.univ : Finset V) \ S, G.degree v =
      d*((Finset.univ : Finset V) \ S).card := by
    rw [Finset.sum_congr rfl (fun v hv => hregular v (Finset.mem_sdiff.mp hv).2)]
    simp [mul_comm]
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [hreg,G.sum_degrees_eq_twice_card_edges] at hsplit
  simp only [Finset.card_univ] at hc
  have hsR : (d:ℝ)*((Finset.univ \ S).card:ℝ)+(∑ s ∈ S, (G.degree s:ℝ))=2*G.edgeFinset.card := by exact_mod_cast hsplit
  have hcR : (((Finset.univ \ S).card):ℝ)+S.card=Fintype.card V := by exact_mod_cast hc
  nlinarith only [hsR,hcR,hdensity]

theorem regular_shell_count (d : ℕ) (η : ℝ) (T Q B : Finset V)
    (hBQ : B ⊆ Q) (hQT : Disjoint Q T)
    (hregular : ∀ v ∉ T ∪ B, G.degree v=d)
    (hlarge : ∀ v ∈ B, d+1 ≤ G.degree v)
    (htouch : ∀ v ∈ Q \ B, ∃ s ∈ T ∪ B, G.Adj v s)
    (hdensity : 2*(G.edgeFinset.card:ℝ) ≤ d*Fintype.card V+η) :
    (B.card:ℝ) ≤ d*T.card+η ∧ (Q.card:ℝ) ≤ d*(d+2)*T.card+(d+2)*η := by
  classical
  let S := T ∪ B
  have hTB : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvB
    exact Finset.disjoint_left.mp hQT (hBQ hvB) hvT
  have hScard : (S.card:ℝ)=T.card+B.card := by exact_mod_cast Finset.card_union_of_disjoint hTB
  have hsum := defect_degree_sum_le G S d η hregular hdensity
  have hlower : (d+1)*B.card ≤ ∑ s ∈ S, G.degree s := by
    calc
      _ = ∑ _v ∈ B, (d+1) := by simp [mul_comm]
      _ ≤ ∑ v ∈ B, G.degree v := Finset.sum_le_sum hlarge
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun _ _ _ => Nat.zero_le _)
  have hlowerR : ((d:ℝ)+1)*B.card ≤ ∑ s ∈ S, (G.degree s:ℝ) := by exact_mod_cast hlower
  have hB : (B.card:ℝ) ≤ d*T.card+η := by nlinarith only [hlowerR,hsum,hScard]
  have hsub : Q \ B ⊆ RadiusTwo.shell G S := by
    intro v hv
    obtain ⟨s,hs,hvs⟩ := htouch v hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨s,hs,(mem_closed G v s).mpr (Or.inr hvs.symm)⟩,?_⟩
    intro hvS
    rcases Finset.mem_union.mp hvS with hvT | hvB
    · exact Finset.disjoint_left.mp hQT (Finset.mem_sdiff.mp hv).1 hvT
    · exact (Finset.mem_sdiff.mp hv).2 hvB
  have hrest : (Q \ B).card ≤ ∑ s ∈ S, G.degree s :=
    (Finset.card_le_card hsub).trans (RadiusTwo.shell_card_le G S)
  have hrestR : ((Q \ B).card:ℝ) ≤ ∑ s ∈ S, (G.degree s:ℝ) := by exact_mod_cast hrest
  have hsplit : ((Q \ B).card:ℝ)+B.card=Q.card := by exact_mod_cast Finset.card_sdiff_add_card_eq_card hBQ
  refine ⟨hB,?_⟩
  nlinarith only [hsplit,hrestR,hsum,hScard,hB]
end Paper.SurfaceRounding
#print axioms Paper.SurfaceRounding.regular_shell_count
