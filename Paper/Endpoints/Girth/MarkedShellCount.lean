import Paper.Preliminaries.RadiusTwo

/-! # The marked degree-sum version of the regular-shell count -/

namespace Paper.MarkedShellCount

open SimpleGraph SevenFoundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Subtract the actual marked degree sum after applying handshaking.
All degrees outside S are the original fixed regular degree. -/
theorem marked_degree_sum_le (S A : Finset V) (d : ℕ) (κ : ℝ)
    (hAS : A ⊆ S) (hregular : ∀ v ∉ S, G.degree v = d)
    (hdensity : (2 : ℝ) * G.edgeFinset.card ≤
      d * Fintype.card V + (1 + κ) * (∑ a ∈ A, G.degree a)) :
    ((∑ v ∈ S \ A, G.degree v) : ℝ) ≤
      d * S.card + κ * (∑ a ∈ A, G.degree a) := by
  have hs := Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset V))
    (f := fun v => G.degree v) (Finset.subset_univ S)
  have ha := Finset.sum_sdiff (s₁ := A) (s₂ := S)
    (f := fun v => G.degree v) hAS
  have hreg : ∑ v ∈ (Finset.univ : Finset V) \ S, G.degree v =
      d * ((Finset.univ : Finset V) \ S).card := by
    rw [Finset.sum_congr rfl (fun v hv => hregular v (Finset.mem_sdiff.mp hv).2)]
    simp [mul_comm]
  rw [hreg, G.sum_degrees_eq_twice_card_edges] at hs
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ] at hc
  have hnat : (∑ v ∈ S \ A, G.degree v) + (∑ a ∈ A, G.degree a) +
      d * ((Finset.univ : Finset V) \ S).card = 2 * G.edgeFinset.card := by
    calc
      _ = (∑ v ∈ S, G.degree v) + d * ((Finset.univ : Finset V) \ S).card :=
        congrArg (fun n => n + d * ((Finset.univ : Finset V) \ S).card) ha
      _ = _ := by simpa only [Nat.add_comm] using hs
  have hreal : ((∑ v ∈ S \ A, G.degree v) : ℝ) + (∑ a ∈ A, G.degree a) +
      d * ((Finset.univ : Finset V) \ S).card = 2 * G.edgeFinset.card := by
    exact_mod_cast hnat
  have hcR : (((Finset.univ : Finset V) \ S).card : ℝ) + S.card = Fintype.card V := by
    exact_mod_cast hc
  have hcD := congrArg (fun z : ℝ => (d : ℝ) * z) hcR
  push_cast at hdensity hreal hcD ⊢
  nlinarith only [hdensity, hreal, hcD]

/-- The only counted vertices are Q. Their regular members touch T∪B,
which avoids A; the marked degree is removed before the shell estimate. -/
theorem regular_shell_count (A T Q B : Finset V) (d : ℕ) (κ : ℝ)
    (hAT : Disjoint A T) (hBQ : B ⊆ Q) (hQAT : Disjoint Q (A ∪ T))
    (hregular : ∀ v ∉ (A ∪ T) ∪ B, G.degree v = d)
    (hlarge : ∀ v ∈ B, d + 1 ≤ G.degree v)
    (htouch : ∀ v ∈ Q \ B, ∃ s ∈ T ∪ B, G.Adj v s)
    (hdensity : (2 : ℝ) * G.edgeFinset.card ≤
      d * Fintype.card V + (1 + κ) * (∑ a ∈ A, G.degree a)) :
    (B.card : ℝ) ≤ d * (A.card + T.card) + κ * (∑ a ∈ A, G.degree a) ∧
      (Q.card : ℝ) ≤ (d : ℝ) * (d + 2) * (A.card + T.card) +
        (d + 2) * κ * (∑ a ∈ A, G.degree a) := by
  let S := (A ∪ T) ∪ B
  have hAB : Disjoint A B := (hQAT.mono_left hBQ).symm.mono_left Finset.subset_union_left
  have hTB : Disjoint T B := (hQAT.mono_left hBQ).symm.mono_left Finset.subset_union_right
  have hScard : S.card = A.card + T.card + B.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAB, hTB⟩),
      Finset.card_union_of_disjoint hAT]
  have hAS : A ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hBsub : B ⊆ S \ A := by
    intro b hb
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hb,
      fun ha => Finset.disjoint_left.mp hAB ha hb⟩
  have hTsub : T ∪ B ⊆ S \ A := by
    intro s hs
    rcases Finset.mem_union.mp hs with ht | hb
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ht),
          fun ha => Finset.disjoint_left.mp hAT ha ht⟩
    · exact hBsub hb
  have hsum := marked_degree_sum_le G S A d κ hAS hregular hdensity
  rw [hScard] at hsum
  push_cast at hsum
  have hlowN : (d + 1) * B.card ≤ ∑ s ∈ S \ A, G.degree s := by
    calc
      _ = ∑ _b ∈ B, (d + 1) := by simp [mul_comm]
      _ ≤ ∑ b ∈ B, G.degree b := Finset.sum_le_sum hlarge
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun _ _ _ => Nat.zero_le _)
  have hlow : ((d : ℝ) + 1) * B.card ≤ ((∑ s ∈ S \ A, G.degree s) : ℝ) := by
    exact_mod_cast hlowN
  have hBcount : (B.card : ℝ) ≤ d * (A.card + T.card) +
      κ * (∑ a ∈ A, G.degree a) := by
    push_cast
    nlinarith only [hsum, hlow]
  have hsub : Q \ B ⊆ RadiusTwo.shell G (S \ A) := by
    intro v hv
    obtain ⟨s, hs, hvs⟩ := htouch v hv
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_biUnion.mpr
        ⟨s, hTsub hs, (mem_closed G v s).mpr (Or.inr hvs.symm)⟩
    · intro hvS
      rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hvS).1 with hat | hb
      · exact Finset.disjoint_left.mp hQAT (Finset.mem_sdiff.mp hv).1 hat
      · exact (Finset.mem_sdiff.mp hv).2 hb
  have hrestN : (Q \ B).card ≤ ∑ s ∈ S \ A, G.degree s :=
    (Finset.card_le_card hsub).trans (RadiusTwo.shell_card_le G (S \ A))
  have hrest : ((Q \ B).card : ℝ) ≤ ((∑ s ∈ S \ A, G.degree s) : ℝ) := by
    exact_mod_cast hrestN
  have hsplit : ((Q \ B).card : ℝ) + B.card = Q.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hBQ
  have hm := mul_le_mul_of_nonneg_left hBcount (show (0 : ℝ) ≤ d + 1 by positivity)
  refine ⟨hBcount, ?_⟩
  push_cast at hm ⊢
  nlinarith only [hm, hrest, hsplit, hsum]

end Paper.MarkedShellCount

#print axioms Paper.MarkedShellCount.marked_degree_sum_le
#print axioms Paper.MarkedShellCount.regular_shell_count
