import Paper.Preliminaries.PartBoundaries
import Paper.Preliminaries.FiniteGoodMass

/-! Actual connected eligible subsets cover at least half of every current
region. This is derived from the proved small-cut partition. -/
namespace Paper.EligibleSets
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def family (S : Finset V) (k : ℕ) (ε : ℝ) : Finset (Finset V) :=
  S.powerset.filter (fun U => (G.induce (U : Set V)).Connected ∧ U.card ≤ k ∧
    (PartBoundaries.boundary G S U : ℝ) ≤ 4 * ε * U.card)

noncomputable def covered (S : Finset V) (k : ℕ) (ε : ℝ) : Finset V :=
  (family G S k ε).biUnion id

theorem mem_family (S U : Finset V) (k : ℕ) (ε : ℝ) :
    U ∈ family G S k ε ↔ U ⊆ S ∧ (G.induce (U : Set V)).Connected ∧ U.card ≤ k ∧
      (PartBoundaries.boundary G S U : ℝ) ≤ 4 * ε * U.card := by
  simp only [family, Finset.mem_filter, Finset.mem_powerset, and_assoc]

theorem covered_subset (S : Finset V) (k : ℕ) (ε : ℝ) : covered G S k ε ⊆ S := by
  intro v hv
  obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
  exact ((mem_family G S U k ε).mp hU).1 hv

theorem half_covered {C ε : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k) (hε : 0 < ε)
    (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ ε) (S : Finset V) :
    (S.card : ℝ) / 2 ≤ (covered G S k ε).card := by
  obtain ⟨D, _, P, he, hcut⟩ := SmallCutPartition.prescribed G hC hprofile Δ hdeg k hk hparam S
  let p := SmallParts.label G S D
  have htotal := PartBoundaries.total G S k P p he
    (SmallParts.label_self G S D) (SmallParts.label_consistent G S D)
  have hcards := SmallParts.sum_card G P
  have hbudget : (∑ U ∈ P.parts, (PartBoundaries.boundary G S U : ℝ)) ≤
      2 * ε * ∑ U ∈ P.parts, (U.card : ℝ) := by
    have ht : (∑ U ∈ P.parts, (PartBoundaries.boundary G S U : ℝ)) =
        2 * ((CrossingEdges.graph G S p).edgeFinset.card : ℝ) := by exact_mod_cast htotal
    have hc : (∑ U ∈ P.parts, (U.card : ℝ)) = S.card := by exact_mod_cast hcards
    rw [ht, hc]
    linarith
  have hmass := FiniteGoodMass.half P.parts Finset.card (PartBoundaries.boundary G S) hε hbudget
  let good := P.parts.filter (fun U => (PartBoundaries.boundary G S U : ℝ) ≤ 4 * ε * U.card)
  have hsub : good.biUnion id ⊆ covered G S k ε := by
    intro v hv
    obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
    have hUF := (Finset.mem_filter.mp hU).1
    have hUg := (Finset.mem_filter.mp hU).2
    exact Finset.mem_biUnion.mpr ⟨U,
      (mem_family G S U k ε).mpr ⟨P.subset U hUF, P.connected U hUF, P.size U hUF, hUg⟩, hv⟩
  have hdis : (good : Set (Finset V)).Pairwise Disjoint :=
    fun U hU W hW hne => P.disjoint (Finset.mem_filter.mp hU).1 (Finset.mem_filter.mp hW).1 hne
  have hc : (good.biUnion id).card = ∑ U ∈ good, U.card := Finset.card_biUnion hdis
  have hs := Finset.card_le_card hsub
  have hsreal : (∑ U ∈ good, (U.card : ℝ)) ≤ (covered G S k ε).card := by
    have hh := hc.symm.trans_le hs
    exact_mod_cast hh
  have hreal : (∑ U ∈ P.parts, (U.card : ℝ)) = S.card := by exact_mod_cast hcards
  rw [hreal] at hmass
  exact hmass.trans hsreal
end Paper.EligibleSets
