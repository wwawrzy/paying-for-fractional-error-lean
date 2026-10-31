import Paper.Preliminaries.ResidualDefects
import Paper.Preliminaries.RadiusThree

namespace Paper.ResidualWalkDefects
open SevenFoundation ResidualDefects
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def closure (S : Finset V) : ℕ → Finset V
  | 0 => S
  | n+1 => covered G (closure S n)

theorem subset_closure (S : Finset V) (n : ℕ) : S ⊆ closure G S n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact ih.trans (subset_covered G _)

theorem closure_mono (S : Finset V) {n m : ℕ} (h : n ≤ m) : closure G S n ⊆ closure G S m := by
  induction m,h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ m hm ih => exact ih.trans (subset_covered G _)

theorem walk_cover (R : Finset V) (d : ℕ) {v b : V} (p : G.Walk v b)
    (hb : G.degree b ≠ d) (hv : v ∈ R) :
    (⟨v,hv⟩ : (R:Set V)) ∈ closure (G.induce (R:Set V)) (localDefects G R d) p.length := by
  classical
  induction p with
  | nil =>
    change (⟨_,hv⟩ : (R:Set V)) ∈ localDefects G R d
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hb⟩
  | @cons v u b ha p ih =>
    let J := G.induce (R:Set V)
    let S := localDefects G R d
    by_cases hT : (⟨v,hv⟩ : (R:Set V)) ∈ S
    · exact subset_closure J S _ hT
    · have he := outside_localDefects G R d hT
      have hu : u ∈ R := neighbors_retained G R ⟨v,hv⟩ (he.1.trans he.2.symm) u ha
      have hmem := ih hb hu
      change (⟨v,hv⟩ : (R:Set V)) ∈ covered J (closure J S p.length)
      exact Finset.mem_biUnion.mpr ⟨⟨u,hu⟩,hmem,
        (mem_closed J ⟨v,hv⟩ ⟨u,hu⟩).mpr (Or.inr ha.symm)⟩

theorem cover_three (R : Finset V) (d : ℕ)
    (hpaths : ∀ v ∈ R, ∃ b, G.degree b ≠ d ∧ ∃ p : G.Walk v b, p.length ≤ 3) :
    ∀ v : (R:Set V), v ∈ covered (G.induce (R:Set V))
      (covered (G.induce (R:Set V)) (covered (G.induce (R:Set V)) (localDefects G R d))) := by
  intro v
  obtain ⟨b,hb,p,hp⟩ := hpaths v.val v.property
  have hmem := walk_cover G R d p hb v.property
  exact closure_mono (G.induce (R:Set V)) (localDefects G R d) hp hmem

end Paper.ResidualWalkDefects
#print axioms Paper.ResidualWalkDefects.cover_three
