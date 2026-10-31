import Paper.Endpoints.Girth.HighGirthDilution
import GraphTheory.SimpleGraph.Minor.Density

/-! A proper finite minor-closed class has a rational all-minors density bound.
Properness is witnessed by one excluded finite graph; no density is assumed. -/
namespace Paper.HighGirthProperClass
attribute [local instance] Classical.propDecidable

abbrev Class := ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop

def Closed (P : Class) : Prop :=
  ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W), P G → SimpleGraph.IsMinor H G → P H

theorem rational_density (P : Class) (hclosed : Closed P)
    (hproper : ∃ n, ∃ H : SimpleGraph (Fin n), ¬ P H) :
    ∃ rho : Rat, 1 ≤ rho ∧ ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], P G → MinorDensity.Bound G (rho:Real) := by
  classical
  obtain ⟨n,H,hH⟩ := hproper
  have hHK : SimpleGraph.IsMinor H (⊤ : SimpleGraph (Fin n)) :=
    SimpleGraph.IsMinor.of_subgraph le_top
  have hnotK : ¬ P (⊤ : SimpleGraph (Fin n)) := fun h => hH (hclosed _ H h hHK)
  let M := max 1 (SimpleGraph.maderConst n)
  refine ⟨(M:Rat),by exact_mod_cast (le_max_left 1 (SimpleGraph.maderConst n)),?_⟩
  intro V _ _ G _ hG A _ _ J _ hJ
  have hPJ : P J := hclosed G J hG hJ
  have hfree : J.IsKMinorFree n := by
    intro hK
    exact hnotK (hclosed J _ hPJ hK)
  have he := hfree.edgeFinset_card_le J
  have hM : J.edgeFinset.card ≤ M * Fintype.card A :=
    he.trans (Nat.mul_le_mul_right _ (le_max_right 1 (SimpleGraph.maderConst n)))
  exact_mod_cast hM

theorem excluded_finite_witness (P : Class) (hclosed : Closed P)
    {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (hH : ¬ P H) :
    ∃ n, ∃ J : SimpleGraph (Fin n), ¬ P J := by
  classical
  let f : H →g (⊤ : SimpleGraph (Fin (Fintype.card V))) := {
    toFun := Fintype.equivFin V
    map_rel' := by
      intro u v he
      exact (Fintype.equivFin V).injective.ne he.ne }
  have hm := HighGirthDilution.minor_of_injective f (Fintype.equivFin V).injective
  exact ⟨Fintype.card V,⊤,fun h => hH (hclosed _ H h hm)⟩

end Paper.HighGirthProperClass
#print axioms Paper.HighGirthProperClass.rational_density

#print axioms Paper.HighGirthProperClass.excluded_finite_witness
