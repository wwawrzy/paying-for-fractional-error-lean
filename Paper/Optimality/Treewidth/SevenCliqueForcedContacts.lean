import Paper.Optimality.Treewidth.SevenCliqueUniversalContact
import Paper.Optimality.Treewidth.CliqueForcedExteriorContact
namespace Paper.SevenCliqueTwentySixClassification
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem forced_contacts (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    let T := vertices (outside G (insert v (G.neighborSet v)) C)
    ∃ x ∈ T, ∃ p ∉ T, G.Adj x p ∧
      ∀ z ∈ T, G.inducedDegree z T = 5 → G.Adj p z := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  obtain ⟨x,hx,hinside,houtside⟩ := universal_contact G hG horder hmin hcn hsep v hv8 C hsize
  change G.inducedDegree x T = 7 at hinside
  obtain ⟨p,hp,hxp,hunique⟩ := unique_outside G T x houtside
  change ∃ x ∈ T, ∃ p ∉ T, G.Adj x p ∧ ∀ z ∈ T, G.inducedDegree z T = 5 → G.Adj p z
  refine ⟨x,hx,p,hp,hxp,?_⟩
  intro z hz hdeg
  have hzx : z ≠ x := by intro heq; subst z; omega
  have hxz := CliqueForcedExteriorContact.universal_inside G T x hx hsize hinside z hz hzx
  exact CliqueForcedExteriorContact.forced G T x p z hx hxz hunique hdeg (hcn x z hxz)
end Paper.SevenCliqueTwentySixClassification
