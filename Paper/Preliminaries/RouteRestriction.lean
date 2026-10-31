import Paper.Preliminaries.GuardedRoutes

/-! Restrict a genuine guarded walk system to the finite physical vertices
actually used by the routes and roots. -/
namespace Paper.RouteRestriction
attribute [local instance] Classical.propDecidable
open GuardedRoutes
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
variable {K : SimpleGraph A} {G : SimpleGraph B}

noncomputable def restrict (S : System K G) (W : Finset B)
    (hroot : ∀ a, S.root a ∈ W)
    (hroute : ∀ {a b} (h : K.Adj a b), ∀ v ∈ (S.route h).support, v ∈ W) :
    System K (G.induce (W : Set B)) where
  root a := ⟨S.root a, hroot a⟩
  injective := fun a b h => S.injective (congrArg Subtype.val h)
  labels v := S.labels v.val
  root_label a := S.root_label a
  route h := (S.route h).induce (W : Set B) (hroute h)
  guarded h v hv := by
    have he := SimpleGraph.Walk.map_induce (s := (W : Set B)) (S.route h) (hroute h)
    have hm : v.val ∈ (((S.route h).induce (W : Set B) (hroute h)).map
        (SimpleGraph.Embedding.induce (W : Set B)).toHom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    rw [he] at hm
    exact S.guarded h v.val hm
end Paper.RouteRestriction
