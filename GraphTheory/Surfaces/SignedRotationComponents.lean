import GraphTheory.Surfaces.SignedRotationVertices

/-! Flag connectivity agrees with graph reachability. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)
  [Fintype V] [DecidableRel G.Adj]

def ComponentRel (x y : Flag G) : Prop :=
  Relation.EqvGen (fun a b : Flag G =>
    r.edgeFlip a = b ∨ sideFlip a = b ∨ r.cornerFlip a = b) x y

omit [Fintype V] [DecidableRel G.Adj] in
private theorem component_of_vertex {x y : Flag G}
    (h : (pairSetoid (sideFlip (G := G)) r.cornerFlip).r x y) : r.ComponentRel x y :=
  Relation.EqvGen.mono (fun _ _ hab => hab.elim
    (fun hs => Or.inr (Or.inl hs)) (fun hc => Or.inr (Or.inr hc))) h

private theorem component_of_walk {u v : V} (p : G.Walk u v) :
    ∀ x y : Flag G, x.1.toProd.1 = u → y.1.toProd.1 = v → r.ComponentRel x y := by
  induction p with
  | nil =>
    intro x y hx hy
    exact component_of_vertex r ((r.vertex_relation_iff x y).mpr (hx.trans hy.symm))
  | @cons u w v huv p ih =>
    intro x y hx hy
    let z : Flag G := (⟨(u, w), huv⟩, false)
    have h₁ : r.ComponentRel x z :=
      component_of_vertex r ((r.vertex_relation_iff x z).mpr hx)
    have h₂ : r.ComponentRel z (r.edgeFlip z) := Relation.EqvGen.rel _ _ (Or.inl rfl)
    have h₃ := ih (r.edgeFlip z) y rfl hy
    exact Relation.EqvGen.trans _ _ _ h₁ (Relation.EqvGen.trans _ _ _ h₂ h₃)

theorem component_relation_iff (x y : Flag G) :
    r.ComponentRel x y ↔ G.Reachable x.1.toProd.1 y.1.toProd.1 := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
      rcases h with h | h | h
      · subst b
        exact a.1.adj.reachable
      · subst b
        exact Reachable.refl _
      · subst b
        rw [r.cornerFlip_source]
    | refl => exact Reachable.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih hj => exact ih.trans hj
  · rintro ⟨p⟩
    exact component_of_walk r p x y rfl rfl

theorem component_card_of_connected (hG : G.Connected) [Nonempty G.Dart] :
    Nat.card r.Component = 1 := by
  classical
  letI : Nonempty r.Component := ⟨Quotient.mk _ (Classical.choice inferInstance, false)⟩
  letI : Subsingleton r.Component := ⟨by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact Quotient.sound ((r.component_relation_iff a b).mpr (hG.preconnected _ _))⟩
  exact Nat.card_unique

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.component_relation_iff
#print axioms SimpleGraph.SignedRotation.component_card_of_connected
