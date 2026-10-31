import Paper.Optimality.Treewidth.CliqueInducedLift
import Paper.Optimality.Treewidth.CliqueExteriorContacts
import Paper.Optimality.Treewidth.CliqueMissingEdgeCompletion

/-! The exterior-component bridge for the K7 structural argument. A
six-branch almost-complete minor in a least-degree neighborhood excludes
a connected exterior. The bounded neighborhood-witness theorem remains
a separate obligation; it is explicit in this intermediate statement. -/
namespace Paper.SevenCliqueExteriorDisconnected

open SimpleGraph CliqueTwoContractions
variable {V : Type} {G : SimpleGraph V} {p q : Fin 6}

private noncomputable def direct_model (m : MinorModel (punctured p q) G)
    (hcross : ∃ a ∈ m.branchSet p, ∃ b ∈ m.branchSet q, G.Adj a b) :
    MinorModel (completeGraph (Fin 6)) G where
  branchSet := m.branchSet
  nonempty := m.nonempty
  disjoint := m.disjoint
  connected := m.connected
  adjacent a b hab := by
    change a ≠ b at hab
    by_cases hH : (punctured p q).Adj a b
    · exact m.adjacent a b hH
    · have hmissing : a = p ∧ b = q ∨ a = q ∧ b = p := by
        by_contra hn
        exact hH ⟨hab, hn⟩
      rcases hmissing with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · subst a
        subst b
        exact hcross
      · subst a
        subst b
        obtain ⟨x, hx, y, hy, hxy⟩ := hcross
        exact ⟨y, hy, x, hx, hxy.symm⟩

theorem not_connected [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsKMinorFree 7) (v : V) (hmin : ∀ z, G.degree v ≤ G.degree z)
    (p q : Fin 6) (hpq : p ≠ q)
    (m : MinorModel (punctured p q) (G.induce (G.neighborSet v))) :
    ¬(G.induce (insert v (G.neighborSet v))ᶜ).Connected := by
  classical
  intro hconn
  let n := CliqueInducedLift.model G (G.neighborSet v) m
  have hsub : ∀ a, n.branchSet a ⊆ G.neighborSet v :=
    CliqueInducedLift.branch_subset G (G.neighborSet v) m
  have havoid : ∀ a, v ∉ n.branchSet a := by
    intro a hh
    exact G.loopless.irrefl v (hsub a hh)
  have htouch : ∀ a, ∃ z ∈ n.branchSet a, G.Adj v z := by
    intro a
    obtain ⟨z, hz⟩ := n.nonempty a
    exact ⟨z, hz, hsub a hz⟩
  by_cases hcross : ∃ a ∈ n.branchSet p, ∃ b ∈ n.branchSet q, G.Adj a b
  · let k := direct_model n hcross
    have hf := CliqueRootedProjection.excludes 7 (by decide) hG k v havoid htouch
    exact hf (IsMinor.refl _)
  · let X : Set V := (insert v (G.neighborSet v))ᶜ
    have hdisj : ∀ a, Disjoint X (n.branchSet a) := by
      intro a
      rw [Set.disjoint_left]
      intro z hzX hzB
      exact hzX (Or.inr (hsub a hzB))
    obtain ⟨a, ha⟩ := n.nonempty p
    obtain ⟨b, hb⟩ := n.nonempty q
    have hab : a ≠ b := (n.disjoint p q hpq).ne_of_mem ha hb
    have hnot : ¬G.Adj a b := fun hh => hcross ⟨a, ha, b, hb, hh⟩
    obtain ⟨z, hz, haz⟩ := CliqueExteriorContacts.exists_contact G v a b
      (hsub p ha) (hsub q hb) hab hnot (hmin a)
    obtain ⟨w, hw, hbw⟩ := CliqueExteriorContacts.exists_contact G v b a
      (hsub q hb) (hsub p ha) hab.symm (fun hh => hnot hh.symm) (hmin b)
    exact CliqueMissingEdgeCompletion.rooted_impossible hG n X hconn hdisj
      ⟨a, ha, z, hz, haz⟩ ⟨w, hw, b, hb, hbw.symm⟩
      v (fun hh => hh (Set.mem_insert _ _)) havoid htouch

end Paper.SevenCliqueExteriorDisconnected

#print axioms Paper.SevenCliqueExteriorDisconnected.not_connected
