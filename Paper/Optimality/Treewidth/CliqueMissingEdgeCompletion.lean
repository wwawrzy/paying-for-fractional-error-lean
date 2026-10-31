import Paper.Optimality.Treewidth.CliqueTwoContractions
import Paper.Optimality.Treewidth.CliqueRootedProjection

/-! Complete the missing edge of a genuine six-branch minor through a
connected disjoint outside set. Retaining an apex then forces K7. This
is a model construction, independent of any density conclusion. -/
namespace Paper.CliqueMissingEdgeCompletion

open SimpleGraph CliqueTwoContractions
variable {V : Type} {G : SimpleGraph V} {p q : Fin 6}

def expanded (m : MinorModel (punctured p q) G) (X : Set V) (a : Fin 6) : Set V :=
  if a = p then m.branchSet a ∪ X else m.branchSet a

theorem original_subset (m : MinorModel (punctured p q) G) (X : Set V) (a : Fin 6) :
    m.branchSet a ⊆ expanded m X a := by
  intro z hz
  unfold expanded
  split_ifs
  · exact Or.inl hz
  · exact hz

theorem outside_subset (m : MinorModel (punctured p q) G) (X : Set V) :
    X ⊆ expanded m X p := by
  intro z hz
  simpa [expanded] using (Or.inr hz : z ∈ m.branchSet p ∪ X)

noncomputable def model (m : MinorModel (punctured p q) G) (X : Set V)
    (hX : (G.induce X).Connected) (hdisj : ∀ a, Disjoint X (m.branchSet a))
    (hattachP : ∃ a ∈ m.branchSet p, ∃ z ∈ X, G.Adj a z)
    (hattachQ : ∃ z ∈ X, ∃ b ∈ m.branchSet q, G.Adj z b) :
    MinorModel (completeGraph (Fin 6)) G := by
  classical
  refine {
    branchSet := expanded m X
    nonempty := fun a => (m.nonempty a).mono (original_subset m X a)
    disjoint := ?_
    connected := ?_
    adjacent := ?_
  }
  · intro a b hab
    dsimp only [expanded]
    split_ifs with ha hb
    · exact False.elim (hab (ha.trans hb.symm))
    · exact Set.disjoint_union_left.mpr ⟨m.disjoint a b hab, hdisj b⟩
    · exact Set.disjoint_union_right.mpr ⟨m.disjoint a b hab, (hdisj a).symm⟩
    · exact m.disjoint a b hab
  · intro a
    by_cases ha : a = p
    · subst a
      obtain ⟨u, hu, z, hz, huz⟩ := hattachP
      have hsets : expanded m X p = m.branchSet p ∪ X := by simp [expanded]
      exact Eq.mpr (congrArg (fun Y : Set V => (G.induce Y).Connected) hsets)
        (connected_induce_union (m.connected p).preconnected hX.preconnected hu hz huz)
    · have hsets : expanded m X a = m.branchSet a := by simp [expanded, ha]
      exact Eq.mpr (congrArg (fun Y : Set V => (G.induce Y).Connected) hsets) (m.connected a)
  · intro a b hab
    change a ≠ b at hab
    by_cases hH : (punctured p q).Adj a b
    · obtain ⟨u, hu, z, hz, huz⟩ := m.adjacent a b hH
      exact ⟨u, original_subset m X a hu, z, original_subset m X b hz, huz⟩
    · have hmissing : a = p ∧ b = q ∨ a = q ∧ b = p := by
        by_contra hn
        exact hH ⟨hab, hn⟩
      rcases hmissing with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · subst a
        subst b
        obtain ⟨z, hz, u, hu, hzu⟩ := hattachQ
        exact ⟨z, outside_subset m X hz, u, original_subset m X q hu, hzu⟩
      · subst a
        subst b
        obtain ⟨z, hz, u, hu, hzu⟩ := hattachQ
        exact ⟨u, original_subset m X q hu, z, outside_subset m X hz, hzu.symm⟩

theorem rooted_impossible [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsKMinorFree 7) (m : MinorModel (punctured p q) G) (X : Set V)
    (hX : (G.induce X).Connected) (hdisj : ∀ a, Disjoint X (m.branchSet a))
    (hattachP : ∃ a ∈ m.branchSet p, ∃ z ∈ X, G.Adj a z)
    (hattachQ : ∃ z ∈ X, ∃ b ∈ m.branchSet q, G.Adj z b)
    (v : V) (hvX : v ∉ X) (havoid : ∀ a, v ∉ m.branchSet a)
    (htouch : ∀ a, ∃ z ∈ m.branchSet a, G.Adj v z) : False := by
  classical
  let n := model m X hX hdisj hattachP hattachQ
  have havoidN : ∀ a, v ∉ n.branchSet a := by
    intro a
    change v ∉ expanded m X a
    by_cases ha : a = p
    · simpa only [expanded, if_pos ha, Set.mem_union, not_or] using And.intro (havoid a) hvX
    · simpa only [expanded, if_neg ha] using havoid a
  have htouchN : ∀ a, ∃ z ∈ n.branchSet a, G.Adj v z := by
    intro a
    obtain ⟨z, hz, hvz⟩ := htouch a
    exact ⟨z, original_subset m X a hz, hvz⟩
  have hf := CliqueRootedProjection.excludes 7 (by decide) hG n v havoidN htouchN
  exact hf (IsMinor.refl _)

end Paper.CliqueMissingEdgeCompletion

#print axioms Paper.CliqueMissingEdgeCompletion.original_subset
#print axioms Paper.CliqueMissingEdgeCompletion.outside_subset
#print axioms Paper.CliqueMissingEdgeCompletion.model
#print axioms Paper.CliqueMissingEdgeCompletion.rooted_impossible
