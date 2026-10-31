import Paper.Preliminaries.DepthOne

/-! Contract the fibers of an actual star map into fixed retained vertices. -/
namespace Paper.StarMap
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def graph (f : V → V) (K : Finset V) : SimpleGraph K where
  Adj a b := a ≠ b ∧ ∃ u v, f u = a.val ∧ f v = b.val ∧ G.Adj u v
  symm := by rintro a b ⟨hne, u, v, hu, hv, ha⟩; exact ⟨hne.symm, v, u, hv, hu, ha.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def model (f : V → V) (K : Finset V) (hfix : ∀ v ∈ K, f v = v)
    (hstar : ∀ v, f v = v ∨ G.Adj (f v) v) : DepthOne.StarModel (graph G f K) G where
  branchSet a := {v | f v = a.val}
  nonempty a := ⟨a.val, hfix a.val a.property⟩
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v ha hb
    exact hab (Subtype.ext (ha.symm.trans hb))
  connected a := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨a.val, hfix a.val a.property⟩, ?_⟩
    intro v
    rcases hstar v.val with he | ha
    · have hv : (⟨a.val, hfix a.val a.property⟩ : {v | f v = a.val}) = v :=
        Subtype.ext (v.property.symm.trans he)
      rw [hv]
    · have ha' : G.Adj a.val v.val := by rwa [v.property] at ha
      exact (show (G.induce {v | f v = a.val}).Adj ⟨a.val, hfix a.val a.property⟩ v from ha').reachable
  adjacent a b hab := by obtain ⟨_, u, v, hu, hv, ha⟩ := hab; exact ⟨u, hu, v, hv, ha⟩
  root a := a.val
  root_mem a := hfix a.val a.property
  radius_one a v hv := by
    rcases hstar v with he | ha
    · exact Or.inl (hv.symm.trans he)
    · exact Or.inr (by rwa [hv] at ha)
end Paper.StarMap
