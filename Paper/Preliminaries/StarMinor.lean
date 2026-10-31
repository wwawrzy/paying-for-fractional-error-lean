import Paper.Preliminaries.SevenFoundation
import GraphTheory.SimpleGraph.Minor.Defs

/-! Actual disjoint-star contraction for minor counting. No density is assumed. -/
namespace Paper.StarMinor
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Assign a covered noncenter to one of its adjacent centers; retain all others. -/
noncomputable def owner (W : Finset V) (v : V) : V := by
  classical
  exact if v ∈ W then v else
    if h : ∃ w ∈ W, G.Adj w v then h.choose else v

omit [Fintype V] in
theorem owner_center (W : Finset V) {v : V} (hv : v ∈ W) :
    owner G W v = v := by
  classical
  simp [owner, hv]

theorem owner_uncovered (W : Finset V) {v : V} (hv : v ∉ covered G W) :
    owner G W v = v := by
  classical
  have hn : v ∉ W := fun h => hv (subset_covered G W h)
  have he : ¬ ∃ w ∈ W, G.Adj w v := by
    rintro ⟨w, hw, ha⟩
    exact hv (Finset.mem_biUnion.mpr ⟨w, hw, (mem_closed G v w).mpr (Or.inr ha)⟩)
  simp [owner, hn, he]

theorem owner_star (W : Finset V) (v : V) :
    owner G W v = v ∨ G.Adj (owner G W v) v := by
  classical
  by_cases hv : v ∈ W
  · exact Or.inl (owner_center G W hv)
  by_cases he : ∃ w ∈ W, G.Adj w v
  · right
    simpa [owner, hv, he] using he.choose_spec.2
  · left; simp [owner, hv, he]

theorem owner_covered (W : Finset V) {v : V} (hv : v ∈ covered G W) :
    owner G W v ∈ W := by
  classical
  by_cases hw : v ∈ W
  · simpa [owner_center G W hw] using hw
  have he : ∃ w ∈ W, G.Adj w v := by
    obtain ⟨w, hwW, hvw⟩ := Finset.mem_biUnion.mp hv
    rcases (mem_closed G v w).mp hvw with heq | ha
    · exact False.elim (hw (heq ▸ hwW))
    · exact ⟨w, hwW, ha⟩
  simpa [owner, hw, he] using he.choose_spec.1

/-- The retained vertices are precisely the centers and the residual vertices. -/
def graph (W R : Finset V) : SimpleGraph {v // v ∈ W ∪ R} where
  Adj i j := i ≠ j ∧ ∃ u v, owner G W u = i.val ∧ owner G W v = j.val ∧ G.Adj u v
  symm := by
    rintro i j ⟨hne, u, v, hu, hv, ha⟩
    exact ⟨hne.symm, v, u, hv, hu, ha.symm⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem owner_retained (W R : Finset V) (hR : Disjoint R (covered G W))
    (i : {v // v ∈ W ∪ R}) : owner G W i.val = i.val := by
  rcases Finset.mem_union.mp i.property with hw | hr
  · exact owner_center G W hw
  · exact owner_uncovered G W (fun hc => Finset.disjoint_left.mp hR hr hc)

/-- Fibers of the explicit owner map are nonempty disjoint connected stars. -/
noncomputable def model (W R : Finset V) (hR : Disjoint R (covered G W)) :
    SimpleGraph.MinorModel (graph G W R) G where
  branchSet i := {v | owner G W v = i.val}
  nonempty i := ⟨i.val, owner_retained G W R hR i⟩
  disjoint i j hij := by
    apply Set.disjoint_left.mpr
    intro v hi hj
    exact hij (Subtype.ext (hi.symm.trans hj))
  connected i := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨i.val, owner_retained G W R hR i⟩, ?_⟩
    intro v
    rcases owner_star G W v.val with he | ha
    · have heq : i.val = v.val := v.property.symm.trans he
      have hs : (⟨i.val, owner_retained G W R hR i⟩ : {v | owner G W v = i.val}) = v :=
        Subtype.ext heq
      rw [hs]
    · have ha' : G.Adj i.val v.val := by
        have hv : owner G W v.val = i.val := v.property
        rwa [hv] at ha
      exact (show (G.induce {v | owner G W v = i.val}).Adj
        ⟨i.val, owner_retained G W R hR i⟩ v from ha').reachable
  adjacent i j hij := by
    obtain ⟨_, u, v, hu, hv, ha⟩ := hij
    exact ⟨u, hu, v, hv, ha⟩

theorem isMinor (W R : Finset V) (hR : Disjoint R (covered G W)) :
    SimpleGraph.IsMinor (graph G W R) G := ⟨model G W R hR⟩

/-- Every edge of G[R] survives in the simple minor. -/
theorem residual_edge (W R : Finset V) (hR : Disjoint R (covered G W))
    {u v : V} (hu : u ∈ R) (hv : v ∈ R) (ha : G.Adj u v) :
    (graph G W R).Adj ⟨u, Finset.mem_union_right W hu⟩
      ⟨v, Finset.mem_union_right W hv⟩ := by
  refine ⟨?_, u, v, ?_, ?_, ha⟩
  · intro heq
    exact ha.ne (congrArg Subtype.val heq)
  · exact owner_retained G W R hR ⟨u, Finset.mem_union_right W hu⟩
  · exact owner_retained G W R hR ⟨v, Finset.mem_union_right W hv⟩

/-- A residual-to-covered edge gives an edge to an actual star center. -/
theorem boundary_edge (W R : Finset V) (hR : Disjoint R (covered G W))
    {q v : V} (hq : q ∈ R) (hv : v ∈ covered G W) (ha : G.Adj q v) :
    ∃ w, ∃ hw : w ∈ W,
      (graph G W R).Adj ⟨q, Finset.mem_union_right W hq⟩
        ⟨w, Finset.mem_union_left R hw⟩ := by
  refine ⟨owner G W v, owner_covered G W hv, ?_⟩
  refine ⟨?_, q, v, owner_retained G W R hR ⟨q, Finset.mem_union_right W hq⟩, rfl, ha⟩
  intro heq
  have he : q = owner G W v := congrArg Subtype.val heq
  have hqW : q ∈ W := he.symm ▸ owner_covered G W hv
  exact Finset.disjoint_left.mp hR hq (subset_covered G W hqW)
end Paper.StarMinor
