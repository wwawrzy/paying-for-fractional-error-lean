import Paper.Endpoints.Girth.HighGirthResidualSize
import Mathlib.Combinatorics.SimpleGraph.Paths
set_option maxHeartbeats 200000
namespace Paper.HighGirthShortPaths

theorem two_closed_steps_path
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u p b : V) (hu : u ∈ S) (hp : p ∈ S) (hb : b ∈ S)
    (hup : u ∈ Paper.SevenFoundation.closed G p)
    (hpb : p ∈ Paper.SevenFoundation.closed G b) :
    ∃ w : G.Walk u b, w.IsPath ∧ w.length ≤ 2 ∧ ∀ v ∈ w.support, v ∈ S := by
  classical
    have hwalk : ∃ w : G.Walk u b, w.length ≤ 2 ∧ ∀ v ∈ w.support, v ∈ S := by
      rcases (Paper.SevenFoundation.mem_closed G u p).mp hup with heq | hpu
      · subst u
        rcases (Paper.SevenFoundation.mem_closed G p b).mp hpb with heq | hbp
        · subst p
          exact ⟨SimpleGraph.Walk.nil, by simp, by simpa using hb⟩
        · refine ⟨SimpleGraph.Walk.cons hbp.symm SimpleGraph.Walk.nil, by simp, ?_⟩
          intro v hv
          have hv' : v = p ∨ v = b := by simpa using hv
          rcases hv' with rfl | rfl
          · exact hp
          · exact hb
      · rcases (Paper.SevenFoundation.mem_closed G p b).mp hpb with heq | hbp
        · subst p
          refine ⟨SimpleGraph.Walk.cons hpu.symm SimpleGraph.Walk.nil, by simp, ?_⟩
          intro v hv
          have hv' : v = u ∨ v = b := by simpa using hv
          rcases hv' with rfl | rfl
          · exact hu
          · exact hb
        · refine ⟨SimpleGraph.Walk.cons hpu.symm (SimpleGraph.Walk.cons hbp.symm SimpleGraph.Walk.nil), by simp, ?_⟩
          intro v hv
          have hv' : v = u ∨ v = p ∨ v = b := by simpa using hv
          rcases hv' with rfl | rfl | rfl
          · exact hu
          · exact hp
          · exact hb
    obtain ⟨w, hw, hs⟩ := hwalk
    exact ⟨w.bypass, w.bypass_isPath, (w.length_bypass_le).trans hw,
      fun v hv => hs v (w.support_bypass_subset hv)⟩

end Paper.HighGirthShortPaths

#print axioms Paper.HighGirthShortPaths.two_closed_steps_path
