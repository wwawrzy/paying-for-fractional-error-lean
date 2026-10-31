import Paper.Endpoints.Girth.HighGirthTrimmedSupport
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
set_option maxHeartbeats 200000
namespace Paper.HighGirthTrimmedConnected

theorem trimmed_path_connected
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (K : (G.induce (↑(Paper.HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (a b : K) (p : K.toSimpleGraph.Walk a b)
    (hS : (Paper.HighGirthAttachmentPositions.positions G x K p).Nonempty) :
    (G.induce (↑(Paper.HighGirthTrimmedPath.vertices G x K p hS) : Set V)).Connected := by
  classical
  let S := Paper.HighGirthAttachmentPositions.positions G x K p
  let m := S.min' hS
  let M := S.max' hS
  let r := (p.drop m).take (M-m)
  have hsup := (Paper.HighGirthTrimmedSupport.trimmed_path_support G x K a b p hS).2.2
  change r.support.toFinset.image (fun v : K => v.val.val) = Paper.HighGirthTrimmedPath.vertices G x K p hS at hsup
  let f : K.toSimpleGraph →g G := ⟨fun v => v.val.val, by intro v w hvw; exact hvw⟩
  have he : {u | u ∈ (r.map f).support} = (↑(Paper.HighGirthTrimmedPath.vertices G x K p hS) : Set V) := by
    rw [←hsup]
    ext u
    simp only [Set.mem_setOf_eq, SimpleGraph.Walk.support_map, Finset.mem_coe, List.mem_map, f]
  
  
  
  
  
  
    simp [List.mem_toFinset]
  rw [←he]
  exact (r.map f).connected_induce_support

end Paper.HighGirthTrimmedConnected

#print axioms Paper.HighGirthTrimmedConnected.trimmed_path_connected
