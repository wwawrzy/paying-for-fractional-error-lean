import GraphTheory.Surfaces.SignedRotationContractionFaces
import GraphTheory.Surfaces.SignedRotationContractionReduction
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u v : V)
theorem exists_contract_genus_le_connected [Fintype V] [DecidableRel G.Adj]
    (r : SignedRotation G) (huv : G.Adj u v) (hG : G.Connected) :
    ∃ q : SignedRotation (contrGraph G u v), q.eulerGenus ≤ r.eulerGenus := by
  classical
  let K := contractionReduced G u v
  obtain ⟨s,hs⟩ := exists_contractionReduced_rotation G u v r
  let d : K.Dart := ⟨(u,v),contractionReduced_edge G u v huv⟩
  have hc : ∀ w, ¬ (K.Adj d.fst w ∧ K.Adj d.snd w) := contractionReduced_no_common G u v
  have hK : K.Connected := contractionReduced_connected G u v huv hG
  obtain ⟨q,hq⟩ := s.exists_contract_genus_le_connected_no_common d hc hK
  have he : contrGraph K u v = contrGraph G u v := contractionReduced_contract G u v huv.ne
  refine ⟨he ▸ q, ?_⟩
  rw [eulerGenus_transport he q]
  exact hq.trans hs

end SimpleGraph.SignedRotation
