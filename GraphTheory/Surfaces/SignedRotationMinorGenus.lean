import GraphTheory.Surfaces.SignedRotationGeneralContraction
import GraphTheory.Surfaces.SignedRotationCopyTransport
import GraphTheory.Surfaces.SignedRotationGeneralDensity
import GraphTheory.SimpleGraph.Minor.BranchContraction
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
universe u v
variable {W : Type v} [Fintype W] [DecidableEq W]
theorem exists_minorModel_genus_le (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : SignedRotation G) (H : SimpleGraph W) [DecidableRel H.Adj] (m : MinorModel H G) :
    ∃ s : SignedRotation H, s.eulerGenus ≤ r.eulerGenus := by
  classical
  by_cases hs : ∀ x, (m.branchSet x).Subsingleton
  · exact r.exists_copy_genus_le (m.singletonCopy hs)
  · push Not at hs
    obtain ⟨k,hk⟩ := hs
    obtain ⟨a,ha,b,hb,hne⟩ := hk
    obtain ⟨u,hu,v,hv,huv⟩ := m.exists_internal_edge k a b ha hb hne
    obtain ⟨q,hq⟩ := exists_contract_genus_le G r u v huv
    let m' := m.contractInsideBranch k u v hu hv
    obtain ⟨s,hs⟩ := exists_minorModel_genus_le (ContrVertex u v) (contrGraph G u v) q H m'
    exact ⟨s,hs.trans hq⟩
termination_by Fintype.card V
decreasing_by
  exact contrVertex_card_lt huv.ne
theorem exists_minor_genus_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : SignedRotation G)
    (H : SimpleGraph W) [DecidableRel H.Adj] (hm : IsMinor H G) :
    ∃ s : SignedRotation H, s.eulerGenus ≤ r.eulerGenus := by
  obtain ⟨m⟩ := hm
  exact exists_minorModel_genus_le V G r H m

theorem minor_edge_bound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : SignedRotation G)
    (H : SimpleGraph W) [DecidableRel H.Adj] (hm : IsMinor H G)
    (e : ℝ) (hg : (r.eulerGenus : ℝ) ≤ e) :
    (H.edgeFinset.card : ℝ) ≤ 3 * Fintype.card W + 3 * e := by
  obtain ⟨s,hs⟩ := exists_minor_genus_le G r H hm
  have hd : (H.edgeFinset.card : ℝ) ≤ 3 * Fintype.card W + 3 * (s.eulerGenus : ℝ) := by
    exact_mod_cast s.edge_genus_bound
  have hs' : (s.eulerGenus : ℝ) ≤ (r.eulerGenus : ℝ) := by exact_mod_cast hs
  linarith

end SimpleGraph.SignedRotation
