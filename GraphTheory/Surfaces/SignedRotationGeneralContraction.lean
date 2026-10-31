import GraphTheory.Surfaces.SignedRotationDartTransport
import GraphTheory.Surfaces.SignedRotationContractionFaces
import GraphTheory.Surfaces.SignedRotationContractionGenus
import GraphTheory.Surfaces.SignedRotationContractionReduction
import GraphTheory.Surfaces.SignedRotationSubgraphGenus
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] (r : SignedRotation G) (d : G.Dart)
variable (hfix : r.σ d = d) (hrev : r.σ d.symm = d.symm)
def isolatedEdgeOutside : Set V := {w | w ≠ d.fst ∧ w ≠ d.snd}

include hfix hrev in
theorem isolated_survivor_source (x : ContractionDart d) : x.val.fst ∈ isolatedEdgeOutside d := by
  constructor
  · intro h
    exact x.property.1 (r.dart_eq_of_source_fixed d hfix x.val h)
  · intro h
    exact x.property.2 (r.dart_eq_of_source_fixed d.symm hrev x.val h)

noncomputable def isolatedOutsideDartEquiv :
    (G.induce (isolatedEdgeOutside d)).Dart ≃ ContractionDart d where
  toFun x := ⟨⟨(x.fst.val,x.snd.val),x.adj⟩, by
    constructor
    · intro h
      exact x.fst.property.1 (congrArg (fun a : G.Dart => a.fst) h)
    · intro h
      exact x.fst.property.2 (congrArg (fun a : G.Dart => a.fst) h)⟩
  invFun x := ⟨(⟨x.val.fst,r.isolated_survivor_source d hfix hrev x⟩,
    ⟨x.val.snd,r.isolated_survivor_source d hfix hrev (contractionDartReverse d x)⟩),x.val.adj⟩
  left_inv x := by apply Dart.ext; rfl
  right_inv x := by apply Subtype.val_injective; apply Dart.ext; rfl

include hfix hrev in
theorem isolatedOutside_closed : ∀ ⦃a b : V⦄,
    a ∈ isolatedEdgeOutside d → G.Adj a b → b ∈ isolatedEdgeOutside d := by
  intro a b ha hab
  constructor
  · intro hb
    have he := r.dart_eq_of_source_fixed d hfix (⟨(b,a),hab.symm⟩ : G.Dart) hb
    exact ha.2 (congrArg (fun x : G.Dart => x.snd) he)
  · intro hb
    have he := r.dart_eq_of_source_fixed d.symm hrev (⟨(b,a),hab.symm⟩ : G.Dart) hb
    exact ha.1 (congrArg (fun x : G.Dart => x.snd) he)

variable (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w))
noncomputable def isolatedContractDartEquiv :
    (G.induce (isolatedEdgeOutside d)).Dart ≃ (contrGraph G d.fst d.snd).Dart :=
  (r.isolatedOutsideDartEquiv d hfix hrev).trans (contractionDartEquiv d hc)

theorem isolatedContractDartEquiv_source
    (a b : (G.induce (isolatedEdgeOutside d)).Dart) :
    (r.isolatedContractDartEquiv d hfix hrev hc a).fst =
      (r.isolatedContractDartEquiv d hfix hrev hc b).fst ↔ a.fst = b.fst := by
  change contrMk d.fst d.snd a.fst.val = contrMk d.fst d.snd b.fst.val ↔ _
  constructor
  · intro h
    apply Subtype.ext
    exact contrMk_injOn_compl_v d.fst d.snd a.fst.property.2 b.fst.property.2 h
  · intro h
    rw [h]

theorem isolatedContractDartEquiv_reverse
    (a : (G.induce (isolatedEdgeOutside d)).Dart) :
    r.isolatedContractDartEquiv d hfix hrev hc a.symm =
      (r.isolatedContractDartEquiv d hfix hrev hc a).symm := by
  rfl

include hfix hrev hc in
theorem exists_contract_genus_le_both_fixed :
    ∃ q : SignedRotation (contrGraph G d.fst d.snd), q.eulerGenus ≤ r.eulerGenus := by
  classical
  let S := isolatedEdgeOutside d
  let hs := r.isolatedOutside_closed d hfix hrev
  let s := r.restrictClosed S hs
  let e := r.isolatedContractDartEquiv d hfix hrev hc
  let q := s.dartTransport e (r.isolatedContractDartEquiv_source d hfix hrev hc)
    (r.isolatedContractDartEquiv_reverse d hfix hrev hc)
  refine ⟨q,?_⟩
  have he : q.eulerGenus = s.eulerGenus := s.dartTransport_eulerGenus e _ _
  exact he.le.trans (r.restrictClosed_genus_le S hs)
include hc in
theorem exists_contract_genus_le_no_common :
    ∃ q : SignedRotation (contrGraph G d.fst d.snd), q.eulerGenus ≤ r.eulerGenus := by
  obtain ⟨s,ht,hg⟩ := r.exists_untwisted_same_genus d
  have hex : ∃ q : SignedRotation (contrGraph G d.fst d.snd), q.eulerGenus ≤ s.eulerGenus := by
    by_cases hfix : s.σ d = d
    · by_cases hrev : s.σ d.symm = d.symm
      · exact s.exists_contract_genus_le_both_fixed d hfix hrev hc
      · exact ⟨s.contractRotation d hc,s.contract_genus_le_either_nonfixed d hc ht (Or.inr hrev)⟩
    · exact ⟨s.contractRotation d hc,s.contract_genus_le_either_nonfixed d hc ht (Or.inl hfix)⟩
  obtain ⟨q,hq⟩ := hex
  exact ⟨q,hq.trans hg.le⟩

end SimpleGraph.SignedRotation
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem exists_contract_genus_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : SignedRotation G) (u v : V) (huv : G.Adj u v) :
    ∃ q : SignedRotation (contrGraph G u v), q.eulerGenus ≤ r.eulerGenus := by
  classical
  let K := contractionReduced G u v
  obtain ⟨s,hs⟩ := exists_contractionReduced_rotation G u v r
  let d : K.Dart := ⟨(u,v),contractionReduced_edge G u v huv⟩
  have hc : ∀ w, ¬ (K.Adj d.fst w ∧ K.Adj d.snd w) := contractionReduced_no_common G u v
  obtain ⟨q,hq⟩ := s.exists_contract_genus_le_no_common d hc
  have he : contrGraph K u v = contrGraph G u v := contractionReduced_contract G u v huv.ne
  refine ⟨he ▸ q,?_⟩
  rw [eulerGenus_transport he q]
  exact hq.trans hs

end SimpleGraph.SignedRotation

