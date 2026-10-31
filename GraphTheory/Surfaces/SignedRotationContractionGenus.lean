import GraphTheory.Surfaces.SignedRotationContractionComponents
import GraphTheory.Surfaces.SignedRotationContractionSupport
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] (r : SignedRotation G) (d : G.Dart)
variable (hc : ∀ w, ¬ (G.Adj d.fst w ∧ G.Adj d.snd w))
theorem contract_genus_le_either_nonfixed (ht : r.twist d = false)
    (hd : r.σ d ≠ d ∨ r.σ d.symm ≠ d.symm) :
    (r.contractRotation d hc).eulerGenus ≤ r.eulerGenus := by
  classical
  let H := contrGraph G d.fst d.snd
  let q := r.contractRotation d hc
  have hm : contrMk d.fst d.snd d.fst ∈ H.support := by
    rcases hd with hd | hd
    · have hs : r.σ d ≠ d.symm := by
        intro he
        have hh := r.σ_source d
        rw [he] at hh
        exact d.adj.ne hh.symm
      let z := contractionDartMap d ⟨r.σ d,hd,hs⟩
      have hz : z.fst = contrMk d.fst d.snd d.fst := by
        change contrMk d.fst d.snd (r.σ d).fst = _
        rw [r.σ_source]
      exact hz ▸ H.mem_support.mpr ⟨z.snd,z.adj⟩
    · have hs : r.σ d.symm ≠ d := by
        intro he
        have hh := r.σ_source d.symm
        rw [he] at hh
        exact d.adj.ne hh
      let z := contractionDartMap d ⟨r.σ d.symm,hs,hd⟩
      have hz : z.fst = contrMk d.fst d.snd d.fst := by
        change contrMk d.fst d.snd (r.σ d.symm).fst = _
        rw [r.σ_source]
        exact (contrMk_eq _ _).symm
      exact hz ▸ H.mem_support.mpr ⟨z.snd,z.adj⟩
  have hv := contraction_support_card_lower G d.fst d.snd d.adj hm
  rw [← r.vertex_card,← q.vertex_card] at hv
  have he := contract_edge_card d hc
  have he₁ := r.edge_card
  have he₂ := q.edge_card
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he₁ he₂
  have hf := r.contract_faces_lower_of_either_nonfixed d hc ht hd
  have hcomp := r.contract_component_card_le d hc
  change Nat.card r.Face ≤ Nat.card q.Face at hf
  change Nat.card q.Component ≤ Nat.card r.Component at hcomp
  unfold eulerGenus eulerCharacteristic
  change 2 * (Nat.card q.Component : ℤ) - ((Nat.card q.Vertex : ℤ) - (Nat.card q.Edge : ℤ) + (Nat.card q.Face : ℤ)) ≤ _
  rw [he₁,he₂]
  dsimp only [H] at *
  omega
end SimpleGraph.SignedRotation
