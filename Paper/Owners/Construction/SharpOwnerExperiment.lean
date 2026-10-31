import Paper.Owners.Construction.OwnerSampleMinor
import Paper.Owners.Construction.OwnerEdgeCylinder
import Paper.Averaging.Tasks.FiniteMeanIncidence

/-! Half of the owner stars are retained; light vertices choose uniformly
from L padded positions in their full support. All outcomes are physical
minor models through the already proved OwnerSampleMinor construction. -/
namespace Paper.SharpOwnerExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyRepair OwnerExperiment
open FiniteMeanIncidence
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def lift (I : Finset V) (L : ℕ) (hL : 1 ≤ L) (ω : Outcomes (V := V) L) :
    V ⊕ V → Fin (L+1)
  | .inl d => if d ∈ I ∧ ω.1 d = 0 then 0 else ⟨1, by omega⟩
  | .inr v => ⟨(ω.2 v).val, by have hh := (ω.2 v).isLt; omega⟩

theorem sampled_eq (D I : Finset V) (hI : I ⊆ D) (L : ℕ) (hL : 1 ≤ L)
    (ω : Outcomes (V := V) L) : sampled D (lift I L hL ω) = I.filter (fun d => ω.1 d = 0) := by
  ext d
  simp only [sampled, Finset.mem_filter, lift]
  by_cases hd : d ∈ I
  · simp [hd, hI hd]
  · simp [hd]

theorem sampled_mem (D I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (ω : Outcomes (V := V) L) (d : V) (hdD : d ∈ D) (hdI : d ∈ I) (hb : ω.1 d = 0) :
    d ∈ sampled D (lift I L hL ω) := by
  simp [sampled, lift, hdD, hdI, hb]

theorem sampled_not (D I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (ω : Outcomes (V := V) L) (d : V) (hb : ω.1 d = 1) :
    d ∉ sampled D (lift I L hL ω) := by
  simp [sampled, lift, hb]

/-- Deterministic geometric part of edge survival, independent of probabilities. -/
theorem witness_survives {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c)
    {i j v : V} (hne : i ≠ j)
    (hiW : i ∈ support G D R v) (hjW : j ∈ support G D R v)
    (hii : i ∈ sampled D ω) (hjj : j ∈ sampled D ω)
    (hvlab : label G D R L ω v = some i ∨ label G D R L ω v = some j) :
    OwnerEdgeCylinder.Survives G D R L ω i j := by
  obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hiW
  obtain ⟨w, hw, hwj⟩ := Finset.mem_image.mp hjW
  have hulab : label G D R L ω u = some i := by
    have hh := label_base G D R L ω (v := u) (by simpa only [hui] using hii)
    simpa only [hui] using hh
  have hwlab : label G D R L ω w = some j := by
    have hh := label_base G D R L ω (v := w) (by simpa only [hwj] using hjj)
    simpa only [hwj] using hh
  refine ⟨hii, hjj, ?_⟩
  apply BlowupEdge.path_crosses G (label G D R L ω) hne u v w w hulab hwlab hvlab (Or.inr hwlab)
  · exact ((mem_closed G u v).mp (Finset.mem_inter.mp hu).1).elim Or.inl (fun ha => Or.inr ha.symm)
  · exact ((mem_closed G w v).mp (Finset.mem_inter.mp hw).1).elim (fun he => Or.inl he.symm) Or.inr
  · exact Or.inl rfl

theorem endpoint_owner_survives (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (ω : Outcomes (V := V) L) {i j v : V} (hne : i ≠ j)
    (hiD : i ∈ D) (hjD : j ∈ D) (hiI : i ∈ I) (hjI : j ∈ I)
    (hiW : i ∈ support G D R v) (hjW : j ∈ support G D R v)
    (hown : owner G D v = i ∨ owner G D v = j)
    (hbi : ω.1 i = 0) (hbj : ω.1 j = 0) :
    OwnerEdgeCylinder.Survives G D R L (lift I L hL ω) i j := by
  have hii := sampled_mem D I L hL ω i hiD hiI hbi
  have hjj := sampled_mem D I L hL ω j hjD hjI hbj
  apply witness_survives G D R L _ hne hiW hjW hii hjj
  rcases hown with he | he
  · left
    have hh := label_base G D R L (lift I L hL ω) (v := v) (he.symm ▸ hii)
    simpa only [he] using hh
  · right
    have hh := label_base G D R L (lift I L hL ω) (v := v) (he.symm ▸ hjj)
    simpa only [he] using hh

/-- If the old owner was not sampled, choosing either endpoint creates its edge. -/
theorem choice_survives (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (ω : Outcomes (V := V) L) {i j v : V} (hne : i ≠ j)
    (hiD : i ∈ D) (hjD : j ∈ D) (hiI : i ∈ I) (hjI : j ∈ I)
    (hiW : i ∈ support G D R v) (hjW : j ∈ support G D R v)
    (hv : v ∉ heavy G D R L) (hbi : ω.1 i = 0) (hbj : ω.1 j = 0)
    (hbo : ω.1 (owner G D v) = 1)
    (hchoice : pick G D R (lift I L hL ω) v = some i ∨ pick G D R (lift I L hL ω) v = some j) :
    OwnerEdgeCylinder.Survives G D R L (lift I L hL ω) i j := by
  have hii := sampled_mem D I L hL ω i hiD hiI hbi
  have hjj := sampled_mem D I L hL ω j hjD hjI hbj
  have hnot := sampled_not D I L hL ω (owner G D v) hbo
  apply witness_survives G D R L _ hne hiW hjW hii hjj
  rcases hchoice with he | he
  · left
    simp only [label, if_neg hnot, if_neg hv, he]
    exact if_pos hii
  · right
    simp only [label, if_neg hnot, if_neg hv, he]
    exact if_pos hjj

end Paper.SharpOwnerExperiment
