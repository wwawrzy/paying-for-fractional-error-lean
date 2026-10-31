import Paper.Solver.LocalSearch.GeneralCoveringSearchInvariant
import Paper.Solver.LocalSearch.GeneralCoveringNormalizedFractional

/-! Exact equality of the actual normalized fractional client on two
physical graphs with the same active induced graph. Demand-bit acquisition
is compared through the original private incidences, not assumed equal. -/
namespace Paper.GeneralCoveringFractionalInvariant
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G J : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel J.Adj]

theorem normalization (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hG : ∀ r ∈ R, cover r ⊆ closed G r) (hJ : ∀ r ∈ R, cover r ⊆ closed J r)
    {B : ℕ} (hB : 1 ≤ B) (s : V → GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (ht : ∀ v, (s v).targets = targets v) :
    (GeneralCoveringInputNormalization.program B hB).runEncoded G s =
      (GeneralCoveringInputNormalization.program B hB).runEncoded J s := by
  funext v
  rw [GeneralCoveringInputNormalization.run_program, GeneralCoveringInputNormalization.run_program]
  dsimp only [GeneralCoveringInputNormalization.update]
  rw [GeneralCoveringInputNormalization.retainedTargets_eq G cover targets R hinc hG s hd ht v,
    GeneralCoveringInputNormalization.retainedTargets_eq J cover targets R hinc hJ s hd ht v]

theorem fractional (K : ActiveTask.Context G) (L : ActiveTask.Context J)
    (hvertices : K.vertices = L.vertices)
    (hgraph : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, G.Adj u v ↔ J.Adj u v)
    {bits : ℕ} (ids : BitCode V bits) (a B q M : ℕ)
    (s : V → GeneralCoveringFractional.Input V B)
    (ha : ∀ u, (s u).active = decide (u ∈ K.vertices))
    (hz : ∀ u, u ∉ K.vertices → (s u).demand = false) :
    (GeneralCoveringFractional.program ids K.diameter a B q M).runEncoded G s =
      (GeneralCoveringFractional.program ids L.diameter a B q M).runEncoded J s := by
  simp only [Program.runEncoded_eq_run]
  funext v
  rw [GeneralCoveringFractional.run_program, GeneralCoveringFractional.run_program]
  by_cases hv : v ∈ K.vertices
  · simp only [ha v, decide_eq_true hv, if_true]
    apply congrArg (GeneralCoveringFractional.count M v)
    apply GeneralCoveringSearchInvariant.run G J K L hvertices hgraph ids a B q M
      (fun u => GeneralCoveringFractional.searchInput q (s u)) ha _ v hv
    intro u hu
    simp only [GeneralCoveringFractional.searchInput, hz u hu, Bool.false_eq_true, ↓reduceIte]
  · simp only [ha v, decide_eq_false hv, Bool.false_eq_true, if_false]

theorem normalized (K : ActiveTask.Context G) (L : ActiveTask.Context J)
    (hvertices : K.vertices = L.vertices)
    (hgraph : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, G.Adj u v ↔ J.Adj u v)
    (cover targets : V → Finset V) (R : Finset V) (hR : R ⊆ K.vertices)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hG : ∀ r ∈ R, cover r ⊆ closed G r) (hJ : ∀ r ∈ R, cover r ⊆ closed J r)
    {bits : ℕ} (ids : BitCode V bits) (a B q M : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringFractional.Input V B)
    (ha : ∀ u, (s u).active = decide (u ∈ K.vertices))
    (hd : ∀ u, (s u).demand = decide (u ∈ R))
    (ht : ∀ u, (s u).targets = targets u) :
    (GeneralCoveringNormalizedFractional.program ids K.diameter a B q M hB).runEncoded G s =
      (GeneralCoveringNormalizedFractional.program ids L.diameter a B q M hB).runEncoded J s := by
  rw [GeneralCoveringNormalizedFractional.run_program, GeneralCoveringNormalizedFractional.run_program]
  have hn := normalization G J cover targets R hinc hG hJ hB s hd ht
  change GeneralCoveringNormalizedFractional.normalized G B hB s =
    GeneralCoveringNormalizedFractional.normalized J B hB s at hn
  rw [← hn]
  apply fractional G J K L hvertices hgraph ids a B q M
  · intro u
    exact (GeneralCoveringInputNormalization.metadata G B hB s u).1.trans (ha u)
  · intro u hu
    exact (GeneralCoveringInputNormalization.metadata G B hB s u).2.trans
      ((hd u).trans (decide_eq_false (fun hr => hu (hR hr))))

end Paper.GeneralCoveringFractionalInvariant

#print axioms Paper.GeneralCoveringFractionalInvariant.normalization
#print axioms Paper.GeneralCoveringFractionalInvariant.fractional
#print axioms Paper.GeneralCoveringFractionalInvariant.normalized
