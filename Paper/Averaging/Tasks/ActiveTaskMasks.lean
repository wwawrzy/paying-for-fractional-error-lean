import Paper.Averaging.Tasks.ActiveTaskContext
import Paper.Preliminaries.MaskQuery

/-! Actual cost/ID minima and incidence-mask queries for arbitrary active
task geometry. Scalar broadcast programs remain the existing ones. -/
namespace Paper.ActiveTaskMasks
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (K : ActiveTask.Context G)

theorem taggedMinimum {U : Type} [LinearOrder U] {b c : ℕ} (C : BitCode V b) (F : BitCode U c)
    (S : Finset V) (hS : S ⊆ K.vertices) (tag : V → U) (hinj : Function.Injective tag) :
    ∀ v ∈ K.vertices, (((TaggedMinimum.program C F K.diameter).run G
      (fun u => (decide (u ∈ K.vertices), if u ∈ S then MinimumPayload.singleton (tag u) else 0)) v).2.map
        MinimumPayload.Data.value) = some (MaskedMinimum.minimum (S.image tag)) := by
  have hz : ∀ u, u ∉ K.vertices →
      (if u ∈ S then MinimumPayload.singleton (tag u) else (0 : MinimumPayload.Data U)) = 0 := by
    intro u hu
    exact if_neg (fun h => hu (hS h))
  intro v hv
  have hres := ActiveTaskQueries.allReduce G C (MinimumPayload.code F) K.vertices K.nonempty K.diameter K.paths
    (fun u => if u ∈ S then MinimumPayload.singleton (tag u) else 0) hz v hv
  change ((TaskAllReduce.program C (MinimumPayload.code F) K.diameter).run G _ v).2.map _ = _
  rw [hres, Option.map_some, TaggedMinimum.sum_selected S tag hinj]
  rfl

theorem mask_query {b : ℕ} (C : BitCode V b) (B T : ℕ) (l : List V) (z : Fin T → Bool)
    (cost : V → Fin (B + 1)) (s : V → MaskQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices)) (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).demands = l) : ∀ v ∈ K.vertices,
      ((MaskQuery.program C K.diameter B T z).run G s v).2 =
        MaskedMinimum.minimum ((MaskQuery.fiber G K.vertices T l z).image (CostTag.tag cost)) := by
  intro v hv
  have hi := MaskQuery.input_eq G K.vertices B T l z cost s ha hc hl
  have hres := taggedMinimum G K C (CostTag.code C B) (MaskQuery.fiber G K.vertices T l z)
    (Finset.filter_subset _ _) (CostTag.tag cost) (CostTag.injective cost) v hv
  rw [MaskQuery.run_program, hi]
  dsimp only
  rw [hres]
  rfl
end Paper.ActiveTaskMasks
