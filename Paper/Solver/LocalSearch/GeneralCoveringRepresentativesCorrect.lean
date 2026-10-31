import Paper.Solver.LocalSearch.GeneralCoveringRepresentatives
import Paper.Averaging.Tasks.ActiveTaskMasks

/-! Exact execution of the fixed mask loop, and actual returned candidates
preserving every demand incidence at no greater cost. -/
namespace Paper.GeneralCoveringRepresentativesCorrect
open BroadcastModel GeneralCoveringRepresentatives
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B T : ℕ) (l : List V) (targets : V → Finset V) (cost : V → Fin (B + 1))
variable {b : ℕ} (C : BitCode V b)

noncomputable def answer (z : Fin T → Bool) : Option (CostTag.Tag V B) :=
  MaskedMinimum.minimum ((GeneralCoveringQuery.fiber K.vertices T l targets z).image
    (CostTag.tag cost))


theorem invariant (zs : List (Fin T → Bool)) (s : V → State V B)
    (ha : ∀ v, (s v).1.active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).1.cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).1.demands = l)
    (htarget : ∀ v ∈ K.vertices, (s v).1.targets = targets v) :
    (∀ v, ((program C K.diameter B T zs).run G s v).1 = (s v).1) ∧
    (∀ v ∈ K.vertices,
      ((program C K.diameter B T zs).run G s v).2 = (s v).2 ++
        zs.map (answer G K B T l targets cost)) := by
  induction zs generalizing s with
  | nil => exact ⟨fun _ => rfl, fun _ _ => (List.append_nil _).symm⟩
  | cons z zs ih =>
    let t := (step C K.diameter B T z).run G s
    have ht : ∀ v, (t v).1 = (s v).1 := metadata G C K.diameter B T z s
    have ha' : ∀ v, (t v).1.active = decide (v ∈ K.vertices) :=
      fun v => (congrArg GeneralCoveringQuery.Input.active (ht v)).trans (ha v)
    have hc' : ∀ v, (t v).1.cost = cost v :=
      fun v => (congrArg GeneralCoveringQuery.Input.cost (ht v)).trans (hc v)
    have hl' : ∀ v ∈ K.vertices, (t v).1.demands = l :=
      fun v hv => (congrArg GeneralCoveringQuery.Input.demands (ht v)).trans (hl v hv)
    have ht' : ∀ v ∈ K.vertices, (t v).1.targets = targets v :=
      fun v hv => (congrArg GeneralCoveringQuery.Input.targets (ht v)).trans (htarget v hv)
    obtain ⟨hin, hans⟩ := ih t ha' hc' hl' ht'
    refine ⟨fun v => (hin v).trans (ht v), ?_⟩
    intro v hv
    have hq := GeneralCoveringQuery.active_task G K C B T l targets z cost
      (fun u => (s u).1) ha hc hl htarget v hv
    have hhead : (t v).2 = (s v).2 ++ [answer G K B T l targets cost z] := by
      change ((step C K.diameter B T z).run G s v).2 = _
      rw [run_step]
      dsimp only
      rw [hq]
      rfl
    change ((program C K.diameter B T zs).run G t v).2 = _
    rw [hans v hv, hhead]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

theorem all_correct (s : V → GeneralCoveringQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).demands = l)
    (htarget : ∀ v ∈ K.vertices, (s v).targets = targets v) :
    ∀ v ∈ K.vertices,
      ((all C K.diameter B T).run G s v).2 =
        (patterns T).map (answer G K B T l targets cost) := by
  have hh := invariant G K B T l targets cost C (patterns T)
    (fun v => (s v, [])) ha hc hl htarget
  intro v hv
  change ((program C K.diameter B T (patterns T)).run G (fun u => (s u, [])) v).2 = _
  simpa only [List.nil_append] using hh.2 v hv


end Paper.GeneralCoveringRepresentativesCorrect
