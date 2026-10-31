import Paper.Preliminaries.MaskRepresentatives
import Paper.Averaging.Tasks.ActiveTaskMasks

/-! Exact execution of the fixed mask loop, and actual returned candidates
preserving every demand incidence at no greater cost. -/
namespace Paper.ActiveMaskRepresentatives
open BroadcastModel MaskRepresentatives
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B T : ℕ) (l : List V) (cost : V → Fin (B + 1))
variable {b : ℕ} (C : BitCode V b)

noncomputable def answer (z : Fin T → Bool) : Option (CostTag.Tag V B) :=
  MaskedMinimum.minimum ((MaskQuery.fiber G (K.vertices) T l z).image
    (CostTag.tag cost))


theorem invariant (zs : List (Fin T → Bool)) (s : V → State V B)
    (ha : ∀ v, (s v).1.active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).1.cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).1.demands = l) :
    (∀ v, ((program C K.diameter B T zs).run G s v).1 = (s v).1) ∧
    (∀ v ∈ K.vertices,
      ((program C K.diameter B T zs).run G s v).2 = (s v).2 ++
        zs.map (answer G K B T l cost)) := by
  induction zs generalizing s with
  | nil => exact ⟨fun _ => rfl, fun _ _ => (List.append_nil _).symm⟩
  | cons z zs ih =>
    let t := (step C K.diameter B T z).run G s
    have ht : ∀ v, (t v).1 = (s v).1 := metadata G C K.diameter B T z s
    have ha' : ∀ v, (t v).1.active = decide (v ∈ K.vertices) :=
      fun v => (congrArg MaskQuery.Input.active (ht v)).trans (ha v)
    have hc' : ∀ v, (t v).1.cost = cost v :=
      fun v => (congrArg MaskQuery.Input.cost (ht v)).trans (hc v)
    have hl' : ∀ v ∈ K.vertices, (t v).1.demands = l :=
      fun v hv => (congrArg MaskQuery.Input.demands (ht v)).trans (hl v hv)
    obtain ⟨hin, hans⟩ := ih t ha' hc' hl'
    refine ⟨fun v => (hin v).trans (ht v), ?_⟩
    intro v hv
    have hq := ActiveTaskMasks.mask_query G K C B T l z cost
      (fun u => (s u).1) ha hc hl v hv
    have hhead : (t v).2 = (s v).2 ++ [answer G K B T l cost z] := by
      change ((step C K.diameter B T z).run G s v).2 = _
      rw [run_step]
      dsimp only
      rw [hq]
      rfl
    change ((program C K.diameter B T zs).run G t v).2 = _
    rw [hans v hv, hhead]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

theorem all_correct (s : V → MaskQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).demands = l) :
    ∀ v ∈ K.vertices,
      ((all C K.diameter B T).run G s v).2 =
        (patterns T).map (answer G K B T l cost) := by
  have hh := invariant G K B T l cost C (patterns T)
    (fun v => (s v, [])) ha hc hl
  intro v hv
  change ((program C K.diameter B T (patterns T)).run G (fun u => (s u, [])) v).2 = _
  simpa only [List.nil_append] using hh.2 v hv

theorem all_length (s : V → MaskQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).demands = l) :
    ∀ v ∈ K.vertices,
      (((all C K.diameter B T).run G s v).2).length = 2 ^ T := by
  intro v hv
  rw [all_correct G K B T l cost C s ha hc hl v hv,
    List.length_map, patterns_length]

theorem representative (hlen : l.length ≤ T) (s : V → MaskQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v)
    (hl : ∀ v ∈ K.vertices, (s v).demands = l)
    (v : V) (hv : v ∈ K.vertices)
    (w : V) (hw : w ∈ K.vertices) :
    ∃ u ∈ K.vertices,
      some (CostTag.tag cost u) ∈ ((all C K.diameter B T).run G s v).2 ∧
      SevenFoundation.closed G u ∩ l.toFinset = SevenFoundation.closed G w ∩ l.toFinset ∧
      (cost u).val ≤ (cost w).val := by
  let z := LocalDemandMask.mask T l w (G.neighborFinset w)
  have hwf : w ∈ MaskQuery.fiber G (K.vertices) T l z :=
    Finset.mem_filter.mpr ⟨hw, rfl⟩
  have him : CostTag.tag cost w ∈
      (MaskQuery.fiber G (K.vertices) T l z).image (CostTag.tag cost) :=
    Finset.mem_image.mpr ⟨w, hwf, rfl⟩
  obtain ⟨t, ht, hle⟩ := MaskedMinimum.minimum_le him
  obtain ⟨⟨u, hu, he⟩, _⟩ := TaggedMinimum.least
    (MaskQuery.fiber G (K.vertices) T l z) (CostTag.tag cost) ht
  subst t
  have hmem : some (CostTag.tag cost u) ∈ ((all C K.diameter B T).run G s v).2 := by
    rw [all_correct G K B T l cost C s ha hc hl v hv]
    exact List.mem_map.mpr ⟨z, patterns_complete T z, ht⟩
  refine ⟨u, (Finset.mem_filter.mp hu).1, hmem, ?_, ?_⟩
  · exact (LocalDemandMask.signature_iff G T l hlen u w).mp (Finset.mem_filter.mp hu).2
  · exact Prod.Lex.monotone_fst _ _ hle

end Paper.ActiveMaskRepresentatives
