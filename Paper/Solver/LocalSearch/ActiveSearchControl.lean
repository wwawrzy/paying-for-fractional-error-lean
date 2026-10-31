import Paper.Solver.LocalSearch.SearchControl
import Paper.Owners.Construction.ActiveHeavyListing
import Paper.Preliminaries.ActiveDemandValues
import Paper.Solver.LocalSearch.ActiveSearchCount

/-! Exact shared branch-control output, including actual costs of the
returned heavy IDs. Its bounded shape holds even outside the large case. -/
namespace Paper.ActiveSearchControl
open BroadcastModel SearchControl
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (a B q m : ℕ)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → TerminalProtocol.Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
include ha hc hb

theorem heavy_chosen (v : V) (hv : v ∈ K.vertices) :
    (heavyStates G C K.diameter a B q m s v).chosen = HeavyListShape.initialList G
      (K.vertices)
      (TerminalProtocolCorrect.demands (K.vertices) multiplicity) a m := by
  let H := K.vertices
  let A := TerminalProtocolCorrect.demands H multiplicity
  have hi : (fun u => heavyInput (s u)) = fun u => (decide (u ∈ H), decide (u ∈ A)) := by
    funext u
    dsimp only [heavyInput]
    rw [ha u, hb u]
    simp [A, H, TerminalProtocolCorrect.demands]
  change ((HeavyListing.program C K.diameter a m).run G (fun u => heavyInput (s u)) v).chosen = _
  rw [hi]
  exact ActiveHeavyListing.chosen G K C A (Finset.filter_subset _ _) a m v hv

theorem result (v : V) (hv : v ∈ K.vertices) :
    (program C K.diameter a B q m).run G s v =
      ⟨decide (2 * (a + 1) * m ≤
          (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card),
        (HeavyListShape.initialList G (K.vertices)
          (TerminalProtocolCorrect.demands (K.vertices) multiplicity) a m).map
            (CostTag.tag cost)⟩ := by
  let H := K.vertices
  let A := TerminalProtocolCorrect.demands H multiplicity
  let l := HeavyListShape.initialList G H A a m
  have hl : ∀ u ∈ H, (costInputs G C K.diameter a B q m s u).demands = l :=
    heavy_chosen G K a B q m cost multiplicity C s ha hc hb
  have hlist : ∀ r ∈ l, r ∈ H := fun r hr => (HeavyListShape.subset G H A a m hr).1
  have hcost := ActiveDemandValues.correct G K C B (2 * a * m) l cost
    (costInputs G C K.diameter a B q m s) ha hc hl hlist v hv
  rw [run_program]
  dsimp only
  rw [ActiveSearchCount.correct G K B q multiplicity C s ha hb v hv,
    hcost, heavy_chosen G K a B q m cost multiplicity C s ha hc hb v hv]
  change (⟨decide (2 * (a + 1) * m ≤ A.card),
    ListedCosts.tags B (2 * a * m) l (DemandValues.values (2 * a * m) l cost)⟩ : Output V B) =
      ⟨decide (2 * (a + 1) * m ≤ A.card), l.map (CostTag.tag cost)⟩
  rw [ListedCosts.correct B (2 * a * m) l (HeavyListShape.length G H A a m) cost]

theorem candidates_length (v : V) (hv : v ∈ K.vertices) :
    ((program C K.diameter a B q m).run G s v).candidates.length ≤ 2 * a * m := by
  rw [result G K a B q m cost multiplicity C s ha hc hb v hv]
  simpa only [List.length_map] using HeavyListShape.length G (K.vertices)
    (TerminalProtocolCorrect.demands (K.vertices) multiplicity) a m

theorem consistent (v : V) (hv : v ∈ K.vertices) :
    SolutionWord.Consistent cost ((program C K.diameter a B q m).run G s v).candidates := by
  rw [result G K a B q m cost multiplicity C s ha hc hb v hv]
  intro t ht
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
  rfl

theorem support (v : V) (hv : v ∈ K.vertices) :
    ∀ t ∈ ((program C K.diameter a B q m).run G s v).candidates,
      SolutionWord.id t ∈ K.vertices := by
  rw [result G K a B q m cost multiplicity C s ha hc hb v hv]
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact (HeavyListShape.subset G _ _ a m hu).1

theorem uniform (v w : V) (hv : v ∈ K.vertices)
    (hw : w ∈ K.vertices) :
    (program C K.diameter a B q m).run G s v = (program C K.diameter a B q m).run G s w := by
  rw [result G K a B q m cost multiplicity C s ha hc hb v hv,
    result G K a B q m cost multiplicity C s ha hc hb w hw]

theorem contains_heavy (ha' : 1 ≤ a) (hm : 1 ≤ m) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (hlarge : 2 * (a + 1) * m ≤
      (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card)
    (v : V) (hv : v ∈ K.vertices) (u : V)
    (hu : u ∈ K.vertices)
    (hheavy : u ∈ LocalSearchBounds.heavy G
      (TerminalProtocolCorrect.demands (K.vertices) multiplicity) m) :
    CostTag.tag cost u ∈ ((program C K.diameter a B q m).run G s v).candidates := by
  rw [result G K a B q m cost multiplicity C s ha hc hb v hv]
  apply List.mem_map.mpr
  refine ⟨u, ?_, rfl⟩
  apply List.mem_toFinset.mp
  rw [HeavyListShape.complete G _ _ a m ha' hm hden hlarge]
  exact Finset.mem_inter.mpr ⟨hu, hheavy⟩
end Paper.ActiveSearchControl
