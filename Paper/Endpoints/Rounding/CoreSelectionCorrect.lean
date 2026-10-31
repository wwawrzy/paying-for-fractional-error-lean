import Paper.Endpoints.Rounding.CoreSelectionBroadcast
import Paper.Preliminaries.BoundedLists

/-! Exact physical execution of the recursive bounded-list cover. Every
derived list stays inside an original hosted list, so two-hop bit reports
are sufficient for every rank level, without a degree bound or oracle. -/
namespace Paper.CoreSelectionCorrect
open BroadcastModel SevenFoundation CoreSelectionBroadcast
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem hierarchy_known (lists : V → Finset V) (hlocal : ∀ u, lists u ⊆ closed G u)
    (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (S : Finset V) (v : V) :
    ∀ t ∈ IncidentHierarchy.incident (IncidentHierarchy.globalLevel (ListIncidenceBroadcast.family lists) q n) v,
      ∀ u ∈ t, u ∈ CohostKnown.known G lists S v ↔ u ∈ S := by
  intro t ht u hu
  have hmem := Finset.mem_filter.mp ht
  obtain ⟨original, horiginal, hsub⟩ := IncidentHierarchy.subset_original
    (ListIncidenceBroadcast.family lists) q hq n t hmem.1
  obtain ⟨_, host, he⟩ := (ListIncidenceBroadcast.mem_family lists original).mp horiginal
  rw [← he] at hsub
  exact CohostKnown.cohost_agrees G lists hlocal S v host u (hsub hmem.2) (hsub hu)

theorem step_correct {b : ℕ} (C : BitCode V b) (f q n : ℕ) (hq : 2 ≤ q)
    (lists : V → Finset V) (hbound : ∀ u, (lists u).card ≤ f)
    (hlocal : ∀ u, lists u ⊆ closed G u) (S : Finset V) (s : V → State V)
    (hown : ∀ v, (s v).ownList = lists v)
    (hincident : ∀ v, (s v).incident = IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v)
    (hselected : ∀ v, (s v).selected = decide (v ∈ S)) (v : V) :
    ((step C f q n).run G s v).selected =
      decide (v ∈ ListPhase.phase (IncidentHierarchy.globalLevel (ListIncidenceBroadcast.family lists) q n) S) := by
  have hin : (fun u => ((s u).ownList, (s u).selected)) = fun u => (lists u, decide (u ∈ S)) := by
    funext u
    rw [hown u, hselected u]
  rw [run_step]
  dsimp only
  rw [hin, CohostKnown.correct G C f lists hbound hlocal S, hincident v, hselected v,
    IncidentHierarchy.local_global _ q hq v n]
  have hh := IncidentPhase.correct
    (IncidentHierarchy.globalLevel (ListIncidenceBroadcast.family lists) q n) S
    (CohostKnown.known G lists S v) v
  have hinst : (fun x y : V => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hh
  exact hh (hierarchy_known G lists hlocal q hq n S v)

set_option maxHeartbeats 1000000 in
theorem body_correct {b : ℕ} (C : BitCode V b) (f q : ℕ) (hq : 2 ≤ q)
    (lists : V → Finset V) (hbound : ∀ u, (lists u).card ≤ f)
    (hlocal : ∀ u, lists u ⊆ closed G u) (n j : ℕ) (s : V → State V)
    (hown : ∀ v, (s v).ownList = lists v)
    (hincident : ∀ v, (s v).incident = IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v) :
    ∀ v, ((body C f q n j).run G s v).selected =
      decide (v ∈ BoundedLists.cover (IncidentHierarchy.globalLevel (ListIncidenceBroadcast.family lists) q n) q j) := by
  induction j generalizing n s with
  | zero => intro v; simp only [body, Program.run, BoundedLists.cover, Finset.notMem_empty, decide_false]
  | succ j ih =>
    let t := (body C f q (n + 1) j).run G s
    have hm := body_metadata G C f q (n + 1) j s
    have ht0 : ∀ v, (t v).ownList = lists v := fun v => (hm v).1.trans (hown v)
    have ht1 : ∀ v, (t v).incident = IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v :=
      fun v => (hm v).2.trans (hincident v)
    have ht2 := ih (n + 1) s hown hincident
    intro v
    change ((step C f q n).run G t v).selected = _
    have hh := step_correct G C f q n hq lists hbound hlocal
      (BoundedLists.cover (IncidentHierarchy.globalLevel (ListIncidenceBroadcast.family lists) q (n + 1)) q j)
      t ht0 ht1 ht2 v
    rw [BoundedLists.cover]
    have he : IncidentHierarchy.globalLevel (ListIncidenceBroadcast.family lists) q (n + 1) =
        CoreHierarchy.cores (IncidentHierarchy.globalLevel (ListIncidenceBroadcast.family lists) q n) q :=
      ComputableCores.eq_cores _ q hq
    rw [he] at hh
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst]
    exact hh

theorem correct {b : ℕ} (C : BitCode V b) (f q : ℕ) (hq : 2 ≤ q)
    (lists : V → Finset V) (hbound : ∀ u, (lists u).card ≤ f)
    (hlocal : ∀ u, lists u ⊆ closed G u) :
    (program C f q).run G lists = fun v => decide (v ∈ BoundedLists.cover (ListIncidenceBroadcast.family lists) q f) := by
  let raw := (ProgramMemory.carry (ListIncidenceBroadcast.program C f)).run G (fun u => (lists u, lists u))
  change (fun v => ((body C f q 0 f).run G (initializeState.run G raw) v).selected) = _
  have hraw : raw = fun u => ((ListIncidenceBroadcast.program C f).run G lists u, lists u) :=
    ProgramMemory.run G (ListIncidenceBroadcast.program C f) lists lists
  rw [hraw]
  have hg : (ListIncidenceBroadcast.program C f).run G lists =
      fun v => IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) v :=
    funext (ListIncidenceBroadcast.correct G C f lists hbound hlocal)
  rw [hg]
  funext v
  exact body_correct G C f q hq lists hbound hlocal 0 f
    (fun u => ⟨lists u, IncidentHierarchy.incident (ListIncidenceBroadcast.family lists) u, false⟩)
    (fun _ => rfl) (fun _ => rfl) v
end Paper.CoreSelectionCorrect
