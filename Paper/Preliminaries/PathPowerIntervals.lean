import Paper.Preliminaries.IntervalBiclique
import Paper.Optimality.Treewidth.PathPowerTreewidth
import GraphTheory.SimpleGraph.Minor.Defs

namespace Paper.PathPowerIntervals
open SimpleGraph PathPowerTreewidth IntervalMinorModel
variable {n : ℕ}

/-- A connected branch cannot jump across three consecutive foreign positions. -/
theorem walk_gap {S : Set (Fin n)} {u v : S} (p : ((graph n 3).induce S).Walk u v)
    (k : ℤ) (hu : (u.val.val : ℤ) < k) (hv : k+2 < v.val.val) :
    ∃ w : S, k ≤ (w.val.val : ℤ) ∧ (w.val.val : ℤ) ≤ k+2 := by
  induction p with
  | nil => omega
  | @cons u w v huw p ih =>
    by_cases hw : k ≤ (w.val.val : ℤ)
    · refine ⟨w, hw, ?_⟩
      have hh : (w.val.val : ℤ) ≤ (u.val.val : ℤ)+3 := by exact_mod_cast huw.2.2
      omega
    · exact ih (by omega) hv

variable {A : Type} {H : SimpleGraph A}
variable (M : MinorModel H (graph n 3))

noncomputable def coordinates (a : A) : Finset ℤ :=
  (M.branchSet a).toFinset.image (fun v : Fin n => (v.val : ℤ))

theorem coordinates_nonempty (a : A) : (coordinates M a).Nonempty := by
  obtain ⟨v, hv⟩ := M.nonempty a
  exact ⟨v.val, Finset.mem_image.mpr ⟨v, Set.mem_toFinset.mpr hv, rfl⟩⟩

theorem coordinates_disjoint (a b : A) (hab : a ≠ b) : Disjoint (coordinates M a) (coordinates M b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hz
  obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hw
  have he : u = v := Fin.ext (by omega)
  have hu' : u ∈ M.branchSet a := by simpa only [Set.mem_toFinset] using hu
  have hv' : v ∈ M.branchSet b := by simpa only [Set.mem_toFinset] using hv
  exact Set.disjoint_left.mp (M.disjoint a b hab) hu' (he.symm ▸ hv')

theorem coordinates_gap (a : A) : GapConnected (coordinates M a) := by
  intro x hx y hy k hkx hky
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  let u' : M.branchSet a := ⟨u, Set.mem_toFinset.mp hu⟩
  let v' : M.branchSet a := ⟨v, Set.mem_toFinset.mp hv⟩
  obtain ⟨p⟩ := (M.connected a).preconnected u' v'
  obtain ⟨w, hwL, hwR⟩ := walk_gap p k hkx hky
  exact ⟨w.val.val, Finset.mem_image.mpr ⟨w.val, Set.mem_toFinset.mpr w.property, rfl⟩, hwL, hwR⟩

noncomputable def intervals : Model A where
  pieces := coordinates M
  nonempty := coordinates_nonempty M
  disjoint := coordinates_disjoint M
  gap := coordinates_gap M

theorem adjacent_overlap {a b : A} (hab : H.Adj a b) :
    (intervals M).low a ≤ (intervals M).high b ∧
      (intervals M).low b ≤ (intervals M).high a := by
  obtain ⟨u, hu, v, hv, huv⟩ := M.adjacent a b hab
  have hu' : (u.val : ℤ) ∈ (intervals M).pieces a :=
    Finset.mem_image.mpr ⟨u, Set.mem_toFinset.mpr hu, rfl⟩
  have hv' : (v.val : ℤ) ∈ (intervals M).pieces b :=
    Finset.mem_image.mpr ⟨v, Set.mem_toFinset.mpr hv, rfl⟩
  have hbu := (intervals M).point_bounds hu'
  have hbv := (intervals M).point_bounds hv'
  have hstep : (u.val : ℤ) ≤ (v.val : ℤ)+3 ∧ (v.val : ℤ) ≤ (u.val : ℤ)+3 := by
    exact_mod_cast huv.2
  constructor <;> omega

end Paper.PathPowerIntervals
