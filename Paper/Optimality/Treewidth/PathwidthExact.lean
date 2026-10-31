import Paper.Optimality.Treewidth.Pathwidth
import Paper.Optimality.Treewidth.CliqueMinor

/-! Exact widths of the path-power witnesses: the consecutive first r+1
vertices give an actual complete minor, matching the proved path decomposition. -/
namespace Paper.PathwidthExact

open SimpleGraph PathPowerTreewidth

theorem clique_minor (n r : ℕ) (hfit : r + 1 ≤ n) :
    (completeGraph (Fin (r + 1))).IsMinor (graph n r) := by
  let f : Fin (r + 1) → Fin n := Fin.castLE hfit
  have hinj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact congrArg (fun v : Fin n => v.val) he
  refine ⟨{
    branchSet := fun i => {f i}
    nonempty := fun _ => Set.singleton_nonempty _
    disjoint := fun i j hij => by
      rw [Set.disjoint_singleton]
      exact fun he => hij (hinj he)
    connected := fun i => (MinorModel.refl (graph n r)).connected (f i)
    adjacent := ?_ }⟩
  intro i j hij
  refine ⟨f i, rfl, f j, rfl, ?_⟩
  refine ⟨fun he => hij.ne (hinj he), ?_, ?_⟩
  · have hi := i.isLt
    change i.val ≤ j.val + r
    omega
  · have hj := j.isLt
    change j.val ≤ i.val + r
    omega

theorem treeWidth (n r : ℕ) (hfit : r + 1 ≤ n) : (graph n r).treeWidth = r := by
  apply Nat.le_antisymm (PathPowerTreewidth.treeWidth_le n r)
  by_contra h
  exact CliqueMinorTreewidth.excluded (G := graph n r) le_rfl
    (h := r + 1) (by omega) (clique_minor n r hfit)

theorem pathwidth (n r : ℕ) (hfit : r + 1 ≤ n) : Pathwidth.width (graph n r) = r := by
  apply Nat.le_antisymm (Pathwidth.pathPower_width n r)
  exact (treeWidth n r hfit).symm.le.trans Pathwidth.treeWidth_le_width

end Paper.PathwidthExact

#print axioms Paper.PathwidthExact.treeWidth
#print axioms Paper.PathwidthExact.pathwidth
