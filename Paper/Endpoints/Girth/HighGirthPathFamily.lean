import Paper.Optimality.LowerBounds.TreewidthLocalLower
import Paper.Preliminaries.PathPowerThreePlanar

/-! The first path-power lower-bound witnesses are genuine finite paths,
hence planar and of every finite girth. -/
namespace Paper.HighGirthPathFamily
open SimpleGraph PathPowerTreewidth

theorem first_power_eq_path (n : Nat) : graph n 1 = pathGraph n := by
  ext u v
  change (u ≠ v ∧ u.val ≤ v.val + 1 ∧ v.val ≤ u.val + 1) ↔ _
  rw [pathGraph_adj]
  constructor
  · rintro ⟨hne,h1,h2⟩
    have hv : u.val ≠ v.val := fun he => hne (Fin.ext he)
    omega
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro he
      subst v
      omega
    · omega
    · omega

theorem acyclic (n : Nat) : (graph n 1).IsAcyclic := by
  rw [first_power_eq_path]
  exact PathGraphTree.acyclic n

theorem planar (n : Nat) : (graph n 1).IsPlanar := by
  apply (PathPowerThreePlanar.isPlanar n).mono
  intro u v h
  exact ⟨h.1, by have hh := h.2.1; omega, by have hh := h.2.2; omega⟩

theorem girth (n g : Nat) (v : Fin n) (w : (graph n 1).Walk v v) (hw : w.IsCycle) :
    g ≤ w.length := by
  exact False.elim (acyclic n w hw)

end Paper.HighGirthPathFamily
#print axioms Paper.HighGirthPathFamily.first_power_eq_path
#print axioms Paper.HighGirthPathFamily.acyclic
#print axioms Paper.HighGirthPathFamily.planar
#print axioms Paper.HighGirthPathFamily.girth
