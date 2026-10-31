import Paper.Preliminaries.PathPowerThreePlanar
import Paper.Preliminaries.PathPowerTotalGeometry
namespace Paper.OddPathPower

def graph (n t : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (PathPowerTreewidth.graph n t).Adj u v ∧ u.val%2 ≠ v.val%2
  symm := by intro u v h; exact ⟨h.1.symm,Ne.symm h.2⟩
  loopless := ⟨fun v h => h.2 rfl⟩
instance (n t : ℕ) : DecidableRel (graph n t).Adj := by
  unfold graph
  infer_instance

theorem subgraph (n t : ℕ) : graph n t ≤ PathPowerTreewidth.graph n t := fun _ _ h => h.1

theorem planar (n : ℕ) : (graph n 3).IsPlanar := (PathPowerThreePlanar.isPlanar n).mono (subgraph n 3)

theorem walk_parity {n t : ℕ} {u v : Fin n} (p : (graph n t).Walk u v) :
    (u.val+p.length)%2=v.val%2 := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hp := h.2
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem girth_four {n t : ℕ} (u : Fin n) (p : (graph n t).Walk u u) (hp : p.IsCycle) : 4 ≤ p.length := by
  have h3 := hp.three_le_length
  have hpar := walk_parity p
  omega
end Paper.OddPathPower
#print axioms Paper.OddPathPower.planar
#print axioms Paper.OddPathPower.girth_four
