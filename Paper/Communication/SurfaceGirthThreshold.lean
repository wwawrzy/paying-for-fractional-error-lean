import GraphTheory.Surfaces.SignedRotationGirthDensity
import Paper.Communication.AdditiveThresholdProgram
namespace Paper.SurfaceGirthThreshold
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
theorem induced_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : SimpleGraph.SignedRotation G) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length)
    (e : ℝ) (he : (r.eulerGenus : ℝ) ≤ e) (S : Finset V) :
    (G.inducedEdgeCount S : ℝ) ≤
      ((g : ℝ)/((g : ℝ)-2))*S.card + ((g : ℝ)/((g : ℝ)-2))*e := by
  classical
  have h := SimpleGraph.SignedRotation.copy_girth_edge_bound G r
    (G.induce (S : Set V)) (SimpleGraph.Embedding.induce (G := G) (S : Set V)).toCopy
    g hg3 hg e he
  simpa [SimpleGraph.inducedEdgeCount, mul_add] using h

theorem endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : SimpleGraph.SignedRotation G) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length)
    (e : ℝ) (he : 0 ≤ e) (hr : (r.eulerGenus : ℝ) ≤ e)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G Finset.univ x) :
    let a : ℝ := (g : ℝ)/((g : ℝ)-2)
    dominates G (AdditiveThreshold.output G (1/(2*a+1)) x) ∧
    ((AdditiveThreshold.output G (1/(2*a+1)) x).card : ℝ) ≤
      (3+4/((g : ℝ)-2))*(∑ v, x v)+2*e ∧
    (AdditiveThresholdProgram.program (1/(2*a+1))).run G x =
      (fun v => decide (v ∈ AdditiveThreshold.output G (1/(2*a+1)) x)) ∧
    (AdditiveThresholdProgram.program (V := V) (1/(2*a+1))).rounds = 1 ∧
    (AdditiveThresholdProgram.program (V := V) (1/(2*a+1))).maxBits = 1 := by
  classical
  let a : ℝ := (g : ℝ)/((g : ℝ)-2)
  have hd : 0 < (g : ℝ)-2 := by exact_mod_cast (show (0 : ℤ) < (g : ℤ)-2 by omega)
  have hgp : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have ha : 0 < a := div_pos hgp hd
  have h := AdditiveThresholdProgram.endpoint G a (a*e) ha (mul_nonneg ha.le he)
    x hx (induced_density G r g hg3 hg e hr)
  have hc : 2*a+1 = 3+4/((g : ℝ)-2) := by
    dsimp [a]
    field_simp [ne_of_gt hd]
    ring
  have heq : 2*(a*e)/a = 2*e := by
    field_simp [ne_of_gt ha]
  refine ⟨h.1, ?_, h.2.2⟩
  have hb := h.2.1
  rw [heq] at hb
  calc
    _ ≤ (2*a+1)*(∑ v, x v)+2*e := hb
    _ = _ := by rw [hc]
end Paper.SurfaceGirthThreshold
#print axioms Paper.SurfaceGirthThreshold.induced_density
#print axioms Paper.SurfaceGirthThreshold.endpoint
