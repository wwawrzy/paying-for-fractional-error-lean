import GraphTheory.Surfaces.OrdinarySurface
import Paper.Endpoints.Rounding.SurfaceRotationDensityClass
import GraphTheory.Surfaces.SignedRotationGirthDensity
namespace Paper.OrdinarySurfaceBounds
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
theorem minor_bound (G : SimpleGraph V) [DecidableRel G.Adj] (e : ℕ)
    (h : SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e) :
    SurfaceRounding.MinorBound G (e : ℝ) := by
  obtain ⟨r,hr⟩ := SimpleGraph.OrdinarySurface.signedRotation_real G e h
  exact SurfaceRounding.minorBound_of_signedRotation G r (e : ℝ) hr

theorem minor_density (G : SimpleGraph V) [DecidableRel G.Adj] (e : ℕ)
    (h : SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e) :
    MinorDensity.Bound G (3+3*(e : ℝ)) := by
  obtain ⟨r,hr⟩ := SimpleGraph.OrdinarySurface.signedRotation_real G e h
  exact SurfaceRounding.minorDensity_of_signedRotation G r (e : ℝ) (Nat.cast_nonneg e) hr

theorem subgraph_girth_density {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ℕ)
    (h : SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e)
    (F : SimpleGraph W) [DecidableRel F.Adj] (f : SimpleGraph.Copy F G)
    (g : ℕ) (hg : 3 ≤ g)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    (F.edgeFinset.card : ℝ) ≤ (g : ℝ)/((g : ℝ)-2)*Fintype.card W +
      (g : ℝ)/((g : ℝ)-2)*(e : ℝ) := by
  obtain ⟨r,hr⟩ := SimpleGraph.OrdinarySurface.signedRotation_real G e h
  simpa only [mul_add] using
    SimpleGraph.SignedRotation.copy_girth_edge_bound G r F f g hg hgirth (e : ℝ) hr

theorem subgraph_density {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ℕ)
    (h : SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e)
    (F : SimpleGraph W) [DecidableRel F.Adj] (f : SimpleGraph.Copy F G) :
    (F.edgeFinset.card : ℝ) ≤ 3*Fintype.card W+3*(e : ℝ) := by
  have hh := subgraph_girth_density G e h F f 3 (by norm_num)
    (fun _ _ hc => hc.three_le_length)
  norm_num at hh
  exact hh

variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ)
variable (hx : feasible (CurrentBudget.auxiliary G 6) x)
variable (hcap : ∀ v ∈ CurrentBudget.candidates G 6, x v ≤ 1)
local notation "I" => CurrentCounting.input G 3 6 (by norm_num) x hx hcap
local notation "W" => CurrentRounding.first G 3 I
local notation "L" => CurrentRounding.middle G 3 I
theorem actual_bounds (e : ℕ) (h : SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e) :
    ((W).card+(L).card:ℝ)/4+CurrentRounding.slack G 3 I-3/2*e ≤
      CurrentRounding.objective G 3 I-(CurrentRounding.output G 3 I).card ∧
    ((CurrentRounding.output G 3 I).card:ℝ) ≤ 49*((W).card+(L).card)+294*CurrentRounding.slack G 3 I+99/2*e ∧
    (1+1/294:ℝ)*(CurrentRounding.output G 3 I).card ≤ CurrentRounding.objective G 3 I+2*e := by
  exact SurfaceRounding.actual_bounds G x hx hcap (e : ℝ) (Nat.cast_nonneg e) (minor_bound G e h)
end Paper.OrdinarySurfaceBounds
#print axioms Paper.OrdinarySurfaceBounds.minor_bound
#print axioms Paper.OrdinarySurfaceBounds.minor_density
#print axioms Paper.OrdinarySurfaceBounds.subgraph_girth_density
#print axioms Paper.OrdinarySurfaceBounds.actual_bounds
#print axioms Paper.OrdinarySurfaceBounds.subgraph_density
