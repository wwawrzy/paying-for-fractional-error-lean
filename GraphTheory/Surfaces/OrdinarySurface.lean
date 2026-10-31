import Paper.External.SurfaceTopology
/-! Euler genus of genuine closed surfaces, independent of selected cellulation.
Extraction uses reviewed inputs A and C; the interpretation of genus also relies
on reviewed invariance B, recorded separately by eulerGenus_eq. -/
namespace SimpleGraph.OrdinarySurface
noncomputable def ClosedSurface.selectedCellulation {S : Type} [TopologicalSpace S]
    (s : ClosedSurface S) : Cellulation S :=
  Classical.choice (Paper.External.SurfaceTopology.exists_cellulation s)
noncomputable def ClosedSurface.eulerGenus {S : Type} [TopologicalSpace S]
    (s : ClosedSurface S) : ℤ := 2-s.selectedCellulation.eulerCharacteristic

theorem ClosedSurface.eulerGenus_eq {S : Type} [TopologicalSpace S]
    (s : ClosedSurface S) (c : Cellulation S) : s.eulerGenus = 2-c.eulerCharacteristic := by
  unfold ClosedSurface.eulerGenus
  rw [Paper.External.SurfaceTopology.cellulation_euler_eq s s.selectedCellulation c]

def HasEulerGenusAtMost {V : Type} (G : SimpleGraph V) (e : ℕ) : Prop :=
  ∃ (S : Type) (_ : TopologicalSpace S) (s : ClosedSurface S),
    TopologicalRealization.EmbedsInto G S ∧ s.eulerGenus ≤ (e : ℤ)

theorem signedRotation_of_genus {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ℕ) (h : HasEulerGenusAtMost G e) :
    ∃ r : SignedRotation G, r.eulerGenus ≤ (e : ℤ) := by
  obtain ⟨S,topo,s,hemb,hgen⟩ := h
  obtain ⟨r,hr⟩ := Paper.External.SurfaceTopology.rotation_of_embedding G s s.selectedCellulation hemb
  exact ⟨r,hr.trans hgen⟩

theorem signedRotation_real {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ℕ) (h : HasEulerGenusAtMost G e) :
    ∃ r : SignedRotation G, (r.eulerGenus : ℝ) ≤ (e : ℝ) := by
  obtain ⟨r,hr⟩ := signedRotation_of_genus G e h
  exact ⟨r,by exact_mod_cast hr⟩
end SimpleGraph.OrdinarySurface
#print axioms SimpleGraph.OrdinarySurface.signedRotation_of_genus
#print axioms SimpleGraph.OrdinarySurface.ClosedSurface.eulerGenus_eq
