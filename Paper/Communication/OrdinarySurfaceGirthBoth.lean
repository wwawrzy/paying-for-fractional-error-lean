import Paper.Communication.OrdinarySurfaceImprovedGirth
namespace Paper.OrdinarySurfaceGirthBoth
open BroadcastModel SevenFoundation ImprovedExcessSolver
theorem coefficient_le_basic (g : ℕ) (hg : 5 ≤ g) (hne : g ≠ 6) :
    ImprovedGirth.limitingCoefficient g ≤ 3+4/((g : ℝ)-2) := by
  let a := NoncriticalGirth.density g
  have ha : 1 ≤ a := (NoncriticalGirth.density_bounds g (by omega)).1
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨hzero,hone⟩ := ImprovedExcessEndpoint.gap_bounds a ha
    (NoncriticalGirth.density_noninteger g hg hne)
  have hm := ImprovedExcess.muMax_pos (a : ℝ) (ImprovedExcessEndpoint.gap a) haR hzero hone
  have hd : 0 < (g : ℝ)-2 := by exact_mod_cast (show (0 : ℤ) < (g : ℤ)-2 by omega)
  have heq : 2*(a : ℝ)+1 = 3+4/((g : ℝ)-2) := by
    dsimp [a]
    rw [NoncriticalGirth.density_cast]
    field_simp [ne_of_gt hd]
    ring
  change 2*(a : ℝ)+1-ImprovedExcess.muMax (a : ℝ) (ImprovedExcessEndpoint.gap a) ≤ _
  rw [← heq]
  linarith
theorem parameters (e : ℕ) (g : ℕ) (hg : 5 ≤ g) (hne : g ≠ 6)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Config (NoncriticalGirth.density g), ∃ K : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {b : ℕ} (C : BitCode V b),
      let a := Nat.ceil (3+3*(e : ℝ))
      let R := OrdinaryAbsorption.portProgram C a K (ImprovedExcessSolver.program C p)
      (∀ ports : PortBroadcastModel.Numbering G,
        let Z := Finset.univ.filter (fun v => R.runEncoded G ports (fun _ => ()) v = true)
        dominates G Z ∧ ∀ Y : Finset V, dominates G Y →
          (Z.card : ℝ) ≤ (ImprovedGirth.limitingCoefficient g+ε)*Y.card ∧
          (Z.card : ℝ) ≤ (3+4/((g : ℝ)-2)+ε)*Y.card) ∧
      R.rounds = 1+(roundBound p+SmallComponentProgram.roundBound a K) ∧
      ∀ n c : ℕ, b ≤ c*Nat.clog 2 (n+2) →
        R.maxBits ≤ max c (max (messageConstant p c) (SmallComponentProgram.messageConstant a 1 K c))*
          Nat.clog 2 (n+2) := by
  obtain ⟨p,K,hs⟩ := OrdinarySurfaceImprovedGirth.parameters e g hg hne ε hε
  refine ⟨p,K,?_⟩
  intro V _ _ G _ hsurface hgirth b C
  have h := hs G hsurface hgirth C
  dsimp only at h ⊢
  refine ⟨?_,h.2⟩
  intro ports
  obtain ⟨hd,hb⟩ := h.1 ports
  refine ⟨hd,?_⟩
  intro Y hY
  have hupper := hb Y hY
  refine ⟨hupper,?_⟩
  have hc : ImprovedGirth.limitingCoefficient g+ε ≤ 3+4/((g : ℝ)-2)+ε := by
    linarith [coefficient_le_basic g hg hne]
  exact hupper.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg Y.card))
end Paper.OrdinarySurfaceGirthBoth
#print axioms Paper.OrdinarySurfaceGirthBoth.coefficient_le_basic
#print axioms Paper.OrdinarySurfaceGirthBoth.parameters
