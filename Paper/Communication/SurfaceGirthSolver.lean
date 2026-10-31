import Paper.Communication.SurfaceGirthThreshold
import Paper.Communication.CappedWholeProgram
import Paper.Endpoints.Rounding.SurfaceRotationDensityClass
namespace Paper.SurfaceGirthSolver
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]
noncomputable def program {N : ℕ} (P : Program V Unit (Fin N)) (D : ℕ) (g : ℕ) :
    Program V Unit Bool :=
  .seq P (.seq (.local fun _ _ p => (p.val : ℝ)/D)
    (AdditiveThresholdProgram.program (1/(2*((g : ℝ)/((g : ℝ)-2))+1))))
theorem rounds {N : ℕ} (P : Program V Unit (Fin N)) (D g : ℕ) :
    (program P D g).rounds = P.rounds+1 := by
  simp [program,Program.rounds,AdditiveThresholdProgram.rounds]
theorem maxBits {N : ℕ} (P : Program V Unit (Fin N)) (D g : ℕ) :
    (program P D g).maxBits = max P.maxBits 1 := by
  simp [program,Program.maxBits,AdditiveThresholdProgram.maxBits]
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem correct {N : ℕ} (P : Program V Unit (Fin N)) (D g : ℕ) :
    (program P D g).run G (fun _ => ()) = fun v =>
      decide (v ∈ AdditiveThreshold.output G (1/(2*((g : ℝ)/((g : ℝ)-2))+1))
        (fun u => (((P.run G (fun _ => ()) u).val : ℝ)/D))) := by
  exact AdditiveThresholdProgram.correct G _ _
set_option maxHeartbeats 1000000 in
theorem parameters (e : ℝ) (he : 0 ≤ e) (g : ℕ) (hg3 : 3 ≤ g)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ e) →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {b : ℕ} (C : BitCode V b),
      let P := CappedWholeProgram.program C A L Δ r k t Q T s q M hQ
      let D := PartialFractionalProgram.denominator Δ k Q T s q
      let Z := Finset.univ.filter (fun v => (program P D g).run G (fun _ => ()) v = true)
      dominates G Z ∧ (Z.card : ℝ) ≤
        (3+4/((g : ℝ)-2))*(1+δ)*fractionalNumber G+2*e := by
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,hs⟩ :=
    CappedWholeProgram.parameters (3+3*e) (by linarith) δ hδ
  refine ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,?_⟩
  intro V _ _ G _ hrot hg b C
  obtain ⟨rot,hr⟩ := hrot
  have hf := hs G (SurfaceRounding.minorDensity_of_signedRotation G rot e he hr) C
  dsimp only at hf ⊢
  have ht := SurfaceGirthThreshold.endpoint G rot g hg3 hg e he hr _ hf.1
  dsimp only at ht
  rw [correct]
  have hz : Finset.univ.filter (fun v => decide (v ∈ AdditiveThreshold.output G
      (1/(2*((g : ℝ)/((g : ℝ)-2))+1))
      (fun u => (((CappedWholeProgram.program C A L Δ r k t Q T s q M hQ).run G
        (fun _ => ()) u).val : ℝ)/PartialFractionalProgram.denominator Δ k Q T s q)) = true) =
      AdditiveThreshold.output G (1/(2*((g : ℝ)/((g : ℝ)-2))+1))
      (fun u => (((CappedWholeProgram.program C A L Δ r k t Q T s q M hQ).run G
        (fun _ => ()) u).val : ℝ)/PartialFractionalProgram.denominator Δ k Q T s q) := by
    ext v; simp
  rw [hz]
  refine ⟨ht.1,ht.2.1.trans ?_⟩
  have hd : 0 < (g : ℝ)-2 := by exact_mod_cast (show (0 : ℤ) < (g : ℤ)-2 by omega)
  have hc : 0 ≤ (3+4/((g : ℝ)-2) : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hf.2.2 hc
  nlinarith
end Paper.SurfaceGirthSolver
#print axioms Paper.SurfaceGirthSolver.parameters
