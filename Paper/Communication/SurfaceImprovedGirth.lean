import Paper.Endpoints.Rounding.ImprovedExcessGeneralSolver
import Paper.Communication.OrdinaryAbsorptionPort
import Paper.Communication.SurfaceGirthThreshold
import Paper.Endpoints.Rounding.SurfaceRotationDensityClass
import Paper.Endpoints.Rounding.AbsorptionPublicParameters
import Paper.Endpoints.Girth.ImprovedGirth
namespace Paper.SurfaceImprovedGirth
open BroadcastModel SevenFoundation ImprovedExcessSolver
set_option maxHeartbeats 1500000 in
theorem parameters (e : ℝ) (he : 0 ≤ e) (g : ℕ) (hg : 5 ≤ g) (hne : g ≠ 6)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Config (NoncriticalGirth.density g), ∃ K : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ e) →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {b : ℕ} (C : BitCode V b),
      let a := Nat.ceil (3+3*e)
      let R := OrdinaryAbsorption.portProgram C a K (ImprovedExcessSolver.program C p)
      (∀ ports : PortBroadcastModel.Numbering G,
        let Z := Finset.univ.filter (fun v => R.runEncoded G ports (fun _ => ()) v = true)
        dominates G Z ∧ ∀ Y : Finset V, dominates G Y →
          (Z.card : ℝ) ≤ (ImprovedGirth.limitingCoefficient g+ε)*Y.card) ∧
      R.rounds = 1+(roundBound p+SmallComponentProgram.roundBound a K) ∧
      ∀ n c : ℕ, b ≤ c*Nat.clog 2 (n+2) →
        R.maxBits ≤ max c (max (messageConstant p c) (SmallComponentProgram.messageConstant a 1 K c))*
          Nat.clog 2 (n+2) := by
  let a := NoncriticalGirth.density g
  let θ := ImprovedExcessEndpoint.gap a
  let b : ℝ := 2*(a : ℝ)+1
  let c := ImprovedGirth.limitingCoefficient g
  have ha : 1 ≤ a := (NoncriticalGirth.density_bounds g (by omega)).1
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn := NoncriticalGirth.density_noninteger g hg hne
  obtain ⟨hθ,hθ1⟩ := ImprovedExcessEndpoint.gap_bounds a ha hn
  have hmax := ImprovedExcess.muMax_pos (a : ℝ) θ haR hθ hθ1
  have hbelow : max 0 (b-c-ε/2) < ImprovedExcess.muMax (a : ℝ) θ := by
    apply max_lt hmax
    dsimp [b,c,ImprovedGirth.limitingCoefficient,a,θ]
    linarith
  obtain ⟨μ,hμ,hlo,hhi⟩ := ImprovedExcess.exists_rational_mu_above (a : ℝ) θ
    (max 0 (b-c-ε/2)) (le_max_left _ _) hbelow
  have hμR : (0 : ℝ) < μ := by exact_mod_cast hμ
  obtain ⟨hμθ,hadm⟩ := (ImprovedExcess.admissible_iff_le_muMax (a : ℝ) θ (μ : ℝ)
    haR hθ hθ1 hμR.le).mpr hhi.le
  let r : ℝ := b-(μ : ℝ)
  have hr : 1 ≤ r := by dsimp [r,b]; linarith
  have hrc : r+ε/2 ≤ c+ε := by
    have hh := (le_max_right 0 (b-c-ε/2)).trans_lt hlo
    dsimp [r]; linarith
  let η := (a : ℝ)*e
  let q := Nat.ceil (ImprovedExcess.additive (a : ℝ) θ (μ : ℝ) η)
  obtain ⟨δ,hδ,hsmall,hK,hthreshold⟩ := AbsorptionPublicParameters.public_absorption_parameters r (ε/2) q hr (by linarith)
  let K := max 1 (Nat.ceil (2*(q : ℝ)/(ε/2)))
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨p,hp,hs⟩ := fixed_gain_parameters (3+3*e) (by linarith) a μ η (δ : ℝ)
    ha hn hμ.le hμθ hadm (mul_nonneg (by linarith) he) hδR
  refine ⟨p,K,?_⟩
  intro V _ _ G _ hrot hgirth bits C
  obtain ⟨rot,hgen⟩ := hrot
  have hm := SurfaceRounding.minorDensity_of_signedRotation G rot e he hgen
  have hden : ImprovedExcess.DensityWithExcess G (a : ℝ) η := by
    intro S
    have hh := SurfaceGirthThreshold.induced_density G rot g (by omega) hgirth e hgen S
    simpa only [← NoncriticalGirth.density_cast g] using hh
  have hb := hs G hm hden C
  have hd : Incidence.InducedDensityBound G (3+3*e) := by
    intro S
    have hh := hm (S : Set V) (G.induce (S : Set V)) (SimpleGraph.IsMinor.of_induce G _)
    simpa only [SimpleGraph.inducedEdgeCount,Fintype.card_eq_nat_card,Finset.coe_sort_coe,
      Nat.card_eq_finsetCard] using hh
  have hd' := ComponentDensity.density_mono G (Nat.le_ceil (3+3*e)) hd
  have hapos : 1 ≤ Nat.ceil (3+3*e) := Nat.one_le_ceil_iff.mpr (by linarith)
  have hcost : ((Finset.univ.filter (fun v => (ImprovedExcessSolver.program C p).run G (fun _ => ()) v = true)).card : ℝ) ≤
      r*(1+(δ : ℝ))*fractionalNumber G+q := by
    have hh := hb.2.trans (add_le_add le_rfl (Nat.le_ceil (ImprovedExcess.additive (a : ℝ) θ (μ : ℝ) η)))
    simpa only [ImprovedExcessSolver.output,Program.runEncoded_eq_run] using hh
  have hcov : dominates G (Finset.univ.filter (fun v => (ImprovedExcessSolver.program C p).run G (fun _ => ()) v = true)) := by
    simpa only [ImprovedExcessSolver.output,Program.runEncoded_eq_run] using hb.1
  have ho := OrdinaryAbsorption.endpoint G C (Nat.ceil (3+3*e)) K hapos hd' hK
    (ImprovedExcessSolver.program C p) r (ε/2) q δ hr (by linarith) hδ hsmall hthreshold hcov hcost
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro ports
    rw [OrdinaryAbsorption.port_correct]
    refine ⟨ho.1,?_⟩
    intro Y hY
    exact (ho.2 Y hY).trans (mul_le_mul_of_nonneg_right hrc (Nat.cast_nonneg _))
  · rw [OrdinaryAbsorption.port_rounds,ImprovedExcessSolver.rounds]
  · intro n c hids
    exact OrdinaryAbsorption.port_bits C _ K _ n c (messageConstant p c) hids
      (ImprovedExcessSolver.logarithmic_bits C p n c hids)
end Paper.SurfaceImprovedGirth
#print axioms Paper.SurfaceImprovedGirth.parameters
