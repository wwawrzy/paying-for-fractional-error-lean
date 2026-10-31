import Paper.Communication.SurfaceGirthSolver
import Paper.Endpoints.Rounding.OrdinaryAbsorption
import Paper.Endpoints.Rounding.AbsorptionPublicParameters
namespace Paper.SurfaceGirthAbsorbed
open BroadcastModel SevenFoundation
set_option maxHeartbeats 1000000 in
theorem parameters (e : ℝ) (he : 0 ≤ e) (g : ℕ) (hg3 : 3 ≤ g) (ε : ℝ) (hε : 0 < ε) :
    ∃ A L Δ r k t Q T s q M K : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ e) →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {b : ℕ} (C : BitCode V b),
      let P := CappedWholeProgram.program C A L Δ r k t Q T s q M hQ
      let D := PartialFractionalProgram.denominator Δ k Q T s q
      let B := SurfaceGirthSolver.program P D g
      let Z := Finset.univ.filter (fun v =>
        (OrdinaryAbsorption.program C (Nat.ceil (3+3*e)) K B).runEncoded G (OrdinaryAbsorption.input G) v = true)
      dominates G Z ∧ ∀ Y : Finset V, dominates G Y →
        (Z.card : ℝ) ≤ (3+4/((g : ℝ)-2)+ε)*Y.card := by
  have hd : 0 < (g : ℝ)-2 := by exact_mod_cast (show (0 : ℤ) < (g : ℤ)-2 by omega)
  have hr : (1 : ℝ) ≤ 3+4/((g : ℝ)-2) := by
    have hp : 0 ≤ (4:ℝ)/((g : ℝ)-2) := by positivity
    linarith
  obtain ⟨δ,hδ,hsmall,hK,hthreshold⟩ := AbsorptionPublicParameters.public_absorption_parameters
    (3+4/((g : ℝ)-2)) ε (Nat.ceil (2*e)) hr hε
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,hs⟩ := SurfaceGirthSolver.parameters e he g hg3 (δ : ℝ) hδR
  let K := max 1 (Nat.ceil (2*(Nat.ceil (2*e) : ℝ)/ε))
  refine ⟨A,L,Δ,r,k,t,Q,T,s,q,M,K,hQ,hq,?_⟩
  intro V _ _ G _ hrot hg b C
  have hb := hs G hrot hg C
  obtain ⟨rot,hgen⟩ := hrot
  have hm := SurfaceRounding.minorDensity_of_signedRotation G rot e he hgen
  have hden : Incidence.InducedDensityBound G (3+3*e) := by
    intro S
    have hh := hm (S : Set V) (G.induce (S : Set V)) (SimpleGraph.IsMinor.of_induce G _)
    simpa only [SimpleGraph.inducedEdgeCount,Fintype.card_eq_nat_card,Finset.coe_sort_coe,
      Nat.card_eq_finsetCard] using hh
  have hden' := ComponentDensity.density_mono G (Nat.le_ceil (3+3*e)) hden
  have ha : 1 ≤ Nat.ceil (3+3*e) := Nat.one_le_ceil_iff.mpr (by linarith)
  have hcost : ((Finset.univ.filter (fun v =>
      (SurfaceGirthSolver.program (CappedWholeProgram.program C A L Δ r k t Q T s q M hQ)
        (PartialFractionalProgram.denominator Δ k Q T s q) g).run G (fun _ => ()) v = true)).card : ℝ) ≤
      (3+4/((g : ℝ)-2))*(1+(δ : ℝ))*fractionalNumber G+(Nat.ceil (2*e) : ℝ) :=
    hb.2.trans (add_le_add_right (Nat.le_ceil (2*e)) _)
  exact OrdinaryAbsorption.endpoint G C (Nat.ceil (3+3*e)) K ha hden' hK _
    (3+4/((g : ℝ)-2)) ε (Nat.ceil (2*e)) δ hr hε hδ hsmall hthreshold hb.1 hcost
end Paper.SurfaceGirthAbsorbed
#print axioms Paper.SurfaceGirthAbsorbed.parameters
