import Paper.Endpoints.Components.ActualComponentReplacementCost
import Paper.Endpoints.Components.SmallComponentPhysicalCorrectness
import Paper.Endpoints.Components.ComponentReplacementCost
import Paper.Endpoints.Components.ComponentReplacementOutputSet
set_option maxHeartbeats 200000
namespace Paper.ActualReplacementGlobalCost

theorem replacement_cost_le
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ Paper.SevenFoundation.closed G r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (A0 : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool)
    (hcover0 : Paper.GeneralCoveringIntegral.Covers cover R
      (Finset.univ.filter (fun u => A0.runEncoded G s u = true))) :
    (Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A0
      (Paper.SmallComponentProgram.program ids a B K hB)).runEncoded G s u = true)).sum
        (fun u => (s u).cost.val) ≤
    (Finset.univ.filter (fun u => A0.runEncoded G s u = true)).sum
      (fun u => (s u).cost.val) := by
  classical
  let I := Paper.CoveringIncidence.graph cover R
  letI : Fintype I.ConnectedComponent := Fintype.ofFinite _
  let A1 := Paper.SmallComponentProgram.program ids a B K hB
  let out := A1.runEncoded G s
  let D0 := Finset.univ.filter (fun u => A0.runEncoded G s u = true)
  let D1 := Finset.univ.filter (fun u => (out u).2 = true)
  let D := Finset.univ.filter (fun u => (Paper.ComponentReplacementProgram.program A0 A1).runEncoded G s u = true)
  let rep : I.ConnectedComponent → V := fun X => X.nonempty_supp.choose
  have hrep (X : I.ConnectedComponent) : rep X ∈ X.supp := X.nonempty_supp.choose_spec
  let solved : I.ConnectedComponent → Bool := fun X => (out (rep X)).1
  have hspec (X : I.ConnectedComponent) := Paper.SmallComponentPhysicalCorrectness.physical_correct G cover targets R
    hinc hlocal a ha hden B K hB ids s hd hC ht X hc hK hrows
  have hflag (u : V) : solved (I.connectedComponentMk u) = (out u).1 :=
    (hspec (I.connectedComponentMk u)).1 (rep (I.connectedComponentMk u)) (hrep _) u (by rfl)
  have hcost : ∀ X : I.ConnectedComponent, solved X = true →
      (D1.filter (fun u => I.connectedComponentMk u = X)).sum (fun u => ((s u).cost.val : Real)) ≤
      (D0.filter (fun u => I.connectedComponentMk u = X)).sum (fun u => ((s u).cost.val : Real)) := by
    intro X hs
    have hNat := Paper.ActualComponentReplacementCost.selected_component_cost_le G cover targets R
      hinc hlocal a ha hden B K hB ids s hd hC ht X hc A0 hcover0 (rep X) (hrep X) hs
    have hnew : D1.filter (fun u => I.connectedComponentMk u = X) =
        (Paper.IncidenceComponent.vertices I X).filter (fun u => (out u).2 = true) := by
      ext u
      simp only [D1, Finset.mem_filter, Finset.mem_univ, true_and,
        Paper.IncidenceComponent.mem_vertices, SimpleGraph.ConnectedComponent.mem_supp_iff, and_comm]
    have hold : D0.filter (fun u => I.connectedComponentMk u = X) =
        D0 ∩ Paper.IncidenceComponent.vertices I X := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_inter, Paper.IncidenceComponent.mem_vertices,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hnew, hold]
    exact_mod_cast hNat
  have hout := Paper.ComponentReplacementOutputSet.replacement_output_set G A0 A1 s
  change D = (D0 ∪ D1).filter (fun u => if (out u).1 then u ∈ D1 else u ∈ D0) at hout
  have hmixed : (D0 ∪ D1).filter
      (fun u => if solved (I.connectedComponentMk u) then u ∈ D1 else u ∈ D0) = D := by
    rw [hout]
    apply Finset.filter_congr
    intro u hu
    rw [hflag u]
  have hReal := Paper.ComponentReplacementCost.replacement_cost_le D0 D1 I.connectedComponentMk solved
    (fun u => ((s u).cost.val : Real)) hcost
  rw [hmixed] at hReal
  change D.sum (fun u => (s u).cost.val) ≤ D0.sum (fun u => (s u).cost.val)
  dsimp only at hReal
  exact_mod_cast hReal

end Paper.ActualReplacementGlobalCost

#print axioms Paper.ActualReplacementGlobalCost.replacement_cost_le
