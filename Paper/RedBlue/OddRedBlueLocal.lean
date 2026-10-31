import Paper.RedBlue.OddRedBlueOptima
import Paper.Optimality.LowerBounds.BipartiteTwin
import Paper.Optimality.LowerBounds.TreewidthLocalLower
namespace Paper.OddRedBlue

def color (m : ℕ) (p : Fin 2) (v : Fin (8*m)) : Bool := decide (v ∈ red m p)
theorem color_flip (m : ℕ) : (fun v => !(color m 0 v))=color m 1 := by
  funext v
  simp only [color,red,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_zero,Fin.val_one]
  rw [←decide_not]
  apply Bool.decide_congr
  omega

theorem network_color (m : ℕ) (p : Fin 2) (N : PortLocal.Network (Fin (8*m)))
    (hN : N.Compatible (OddPathPower.graph (8*m) 3)) :
    ∀ v q, color m p (N.neighbor v q)=!(color m p v) := by
  intro v q
  have ha := (hN.2 v (N.neighbor v q)).mpr ⟨q,rfl⟩
  have hp:=p.isLt
  have hpar:=ha.2
  simp only [color,red,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [←decide_not]
  apply Bool.decide_congr
  omega

def output {m : ℕ} (N : PortLocal.Network (Fin (8*m))) (P : PortLocal.Program Bool Bool)
    (ids : Fin (8*m) → ℕ) (p : Fin 2) : Finset (Fin (8*m)) :=
  Finset.univ.filter fun v => P.run N ids (color m p) v=true

def Feasible {m : ℕ} (N : PortLocal.Network (Fin (8*m))) (P : PortLocal.Program Bool Bool)
    (ids : Fin (8*m) → ℕ) (p : Fin 2) : Prop :=
  output N P ids p ⊆ blue m p ∧
    ∀ r ∈ red m p, ∃ v ∈ output N P ids p, (OddPathPower.graph (8*m) 3).Adj r v

theorem twin_output (m : ℕ) (N : PortLocal.Network (Fin (8*m)))
    (hN : N.Compatible (OddPathPower.graph (8*m) 3)) (P : PortLocal.Program Bool Bool)
    (ids : Fin (8*m) → ℕ) :
    TreewidthLocalLower.output N (BipartiteTwin.program P) ids=output N P ids 0 ∪ output N P ids 1 := by
  have hr := BipartiteTwin.run_eq N ids (color m 0) (network_color m 0 N hN) P
  rw [color_flip] at hr
  ext v
  simp only [TreewidthLocalLower.output,output,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_union]
  rw [congrFun hr v]
  simp only [Bool.or_eq_true]

theorem twin_total_dominates (m : ℕ) (N : PortLocal.Network (Fin (8*m)))
    (hN : N.Compatible (OddPathPower.graph (8*m) 3)) (P : PortLocal.Program Bool Bool)
    (ids : Fin (8*m) → ℕ) (hP : ∀ p, Feasible N P ids p) :
    ∀ r, ∃ v ∈ TreewidthLocalLower.output N (BipartiteTwin.program P) ids,
      (OddPathPower.graph (8*m) 3).Adj r v := by
  intro r
  rw [twin_output m N hN P ids]
  by_cases hr : r.val%2=0
  · have hred : r ∈ red m 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩
    obtain ⟨v,hv,ha⟩ := (hP 0).2 r hred
    exact ⟨v,Finset.mem_union_left _ hv,ha⟩
  · have hred : r ∈ red m 1 := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change r.val%2=1
      omega
    obtain ⟨v,hv,ha⟩ := (hP 1).2 r hred
    exact ⟨v,Finset.mem_union_right _ hv,ha⟩
end Paper.OddRedBlue
#print axioms Paper.OddRedBlue.twin_total_dominates
