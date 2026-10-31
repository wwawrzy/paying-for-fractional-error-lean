import Paper.Endpoints.Girth.HighGirthClusterMinor
import Paper.Preliminaries.MinorDensity

/-! fv:hg:dilute for an actual connected graph. All clusters and the simple
minor are constructed, rather than assumed as witnesses. -/
namespace Paper.HighGirthDilutionConnected
open HighGirthVoronoi HighGirthClusterMinor HighGirthClusterSize
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

set_option backward.isDefEq.respectTransparency false in
theorem internal_sum (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (R : Nat)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ R)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 2*R+1 < p.length) :
    (∑ c ∈ C, (internal G C hC c).card) + C.card = Fintype.card V := by
  classical
  have htree : ∀ c ∈ C, (internal G C hC c).card + 1 = (cluster G C hC c).card := by
    intro c hc
    have ht := (HighGirthClusterTree.induced_tree G hconn C hC R hcover hgirth c hc).card_edgeFinset
    rw [internal_card]
    convert ht using 1
    · congr 1
      congr 1
      ext e
      simp
    · simpa only [cluster] using (Fintype.card_subtype (fun v => owner G C hC v = c)).symm
  calc (∑ c ∈ C, (internal G C hC c).card) + C.card =
      ∑ c ∈ C, ((internal G C hC c).card + 1) := by rw [Finset.sum_add_distrib]; simp
       _ = ∑ c ∈ C, (cluster G C hC c).card := Finset.sum_congr rfl htree
       _ = Fintype.card V := cluster_sum G C hC

set_option backward.isDefEq.respectTransparency false in
theorem density_connected (G : SimpleGraph V) (hconn : G.Connected)
    (rho : Real) (hrho : 1 ≤ rho) (r : Nat) (hr : 1 ≤ r)
    (hminor : MinorDensity.Bound G rho)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 8*r+2 < p.length) :
    (G.edgeFinset.card : Real) ≤ (1 + (rho-1)/(r+1)) * Fintype.card V := by
  classical
  letI : Nonempty V := hconn.nonempty
  have hcoef : (1 : Real) ≤ 1 + (rho-1)/(r+1) := by
    have hd : (0 : Real) < (r:Real)+1 := by positivity
    exact le_add_of_nonneg_right (div_nonneg (by linarith) hd.le)
  by_cases hn : Fintype.card V ≤ r
  · have ha : G.IsAcyclic := by
      intro v p hp
      have hh := hp.support_nodup.length_le_card
      have hb : p.length ≤ Fintype.card V := by
        simpa only [List.length_tail,SimpleGraph.Walk.length_support,Nat.add_sub_cancel] using hh
      have hg := hgirth v p hp
      omega
    have ht : G.IsTree := ⟨hconn,ha⟩
    have hh := ht.card_edgeFinset
    have hm : (G.edgeFinset.card : Real) ≤ Fintype.card V := by exact_mod_cast (by omega : G.edgeFinset.card ≤ Fintype.card V)
    exact hm.trans (by nlinarith [show (0:Real) ≤ Fintype.card V from Nat.cast_nonneg _])
  · have hn' : r+1 ≤ Fintype.card V := by omega
    obtain ⟨C,hsep,hcover⟩ := HighGirthCenters.exists_centers G r
    have hC := HighGirthCenters.centers_nonempty G r C hcover
    have hshort : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 2*(2*r)+1 < p.length := by
      intro v p hp
      have hh := hgirth v p hp
      omega
    have hlong : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 4*(2*r)+2 < p.length := by
      intro v p hp
      have hh := hgirth v p hp
      omega
    have hparts := partition_card G C hC
    have hin := internal_sum G hconn C hC (2*r) hcover hshort
    have hcross := cross_card_le G hconn C hC (2*r) hcover hlong
    have hj := hminor {c // c ∈ C} (graph G C hC) (isMinor G hconn C hC)
    have hj' : ((graph G C hC).edgeFinset.card : Real) ≤ rho*C.card := by simpa using hj
    have hc := center_count G hconn C hC r hsep hn'
    have hc' : (C.card:Real)*((r:Real)+1) ≤ Fintype.card V := by exact_mod_cast hc
    have hd : (0:Real) < (r:Real)+1 := by positivity
    have hN : (C.card:Real) ≤ (Fintype.card V:Real)/((r:Real)+1) := (le_div_iff₀ hd).mpr hc'
    have hparts' : (G.edgeFinset.card:Real) =
        (∑ c ∈ C, (internal G C hC c).card:Nat) + (cross G C hC).card := by exact_mod_cast hparts
    have hin' : ((∑ c ∈ C, (internal G C hC c).card:Nat):Real) + C.card = Fintype.card V := by exact_mod_cast hin
    have hcross' : ((cross G C hC).card:Real) ≤ (graph G C hC).edgeFinset.card := by exact_mod_cast hcross
    calc (G.edgeFinset.card:Real) ≤ Fintype.card V + (rho-1)*C.card := by linarith
         _ ≤ Fintype.card V + (rho-1)*((Fintype.card V:Real)/((r:Real)+1)) := by
           have hh := mul_le_mul_of_nonneg_left hN (show (0:Real) ≤ rho-1 by linarith)
           linarith
         _ = _ := by ring

end Paper.HighGirthDilutionConnected
#print axioms Paper.HighGirthDilutionConnected.internal_sum
#print axioms Paper.HighGirthDilutionConnected.density_connected
