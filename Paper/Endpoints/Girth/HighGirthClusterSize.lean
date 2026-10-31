import Paper.Endpoints.Girth.HighGirthVoronoi

/-! Size of genuine nearest-center clusters in a connected finite graph. -/
namespace Paper.HighGirthClusterSize
open HighGirthVoronoi
variable {V : Type} [Fintype V] [LinearOrder V]

noncomputable def ball (G : SimpleGraph V) (c : V) (r : Nat) : Finset V :=
  Finset.univ.filter (fun v => G.dist c v ≤ r)

theorem ball_card (G : SimpleGraph V) (hconn : G.Connected) (c : V) (r : Nat)
    (hn : r + 1 ≤ Fintype.card V) : r + 1 ≤ (ball G c r).card := by
  classical
  by_cases hall : ∀ v, G.dist c v ≤ r
  · have heq : ball G c r = Finset.univ := by ext v; simp [ball, hall]
    simpa [heq] using hn
  · push_neg at hall
    obtain ⟨v,hv⟩ := hall
    obtain ⟨p,hpath,hp⟩ := hconn.exists_path_of_dist c v
    let f : Fin (r+1) → {w // w ∈ ball G c r} := fun i =>
      ⟨p.getVert i.val, by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hh := G.dist_le (p.take i.val)
        rw [SimpleGraph.Walk.take_length] at hh
        exact le_trans hh (le_trans (Nat.min_le_left _ _) (by omega))⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have heq : p.getVert i.val = p.getVert j.val := congrArg Subtype.val hij
      have hi : i.val ≤ p.length := by omega
      have hj : j.val ≤ p.length := by omega
      rw [p.getVert_eq_support_getElem hi, p.getVert_eq_support_getElem hj] at heq
      exact hpath.support_nodup.getElem_inj_iff.mp heq
    have hh := Fintype.card_le_of_injective f hf
    simpa using hh

noncomputable def cluster (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) (c : V) :
    Finset V := Finset.univ.filter (fun v => owner G C hC v = c)

theorem cluster_card (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (r : Nat)
    (hsep : HighGirthCenters.Separated G r C) (c : V) (hc : c ∈ C)
    (hn : r+1 ≤ Fintype.card V) : r+1 ≤ (cluster G C hC c).card := by
  classical
  apply le_trans (ball_card G hconn c r hn)
  apply Finset.card_le_card
  intro v hv
  have hdist := (Finset.mem_filter.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply center_ball_subset G hconn C hC r hsep c hc v
  simpa only [SimpleGraph.dist_comm] using hdist

theorem cluster_sum (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) :
    ∑ c ∈ C, (cluster G C hC c).card = Fintype.card V := by
  classical
  have hh := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset V)) (t := C) (f := owner G C hC)
    (fun v _ => (owner_spec G C hC v).1)
  simpa only [cluster, Finset.card_univ] using hh.symm

theorem center_count (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (r : Nat)
    (hsep : HighGirthCenters.Separated G r C) (hn : r+1 ≤ Fintype.card V) :
    C.card * (r+1) ≤ Fintype.card V := by
  classical
  calc C.card * (r+1) = ∑ _c ∈ C, (r+1) := by simp
       _ ≤ ∑ c ∈ C, (cluster G C hC c).card :=
         Finset.sum_le_sum (fun c hc => cluster_card G hconn C hC r hsep c hc hn)
       _ = Fintype.card V := cluster_sum G C hC

end Paper.HighGirthClusterSize
#print axioms Paper.HighGirthClusterSize.ball_card
#print axioms Paper.HighGirthClusterSize.cluster_card

#print axioms Paper.HighGirthClusterSize.cluster_sum
#print axioms Paper.HighGirthClusterSize.center_count
