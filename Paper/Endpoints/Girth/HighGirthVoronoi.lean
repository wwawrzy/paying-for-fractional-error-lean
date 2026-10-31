import Paper.Endpoints.Girth.HighGirthCenters

/-! Nearest-center clusters with a coherent tie-break for fv:hg:dilute.
The center set is arbitrary and nonempty. Connectedness is explicit because
Mathlib's natural-valued distance is zero for unreachable vertices. -/
namespace Paper.HighGirthVoronoi
variable {V : Type} [LinearOrder V]

def Best (G : SimpleGraph V) (C : Finset V) (v c : V) : Prop :=
  c ∈ C ∧ ∀ d ∈ C, G.dist v c ≤ G.dist v d ∧ (G.dist v c = G.dist v d → c ≤ d)

theorem exists_best (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) (v : V) :
    ∃ c, Best G C v c := by
  classical
  obtain ⟨c₀,hc₀,hmin⟩ := Finset.exists_min_image C (fun c => G.dist v c) hC
  let ties := C.filter (fun c => G.dist v c = G.dist v c₀)
  have hties : ties.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀,rfl⟩⟩
  refine ⟨ties.min' hties, ?_⟩
  have hc := Finset.mem_filter.mp (Finset.min'_mem ties hties)
  refine ⟨hc.1, ?_⟩
  intro d hd
  refine ⟨?_, ?_⟩
  · rw [hc.2]
    exact hmin d hd
  · intro heq
    apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨hd, heq.symm.trans hc.2⟩

noncomputable def owner (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) (v : V) : V :=
  Classical.choose (exists_best G C hC v)

theorem owner_spec (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) (v : V) :
    Best G C v (owner G C hC v) := Classical.choose_spec (exists_best G C hC v)

theorem best_unique (G : SimpleGraph V) (C : Finset V) (v c d : V)
    (hc : Best G C v c) (hd : Best G C v d) : c = d := by
  have hcd := hc.2 d hd.1
  have hdc := hd.2 c hc.1
  have heq := le_antisymm hcd.1 hdc.1
  exact le_antisymm (hcd.2 heq) (hdc.2 heq.symm)

theorem owner_radius (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) (R : Nat)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ R) (v : V) :
    G.dist v (owner G C hC v) ≤ R := by
  obtain ⟨c,hc,hr⟩ := hcover v
  exact le_trans ((owner_spec G C hC v).2 c hc).1 hr

theorem owner_center (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (c : V) (hc : c ∈ C) : owner G C hC c = c := by
  have hs := owner_spec G C hC c
  have hz : G.dist c (owner G C hC c) = 0 := by
    have hh := (hs.2 c hc).1
    simpa using hh
  exact ((hconn.dist_eq_zero_iff).mp hz).symm

theorem owner_toward (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (v u : V) (hadj : G.Adj v u)
    (hstep : G.dist u (owner G C hC v) + 1 = G.dist v (owner G C hC v)) :
    owner G C hC u = owner G C hC v := by
  let c := owner G C hC v
  let d := owner G C hC u
  have hc : Best G C v c := owner_spec G C hC v
  have hd : Best G C u d := owner_spec G C hC u
  have hv := hc.2 d hd.1
  have hu := hd.2 c hc.1
  have htri : G.dist v d ≤ 1 + G.dist u d := by
    have hh := hconn.dist_triangle (u := v) (v := u) (w := d)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hh
    exact hh
  have heqv : G.dist v c = G.dist v d := by dsimp [c] at *; omega
  have hequ : G.dist u d = G.dist u c := by dsimp [c] at *; omega
  exact le_antisymm (hu.2 hequ) (hv.2 heqv)

theorem exists_step (G : SimpleGraph V) (hconn : G.Connected) (v c : V) (hne : v ≠ c) :
    ∃ u, G.Adj v u ∧ G.dist u c + 1 = G.dist v c := by
  obtain ⟨p,hp⟩ := hconn.exists_walk_length_eq_dist v c
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons v u c hadj tail =>
    refine ⟨u,hadj,?_⟩
    have hlo := G.dist_le tail
    have hhi := hconn.dist_triangle (u := v) (v := u) (w := c)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hhi
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

theorem cluster_walk (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (c : V) (hc : c ∈ C) (v : V)
    (hv : owner G C hC v = c) :
    ∃ p : G.Walk v c, p.length = G.dist v c ∧
      ∀ w ∈ p.support, owner G C hC w = c := by
  generalize hn : G.dist v c = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases heq : v = c
    · subst v
      exact ⟨.nil, by simpa using hn, by simpa using owner_center G hconn C hC c hc⟩
    · obtain ⟨u,hadj,hstep⟩ := exists_step G hconn v c heq
      have hu : owner G C hC u = c := by
        have ho := owner_toward G hconn C hC v u hadj (by simpa [hv] using hstep)
        exact ho.trans hv
      obtain ⟨p,hp,hs⟩ := ih (G.dist u c) (by omega) u hu rfl
      refine ⟨p.cons hadj, ?_, ?_⟩
      · simp only [SimpleGraph.Walk.length_cons, hp]
        exact hstep.trans hn
      · intro w hw
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hv
        · exact hs w hw

theorem cluster_connected (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (c : V) (hc : c ∈ C) :
    (G.induce {v | owner G C hC v = c}).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨c,owner_center G hconn C hC c hc⟩,?_⟩
  intro v
  obtain ⟨p,_,hs⟩ := cluster_walk G hconn C hC c hc v.val v.property
  exact ⟨(p.induce {v | owner G C hC v = c} hs).reverse⟩

theorem center_ball_subset (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (r : Nat)
    (hsep : HighGirthCenters.Separated G r C) (c : V) (hc : c ∈ C)
    (v : V) (hv : G.dist v c ≤ r) : owner G C hC v = c := by
  have hs := owner_spec G C hC v
  by_contra hne
  have hfar := hsep c hc (owner G C hC v) hs.1 (Ne.symm hne)
  have hnear := (hs.2 c hc).1
  have htri := hconn.dist_triangle (u := c) (v := v) (w := owner G C hC v)
  rw [SimpleGraph.dist_comm (G := G) (u := c) (v := v)] at htri
  omega

end Paper.HighGirthVoronoi
#print axioms Paper.HighGirthVoronoi.exists_best
#print axioms Paper.HighGirthVoronoi.best_unique
#print axioms Paper.HighGirthVoronoi.owner_radius
#print axioms Paper.HighGirthVoronoi.owner_center
#print axioms Paper.HighGirthVoronoi.owner_toward

#print axioms Paper.HighGirthVoronoi.exists_step
#print axioms Paper.HighGirthVoronoi.cluster_walk
#print axioms Paper.HighGirthVoronoi.cluster_connected

#print axioms Paper.HighGirthVoronoi.center_ball_subset
