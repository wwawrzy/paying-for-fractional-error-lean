import Paper.Preliminaries.MaskedDistance

/-! Every finite counter produced by the actual distance program has an
actual active physical walk to a marked source of exactly that length. -/
namespace Paper.DistanceWitness
open BroadcastModel ClippedRank MaskedDistance
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (A B : V → Bool)

theorem walk (n : ℕ) {v : V} (hfin : (state G D A B n v).rank.val < D + 1) :
    ∃ u, B u = true ∧ ∃ p : G.Walk v u,
      p.length = (state G D A B n v).rank.val ∧ ∀ z ∈ p.support, A z = true := by
  have ha : A v = true := by
    cases hv : A v with
    | false => rw [inactive G D A B n hv] at hfin; exact False.elim (Nat.lt_irrefl _ hfin)
    | true => rfl
  induction n generalizing v with
  | zero =>
    have hb : B v = true := by
      cases hv : B v with
      | false => simp [state, start, Program.run, ha, hv, top] at hfin
      | true => rfl
    exact ⟨v, hb, .nil, by simp [state, start, Program.run, ha, hb], by simpa using ha⟩
  | succ n ih =>
    let r := choose D (G.neighborFinset v) (state G D A B n v).rank
      (fun w => (state G D A B n w).rank)
    have hr : (state G D A B (n + 1) v).rank = r := update_active G D A B n ha
    have hrf : r.val < D + 1 := by simpa only [hr] using hfin
    rcases choose_origin D (G.neighborFinset v) (state G D A B n v).rank
      (fun w => (state G D A B n w).rank) with hs | ⟨w, hw⟩
    · have hf : (state G D A B n v).rank.val < D + 1 := by rw [← hs]; exact hrf
      obtain ⟨u, hb, p, hp, hpa⟩ := ih hf ha
      exact ⟨u, hb, p, hp.trans (congrArg Fin.val (hr.trans hs)).symm, hpa⟩
    · have hn : (next D (state G D A B n w).rank).val < D + 1 := by rw [← hw]; exact hrf
      obtain ⟨heq, hf⟩ := next_finite D _ hn
      have haw : A w = true := by
        cases hw' : A w with
        | false => rw [inactive G D A B n hw'] at hf; exact False.elim (Nat.lt_irrefl _ hf)
        | true => rfl
      obtain ⟨u, hb, p, hp, hpa⟩ := ih hf haw
      refine ⟨u, hb, .cons ((G.mem_neighborFinset v w).mp w.property) p, ?_, ?_⟩
      · simp only [SimpleGraph.Walk.length_cons, hp]
        exact (heq.symm.trans (congrArg Fin.val (hr.trans hw)).symm)
      · intro z hz
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ha
        · exact hpa z hz

theorem rooted (root : V) (hb : ∀ u, B u = true → u = root) (n : ℕ) {v : V}
    (hfin : (state G D A B n v).rank.val < D + 1) :
    ∃ p : G.Walk v root, p.length = (state G D A B n v).rank.val ∧
      ∀ z ∈ p.support, A z = true := by
  obtain ⟨u, hu, p, hp⟩ := walk G D A B n hfin
  cases hb u hu
  exact ⟨p, hp⟩

theorem lower_neighbor (root : V) (hbr : B root = true) (hb : ∀ u, B u = true → u = root)
    {v : V} (hv : v ≠ root) (hfin : (state G D A B D v).rank.val < D + 1) :
    ∃ w, G.Adj v w ∧ A w = true ∧
      (state G D A B D w).rank.val < (state G D A B D v).rank.val := by
  obtain ⟨p, hp, hpa⟩ := rooted G D A B root hb D hfin
  cases p with
  | nil => exact False.elim (hv rfl)
  | @cons _ w _ ha p =>
    refine ⟨w, ha, hpa w (by simp), ?_⟩
    have htail : ∀ z ∈ p.support, A z = true := fun z hz => hpa z (by simp [hz])
    have hlen : p.length ≤ D := by simp only [SimpleGraph.Walk.length_cons] at hp; omega
    have hh := rank_le_walk G D A B p htail hbr D hlen
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega
end Paper.DistanceWitness
