import Paper.Optimality.Treewidth.CliqueFourMatchings
namespace Paper.CliqueBalancedFourRows
open Paper.CliqueFourMatchings
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def pair : Fin 6 → Finset (Fin 4) := ![{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}]
def rows (a b c d : Fin 6) : Fin 4 → Finset (Fin 4) := ![pair a,pair b,pair c,pair d]
theorem numeric : ∀ a b c d : Fin 6,
    (∀ v : Fin 4, (Finset.univ.filter (fun i => v ∈ rows a b c d i)).card = 2) →
    ∃ k : Fin 3, ∀ i : Fin 4, ∀ side : Bool,
      (rows a b c d i ∩ part k side).Nonempty := by decide

theorem pair_covers (T : Finset (Fin 4)) (hT : T.card = 2) :
    ∃ i : Fin 6, pair i = T := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hT
  have hh : ∀ a b : Fin 4, a ≠ b → ∃ i : Fin 6, pair i = {a,b} := by decide
  exact hh a b hab

theorem choose (N : Fin 4 → Finset (Fin 4)) (hN : ∀ i, (N i).card = 2)
    (hbalance : ∀ v : Fin 4, (Finset.univ.filter (fun i => v ∈ N i)).card = 2) :
    ∃ k : Fin 3, ∀ i : Fin 4, ∀ side : Bool, (N i ∩ part k side).Nonempty := by
  obtain ⟨a,ha⟩ := pair_covers (N 0) (hN 0)
  obtain ⟨b,hb⟩ := pair_covers (N 1) (hN 1)
  obtain ⟨c,hc⟩ := pair_covers (N 2) (hN 2)
  obtain ⟨d,hd⟩ := pair_covers (N 3) (hN 3)
  have he : ∀ i : Fin 4, rows a b c d i = N i := by
    intro i
    fin_cases i <;> simp [rows,ha,hb,hc,hd]
  obtain ⟨k,hk⟩ := numeric a b c d (by simpa only [he] using hbalance)
  exact ⟨k,by simpa only [he] using hk⟩
end Paper.CliqueBalancedFourRows
