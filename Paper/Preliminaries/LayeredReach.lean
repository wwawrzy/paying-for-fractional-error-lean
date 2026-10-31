import Paper.Preliminaries.LayeredConnector

/-! A connected physical set meeting all terminal sets supplies a layered
walk through all copies, entirely inside that physical set. -/
namespace Paper.LayeredReach
attribute [local instance] Classical.propDecidable
open LayeredConnector
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def horizontalIn {m : ℕ} (A : Fin (m + 1) → Finset V) (S : Set V) (j : Fin m) :
    G.induce S →g (graph G A).induce {z : V × Fin m | z.1 ∈ S} where
  toFun v := ⟨(v.val, j), v.property⟩
  map_rel' h := Or.inl ⟨rfl, h⟩

theorem reach_terminal {n : ℕ} (A : Fin (n + 2) → Finset V) (S : Set V)
    (hconn : (G.induce S).Connected) (point : Fin (n + 2) → S)
    (hp : ∀ i, (point i).val ∈ A i) (j : Fin (n + 1)) :
    ((graph G A).induce {z : V × Fin (n + 1) | z.1 ∈ S}).Reachable
      ⟨((point 0).val, 0), (point 0).property⟩
      ⟨((point j.succ).val, j), (point j.succ).property⟩ := by
  induction j using Fin.induction with
  | zero => exact (hconn (point 0) (point (0 : Fin (n + 1)).succ)).map (horizontalIn G A S 0)
  | @succ j ih =>
    have hv : ((graph G A).induce {z : V × Fin (n + 1) | z.1 ∈ S}).Adj
        ⟨((point j.castSucc.succ).val, j.castSucc), (point j.castSucc.succ).property⟩
        ⟨((point j.castSucc.succ).val, j.succ), (point j.castSucc.succ).property⟩ := by
      right
      refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
      have he : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
      simpa only [he] using hp j.castSucc.succ
    have hh := (hconn (point j.castSucc.succ) (point j.succ.succ)).map (horizontalIn G A S j.succ)
    exact ih.trans (hv.reachable.trans hh)

noncomputable def sources {n : ℕ} (A : Fin (n + 2) → Finset V) : Finset (V × Fin (n + 1)) :=
  (A 0).image (fun v => (v, 0))

noncomputable def targets {n : ℕ} (A : Fin (n + 2) → Finset V) : Finset (V × Fin (n + 1)) :=
  (A (Fin.last n).succ).image (fun v => (v, Fin.last n))

theorem connected_walk {n : ℕ} (A : Fin (n + 2) → Finset V) (S : Finset V)
    (hconn : (G.induce (S : Set V)).Connected) (hmeet : ∀ i, (S ∩ A i).Nonempty) :
    ∃ x ∈ sources A, ∃ y ∈ targets A, ∃ p : (graph G A).Walk x y,
      ∀ z ∈ p.support, z.1 ∈ S := by
  classical
  let point : Fin (n + 2) → ↥(S : Set V) := fun i =>
    ⟨(hmeet i).choose, (Finset.mem_inter.mp (hmeet i).choose_spec).1⟩
  have hp : ∀ i, (point i).val ∈ A i := fun i => (Finset.mem_inter.mp (hmeet i).choose_spec).2
  obtain ⟨q⟩ := reach_terminal G A (S : Set V) hconn point hp (Fin.last n)
  let p := q.map (SimpleGraph.Embedding.induce {z : V × Fin (n + 1) | z.1 ∈ (S : Set V)}).toHom
  refine ⟨((point 0).val, 0), Finset.mem_image.mpr ⟨(point 0).val, hp 0, rfl⟩,
    ((point (Fin.last n).succ).val, Fin.last n),
    Finset.mem_image.mpr ⟨(point (Fin.last n).succ).val, hp _, rfl⟩, p, ?_⟩
  intro z hz
  change z ∈ (q.map _).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w, _, hw⟩ := List.mem_map.mp hz
  exact hw ▸ w.property
end Paper.LayeredReach
