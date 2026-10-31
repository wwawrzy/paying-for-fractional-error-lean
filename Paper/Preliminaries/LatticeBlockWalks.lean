import Paper.Preliminaries.LatticeBlockGeometry
namespace Paper.LatticeBlock

theorem adjacent_full {b q m s r : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) (H : IsBlockGraph O G)
    {v w : Vertex b q m} (hv : Full (r+s) v.2) (ha : G.Adj v w) :
    v.1=w.1 ∧ Full r w.2 := by
  have hs : Full s v.2 := full_mono (by omega) hv
  have hblock := same_block O G H hs ha
  refine ⟨hblock,?_⟩
  have hi : difference v.2 w.2 ∈ O.values := by
    apply (H.inside v.1 v.2 w.2).mp
    have ha' : G.Adj (v.1,v.2) (w.1,w.2) := ha
    rw [← hblock] at ha'
    exact ha'
  intro i
  have hb := O.bounded _ hi i
  have hh := hv i
  dsimp only [difference] at hb
  omega

theorem walk_full {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) (H : IsBlockGraph O G)
    {v w : Vertex b q m} (p : G.Walk v w) (r : ℕ)
    (hv : Full (r+p.length*s) v.2) : v.1=w.1 ∧ Full r w.2 := by
  induction p generalizing r with
  | nil => exact ⟨rfl,by simpa using hv⟩
  | @cons u v w ha p ih =>
    have hh : Full ((r+p.length*s)+s) u.2 := by
      simpa only [SimpleGraph.Walk.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hv
    obtain ⟨he,hf⟩ := adjacent_full O G H hh ha
    obtain ⟨he',hf'⟩ := ih r hf
    exact ⟨he.trans he',hf'⟩
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.walk_full
