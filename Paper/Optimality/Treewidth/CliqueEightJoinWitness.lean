import Paper.Optimality.Treewidth.CliqueEightThreeJoin
import Paper.Optimality.Treewidth.CliquePartitionDegrees
namespace Paper.CliqueEightJoinWitness
open SimpleGraph CliqueTwoContractions
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 2000000 in
theorem minor (hV : Fintype.card V = 8) (hdeg : ∀ v, 5 ≤ G.degree v)
    (S : Finset V) (hS : S.card = 3)
    (hcross : ∀ s ∈ S, ∀ r ∈ Sᶜ, G.Adj s r) : (punctured 4 5).IsMinor G := by
  classical
  have hR : Sᶜ.card = 5 := by rw [Finset.card_compl,hV,hS]
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < Sᶜ.card by omega)
  have hpart := CliquePartitionDegrees.partition G S a
  have hbound : G.inducedDegree a S ≤ 3 := by
    exact (Finset.card_filter_le S (G.Adj a)).trans hS.le
  have hlow : 2 ≤ (Sᶜ.filter (G.Adj a)).card := by
    have hh := hdeg a
    unfold SimpleGraph.inducedDegree at hpart hbound
    omega
  obtain ⟨b,hb,c,hc,hbc⟩ := Finset.one_lt_card.mp (show 1 < (Sᶜ.filter (G.Adj a)).card by omega)
  obtain ⟨hbR,hab⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcR,hac⟩ := Finset.mem_filter.mp hc
  have habn : a ≠ b := hab.ne
  have hacn : a ≠ c := hac.ne
  have hsub : ({a,b,c} : Finset V) ⊆ Sᶜ := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hbR
    · exact hcR
  have hleft : (Sᶜ \ {a,b,c}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsub,hR]
    simp [habn,hacn,hbc]
  obtain ⟨d,e,hde,hdeSet⟩ := Finset.card_eq_two.mp hleft
  have hd : d ∈ Sᶜ \ {a,b,c} := by rw [hdeSet]; simp
  have he : e ∈ Sᶜ \ {a,b,c} := by rw [hdeSet]; simp
  obtain ⟨hdR,hdnot⟩ := Finset.mem_sdiff.mp hd
  obtain ⟨heR,henot⟩ := Finset.mem_sdiff.mp he
  have hda : d ≠ a := by simpa using (fun h => hdnot (Finset.mem_insert.mpr (Or.inl h)))
  have hdb : d ≠ b := by intro h; apply hdnot; simp [h]
  have hdc : d ≠ c := by intro h; apply hdnot; simp [h]
  have hea : e ≠ a := by intro h; apply henot; simp [h]
  have heb : e ≠ b := by intro h; apply henot; simp [h]
  have hec : e ≠ c := by intro h; apply henot; simp [h]
  obtain ⟨s0,s1,s2,hs01,hs02,hs12,hSset⟩ := Finset.card_eq_three.mp hS
  have hs0 : s0 ∈ S := by rw [hSset]; simp
  have hs1 : s1 ∈ S := by rw [hSset]; simp
  have hs2 : s2 ∈ S := by rw [hSset]; simp
  have hSN : ∀ s ∈ S, ∀ r ∈ Sᶜ, s ≠ r := by
    intro s hs r hr h; exact (Finset.mem_compl.mp hr) (h ▸ hs)
  have h0a := hSN s0 hs0 a ha
  have h0b := hSN s0 hs0 b hbR
  have h0c := hSN s0 hs0 c hcR
  have h0d := hSN s0 hs0 d hdR
  have h0e := hSN s0 hs0 e heR
  have h1a := hSN s1 hs1 a ha
  have h1b := hSN s1 hs1 b hbR
  have h1c := hSN s1 hs1 c hcR
  have h1d := hSN s1 hs1 d hdR
  have h1e := hSN s1 hs1 e heR
  have h2a := hSN s2 hs2 a ha
  have h2b := hSN s2 hs2 b hbR
  have h2c := hSN s2 hs2 c hcR
  have h2d := hSN s2 hs2 d hdR
  have h2e := hSN s2 hs2 e heR
  let label : Fin 8 → V := ![s0,s1,s2,a,b,c,d,e]
  have hinj : Function.Injective label := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [label] at hij <;> simp only [hs01,hs01.symm,hs02,hs02.symm,hs12,hs12.symm,habn,habn.symm,hacn,hacn.symm,hbc,hbc.symm,hda,hda.symm,hdb,hdb.symm,hdc,hdc.symm,hea,hea.symm,heb,heb.symm,hec,hec.symm,hde,hde.symm,h0a,h0a.symm,h0b,h0b.symm,h0c,h0c.symm,h0d,h0d.symm,h0e,h0e.symm,h1a,h1a.symm,h1b,h1b.symm,h1c,h1c.symm,h1d,h1d.symm,h1e,h1e.symm,h2a,h2a.symm,h2b,h2b.symm,h2c,h2c.symm,h2d,h2d.symm,h2e,h2e.symm] at hij <;> rfl
  let f : Fin 8 ↪ V := ⟨label,hinj⟩
  apply CliqueEightThreeJoin.transfer G f
  · intro i j hi hj
    have his : label i ∈ S := by
      fin_cases i <;> norm_num at hi <;> dsimp [label] <;> assumption
    have hjr : label j ∈ Sᶜ := by
      fin_cases j <;> norm_num at hj <;> dsimp [label] <;> assumption
    exact hcross (label i) his (label j) hjr
  · exact hab
  · exact hac
end Paper.CliqueEightJoinWitness
#print axioms Paper.CliqueEightJoinWitness.minor
