import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Paper.DegreeTwoBalls
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
def neighbors (v : V) : Finset V := G.neighborFinset v ∩ S
def second (a : V) : Finset V := (neighbors G S a).biUnion (fun p => neighbors G S p \ {a})
def third (a : V) : Finset V := (neighbors G S a).biUnion
  (fun p => (neighbors G S p \ {a}).biUnion (fun q => neighbors G S q \ {p}))
def ballThree (a : V) : Finset V := insert a (neighbors G S a ∪ second G S a ∪ third G S a)

theorem remove_predecessor (hdeg : ∀ v ∈ S, (neighbors G S v).card ≤ 2)
    {a p : V} (ha : a ∈ S) (hp : p ∈ neighbors G S a) :
    (neighbors G S p \ {a}).card ≤ 1 := by
  have haN : a ∈ neighbors G S p := Finset.mem_inter.mpr
    ⟨(G.mem_neighborFinset p a).mpr (((G.mem_neighborFinset a p).mp (Finset.mem_inter.mp hp).1).symm),ha⟩
  have hc := Finset.card_sdiff_add_card_inter (neighbors G S p) {a}
  have he : neighbors G S p ∩ {a} = {a} := Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr haN)
  rw [he,Finset.card_singleton] at hc
  have hd := hdeg p (Finset.mem_inter.mp hp).2
  omega

theorem card_ballThree (hdeg : ∀ v ∈ S, (neighbors G S v).card ≤ 2)
    {a : V} (ha : a ∈ S) : (ballThree G S a).card ≤ 7 := by
  have hn := hdeg a ha
  have h2 : (second G S a).card ≤ (neighbors G S a).card := by
    calc
      _ ≤ ∑ p ∈ neighbors G S a, (neighbors G S p \ {a}).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ neighbors G S a, 1 := Finset.sum_le_sum fun p hp => remove_predecessor G S hdeg ha hp
      _ = _ := by simp
  have h3 : (third G S a).card ≤ (neighbors G S a).card := by
    calc
      _ ≤ ∑ p ∈ neighbors G S a, ((neighbors G S p \ {a}).biUnion (fun q => neighbors G S q \ {p})).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ neighbors G S a, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        calc
          _ ≤ ∑ q ∈ neighbors G S p \ {a}, (neighbors G S q \ {p}).card := Finset.card_biUnion_le
          _ ≤ ∑ _q ∈ neighbors G S p \ {a}, 1 := by
            apply Finset.sum_le_sum
            intro q hq
            exact remove_predecessor G S hdeg (Finset.mem_inter.mp hp).2 (Finset.mem_sdiff.mp hq).1
          _ = (neighbors G S p \ {a}).card := by simp
          _ ≤ 1 := remove_predecessor G S hdeg ha hp
      _ = _ := by simp
  have hU := Finset.card_union_le (neighbors G S a) (second G S a)
  have hU' := Finset.card_union_le (neighbors G S a ∪ second G S a) (third G S a)
  have hi := Finset.card_insert_le a (neighbors G S a ∪ second G S a ∪ third G S a)
  change (insert a (neighbors G S a ∪ second G S a ∪ third G S a)).card ≤ 7
  omega

theorem endpoint_mem_ballThree {a b : V} (p : G.Walk a b) (hlen : p.length ≤ 3)
    (hs : ∀ v ∈ p.support, v ∈ S) : b ∈ ballThree G S a := by
  cases p with
  | @nil a => simp [ballThree]
  | @cons a v b hav q =>
    cases q with
    | nil =>
      have hv : b ∈ neighbors G S a := Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset a b).mpr hav,hs b (by simp)⟩
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
    | @cons v w b hvw r =>
      have hv : v ∈ neighbors G S a := Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset a v).mpr hav,hs v (by simp)⟩
      have hw : w ∈ neighbors G S v := Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset v w).mpr hvw,hs w (by simp)⟩
      cases r with
      | nil =>
        by_cases he : b = a
        · subst b; exact Finset.mem_insert_self _ _
        · have hm : b ∈ second G S a := Finset.mem_biUnion.mpr
            ⟨v,hv,Finset.mem_sdiff.mpr ⟨hw,by simpa using he⟩⟩
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
      | @cons w z b hwz t =>
        have hz : z ∈ neighbors G S w := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w z).mpr hwz,hs z (by simp)⟩
        cases t with
        | nil =>
          by_cases he : w = a
          · subst w
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
          · by_cases he' : b = v
            · subst b
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
            · have hm : b ∈ third G S a := Finset.mem_biUnion.mpr
                ⟨v,hv,Finset.mem_biUnion.mpr ⟨w,Finset.mem_sdiff.mpr ⟨hw,by simpa using he⟩,
                  Finset.mem_sdiff.mpr ⟨hz,by simpa using he'⟩⟩⟩
              exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)
        | cons _ t =>
          simp only [SimpleGraph.Walk.length_cons] at hlen
          omega

def accessThree (y : V) : Finset V := neighbors G S y ∪
    (neighbors G S y).biUnion (fun p => neighbors G S p) ∪
    (neighbors G S y).biUnion (fun p => (neighbors G S p).biUnion (fun q => neighbors G S q \ {p}))

theorem card_accessThree (hdeg : ∀ v ∈ S, (neighbors G S v).card ≤ 2)
    (y : V) (hy : (neighbors G S y).card ≤ 2)
    (hfirst : ∀ p ∈ neighbors G S y, (neighbors G S p).card ≤ 1) :
    (accessThree G S y).card ≤ 6 := by
  have h2 : ((neighbors G S y).biUnion (fun p => neighbors G S p)).card ≤ (neighbors G S y).card := by
    calc
      _ ≤ ∑ p ∈ neighbors G S y, (neighbors G S p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ neighbors G S y, 1 := Finset.sum_le_sum hfirst
      _ = _ := by simp
  have h3 : ((neighbors G S y).biUnion (fun p => (neighbors G S p).biUnion
      (fun q => neighbors G S q \ {p}))).card ≤ (neighbors G S y).card := by
    calc
      _ ≤ ∑ p ∈ neighbors G S y, ((neighbors G S p).biUnion (fun q => neighbors G S q \ {p})).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ neighbors G S y, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        calc
          _ ≤ ∑ q ∈ neighbors G S p, (neighbors G S q \ {p}).card := Finset.card_biUnion_le
          _ ≤ ∑ _q ∈ neighbors G S p, 1 := Finset.sum_le_sum fun q hq =>
            remove_predecessor G S hdeg (Finset.mem_inter.mp hp).2 hq
          _ = (neighbors G S p).card := by simp
          _ ≤ 1 := hfirst p hp
      _ = _ := by simp
  have hU := Finset.card_union_le (neighbors G S y) ((neighbors G S y).biUnion (fun p => neighbors G S p))
  have hU' := Finset.card_union_le (neighbors G S y ∪ (neighbors G S y).biUnion (fun p => neighbors G S p))
    ((neighbors G S y).biUnion (fun p => (neighbors G S p).biUnion (fun q => neighbors G S q \ {p})))
  unfold accessThree
  omega

theorem endpoint_mem_accessThree {a b : V} (p : G.Walk a b) (hlen : p.length ≤ 3)
    (hb : b ∈ S) (ha : a ∉ S) (hs : ∀ v ∈ p.support, v = a ∨ v ∈ S) :
    b ∈ accessThree G S a := by
  cases p with
  | nil => exact False.elim (ha hb)
  | @cons a v b hav q =>
    have hvS : v ∈ S := (hs v (by simp)).resolve_left hav.ne.symm
    cases q with
    | nil =>
      have hv : b ∈ neighbors G S a := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr hav,hb⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
    | @cons v w b hvw r =>
      have hv : v ∈ neighbors G S a := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a v).mpr hav,hvS⟩
      cases r with
      | nil =>
        have hw : b ∈ neighbors G S v := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v b).mpr hvw,hb⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v,hv,hw⟩))
      | @cons w z b hwz t =>
        cases t with
        | nil =>
          by_cases he : w = a
          · subst w
            have hz : b ∈ neighbors G S a := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr hwz,hb⟩
            exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
          · have hwS : w ∈ S := (hs w (by simp)).resolve_left he
            have hw : w ∈ neighbors G S v := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v w).mpr hvw,hwS⟩
            have hz : b ∈ neighbors G S w := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w b).mpr hwz,hb⟩
            by_cases he' : b = v
            · subst b
              exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
            · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                ⟨v,hv,Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_sdiff.mpr ⟨hz,by simpa using he'⟩⟩⟩)
        | cons _ t =>
          simp only [SimpleGraph.Walk.length_cons] at hlen
          omega

end Paper.DegreeTwoBalls
