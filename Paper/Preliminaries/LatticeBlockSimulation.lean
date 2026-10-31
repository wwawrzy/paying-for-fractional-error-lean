import Paper.Preliminaries.LatticeBlockContext
import Paper.Preliminaries.LatticeLocality
namespace Paper.LatticeBlock

theorem block_run {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    {In Out : Type} (P : PortLocal.Program In Out) (j : Fin b) (ids : Vertex b q m → ℕ)
    (a : Vertex b q m → In) (a' : Delta q → In) (k : ℕ) (hk : 1 ≤ k)
    (ha : ∀ x, Full (k*s) x → a (j,x)=a' (coordinate x))
    (x : Position q m) (hx : Full ((k+P.rounds)*s) x) :
    P.run (network O G H) ids a (j,x)=
      P.run (latticeNetwork O) (extendIds j ids) a' (coordinate x) := by
  induction P generalizing k x with
  | «local» f =>
    have hxk : Full (k*s) x := by simpa only [PortLocal.Program.rounds,add_zero] using hx
    have hxs : Full s x := full_mono (by nlinarith) hxk
    change f (G.degree (j,x)) _ _=f O.values.card _ _
    rw [PortLocal.local_transport f (full_degree O G H j x hxs)]
    rw [block_context O G H j x hxs ids,ha x hxk]
  | round R =>
    have hxx : Full ((k+1)*s) x := hx
    have hxs : Full s x := full_mono (by nlinarith) hxx
    have hxk : Full (k*s) x := full_mono (by nlinarith) hxx
    change R.update (G.degree (j,x)) _ _ _=R.update O.values.card _ _ _
    rw [PortLocal.update_transport R (full_degree O G H j x hxs)]
    rw [block_context O G H j x hxs ids,ha x hxk]
    congr 1
    funext p
    let p' := Fin.cast (full_degree O G H j x hxs).symm p
    let w := (network O G H).neighbor (j,x) p'
    have he : w=(j,shift O x hxs (enumeration O p)) := by
      exact neighbor_full O G H j x hxs p'
    have hwk : Full (k*s) w.2 := by
      rw [he]
      exact shift_full O x hxx (enumeration O p)
    have hws : Full s w.2 := full_mono (by nlinarith) hwk
    have hwj : w.1=j := congrArg Prod.fst he
    have hst : a w=a' (coordinate w.2) := by
      simpa only [←hwj] using ha w.2 hwk
    have hc : ((network O G H).context ids w).transport (full_degree O G H w.1 w.2 hws)=
        (latticeNetwork O).context (extendIds j ids) (coordinate w.2) := by
      simpa only [hwj] using block_context O G H w.1 w.2 hws ids
    have hb := back_index O G H (j,x) hxs p' hws
    have hco := neighbor_coordinate O G H (j,x) hxs p'
    change coordinate w.2=(fun i=>coordinate x i+(enumeration O p).val i) at hco
    change R.send (G.degree (w.1,w.2)) ((network O G H).context ids w) (a w)
      ((network O G H).back (j,x) p') =
      R.send O.values.card ((latticeNetwork O).context (extendIds j ids)
        (fun i=>coordinate x i+(enumeration O p).val i))
        (a' (fun i=>coordinate x i+(enumeration O p).val i)) (reversePort O p)
    rw [PortLocal.send_transport R (full_degree O G H w.1 w.2 hws)]
    rw [hc,hst]
    change Fin.cast (full_degree O G H w.1 w.2 hws) ((network O G H).back (j,x) p')=reversePort O p at hb
    rw [hb,hco]
  | seq P Q ihP ihQ =>
    apply ihQ (P.run (network O G H) ids a)
      (P.run (latticeNetwork O) (extendIds j ids) a') (k+P.rounds) (by omega)
    · intro y hy
      exact ihP a a' k hk ha y hy
    · simpa only [PortLocal.Program.rounds,Nat.add_assoc] using hx

theorem block_run_unit {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (j : Fin b) (ids : Vertex b q m → ℕ)
    (x : Position q m) (hx : Full ((P.rounds+1)*s) x) :
    P.run (network O G H) ids (fun _=>()) (j,x)=
      P.run (latticeNetwork O) (extendIds j ids) (fun _=>()) (coordinate x) := by
  apply block_run O G H P j ids (fun _=>()) (fun _=>()) 1 (by omega)
  · intro y hy;rfl
  · simpa only [Nat.add_comm] using hx

theorem block_output_same {b q m s : ℕ} (O : Offsets q s)
    (G : SimpleGraph (Vertex b q m)) [DecidableRel G.Adj] (H : IsBlockGraph O G)
    (P : PortLocal.Program Unit Bool) (ids : Vertex b q m → ℕ)
    (j k : Fin b) (x y : Position q m)
    (hx : Full ((P.rounds+1)*s) x) (hy : Full ((P.rounds+1)*s) y)
    (hi : SameBox (s*(P.rounds+1)) (extendIds j ids) (extendIds k ids) (coordinate x) (coordinate y)) :
    P.run (network O G H) ids (fun _=>()) (j,x)=
      P.run (network O G H) ids (fun _=>()) (k,y) := by
  rw [block_run_unit O G H P j ids x hx,block_run_unit O G H P k ids y hy]
  exact lattice_run_unit O P hi
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.block_run
