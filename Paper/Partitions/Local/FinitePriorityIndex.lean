import Paper.Partitions.Local.BoundedBallBridge

/-! Executable canonical priority address from a finite neighbor function.
The mask uses the sorted ORIGINAL ball, independent of current residuals. -/
namespace Paper.FinitePriorityIndex
variable {V : Type} [LinearOrder V]

def mask (N : V → Finset V) (v : V) (k B : ℕ) (S : Finset V) (i : Fin B) : Bool :=
  if hi : i.val < (NeighborBalls.ball N v k).card then
    decide (((NeighborBalls.ball N v k).sort (· ≤ ·))[i.val]'(by rw [Finset.length_sort]; exact hi) ∈ S)
  else false

def leader (S : Finset V) (fallback : V) : V :=
  if h : S.Nonempty then S.min' h else fallback

def index (N : V → Finset V) (Δ k : ℕ) (S : Finset V) (fallback : V) :
    V × (Fin ((Δ + 1) ^ k) → Bool) :=
  (leader S fallback, mask N (leader S fallback) k ((Δ + 1) ^ k) S)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem mask_correct (v : V) (k B : ℕ) (S : Finset V) :
    mask (fun u => G.neighborFinset u) v k B S = LocalPriorityIndex.mask G v k B S := by
  funext i
  unfold LocalPriorityIndex.mask
  simp only [mask, BoundedBallBridge.balls_eq G v k, Finset.orderEmbOfFin_apply, Fin.getElem_fin]
  have hb : @BoundedBall.ball V _ (Classical.decEq V) G _ v k =
      @BoundedBall.ball V _ (inferInstance : DecidableEq V) G _ v k :=
    congrArg (fun d : DecidableEq V => @BoundedBall.ball V _ d G _ v k) (Subsingleton.elim _ _)
  simp only [hb]

theorem leader_correct (k : ℕ) (S : LocalPriorityIndex.Domain G k) (fallback : V) :
    leader S.val fallback = LocalPriorityIndex.leader G k S := by
  rw [leader, dif_pos (LocalPriorityIndex.nonempty G k S)]
  rfl

theorem index_correct (Δ k : ℕ) (S : LocalPriorityIndex.Domain G k) (fallback : V) :
    index (fun u => G.neighborFinset u) Δ k S.val fallback = LocalPriorityIndex.index G Δ k S := by
  unfold index LocalPriorityIndex.index
  rw [leader_correct G k S fallback, mask_correct G]
end Paper.FinitePriorityIndex
