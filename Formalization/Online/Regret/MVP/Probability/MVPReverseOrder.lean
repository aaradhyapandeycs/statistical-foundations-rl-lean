import Formalization.Online.Regret.MVP.Probability.MVPRevealFiltration
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev

/-! A concrete bijective stage-descending reveal order. -/
namespace StatisticalRL.OnlineRL

def mvpReverseStageOrder (H B : ℕ) : Fin (H*B) → Fin H × Fin B :=
  fun j => let p := finProdFinEquiv.symm j; (p.1.rev, p.2)

theorem mvpReverseStageOrder_injective (H B : ℕ) :
    Function.Injective (mvpReverseStageOrder H B) := by
  intro i j hij
  apply finProdFinEquiv.symm.injective
  have hfirst := congrArg Prod.fst hij
  have hsecond := congrArg Prod.snd hij
  apply Prod.ext
  · simpa [mvpReverseStageOrder] using congrArg Fin.rev hfirst
  · simpa [mvpReverseStageOrder] using hsecond

theorem mvpReverseStageOrder_later_first (H B : ℕ) (i j : Fin (H*B))
    (hstage : (mvpReverseStageOrder H B j).1 < (mvpReverseStageOrder H B i).1) :
    i.val < j.val := by
  have hs : (finProdFinEquiv.symm i).1 < (finProdFinEquiv.symm j).1 := by
    simpa [mvpReverseStageOrder] using (Fin.rev_lt_rev.mp hstage)
  have hi := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
  have hj := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)
  change (finProdFinEquiv.symm i).2.val + B * (finProdFinEquiv.symm i).1.val = i.val at hi
  change (finProdFinEquiv.symm j).2.val + B * (finProdFinEquiv.symm j).1.val = j.val at hj
  have hbi := (finProdFinEquiv.symm i).2.isLt
  have hbj := (finProdFinEquiv.symm j).2.isLt
  have hpos : 0 < B := Nat.zero_lt_of_lt hbi
  have hmul : B * ((finProdFinEquiv.symm i).1.val + 1) ≤
      B * (finProdFinEquiv.symm j).1.val := Nat.mul_le_mul_left B (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega
end StatisticalRL.OnlineRL
