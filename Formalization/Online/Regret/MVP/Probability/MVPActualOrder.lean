import Formalization.Online.Regret.MVP.Probability.MVPReverseOrder
import Formalization.Generative.FiniteHorizonGenerativeSampling

/-! Actual expanded coordinates in decreasing-stage order. -/
namespace StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Enumerate all (stage,state,action,sample) coordinates with stages
strictly decreasing; the within-stage order is a fixed finite equivalence. -/
noncomputable def mvpExpandedOrder (H K : ℕ) :
    Fin (H * Fintype.card (State × Action × Fin K)) → SampleIndex State Action H K := by
  classical
  let e := Fintype.equivFin (State × Action × Fin K)
  exact fun j => let p := mvpReverseStageOrder H (Fintype.card (State × Action × Fin K)) j
    let r := e.symm p.2
    ((p.1,r.1,r.2.1),r.2.2)

theorem mvpExpandedOrder_injective (H K : ℕ) :
    Function.Injective (mvpExpandedOrder (State := State) (Action := Action) H K) := by
  classical
  intro i j hij
  apply mvpReverseStageOrder_injective H (Fintype.card (State × Action × Fin K))
  let e := Fintype.equivFin (State × Action × Fin K)
  have hh := congrArg (fun x : SampleIndex State Action H K => x.1.1) hij
  have hr := congrArg (fun x : SampleIndex State Action H K => (x.1.2.1,x.1.2.2,x.2)) hij
  apply Prod.ext
  · simpa [mvpExpandedOrder] using hh
  · apply e.symm.injective
    simpa [mvpExpandedOrder, e] using hr

theorem mvpExpandedOrder_later_first (H K : ℕ)
    (i j : Fin (H * Fintype.card (State × Action × Fin K)))
    (hstage : (mvpExpandedOrder (State := State) (Action := Action) H K j).1.1 <
      (mvpExpandedOrder (State := State) (Action := Action) H K i).1.1) :
    i.val < j.val := by
  apply mvpReverseStageOrder_later_first
  simpa [mvpExpandedOrder] using hstage
end StatisticalRL.FiniteHorizonGenerative
