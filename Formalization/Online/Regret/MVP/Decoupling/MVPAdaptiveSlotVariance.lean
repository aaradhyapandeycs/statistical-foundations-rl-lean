import Formalization.Online.Regret.MVP.Decoupling.MVPAdaptiveVisitSlots
import Formalization.Probability.Variance

/-! pathwise variance budget for all adaptive dyadic slots. No law,
independence, optimizer or concentration event is supplied as an assumption. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [DecidableEq Row]

theorem mvp_allRows_groupVisits [Fintype Row] (rows : ℕ → Row) (K : ℕ)
    (f : Row → Fin K → ℝ) :
    (∑ r : Row, ∑ k : Fin K, if rows k.val = r then f r k else 0) =
      ∑ k : Fin K, f (rows k.val) k := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

variable {State : Type*} [Fintype State]

theorem mvp_visitVariance_slots_le (rows : ℕ → Row) (K : ℕ) (r : Row)
    (V : Fin K → State → ℝ) (p : FiniteDistribution State) :
    (∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
      p.variance (mvp_visitValueLookup rows K r (2*2^j+i) V)) ≤
      ∑ k : Fin K, if rows k.val = r then p.variance (V k) else 0 := by
  have h := mvp_adaptiveVisit_sum_dyadicSlots rows K r V
    (fun _ W => p.variance W)
    (fun _ => p.variance_const 0)
  have h0 := p.variance_nonneg (mvp_visitValueLookup rows K r 0 V)
  have h1 := p.variance_nonneg (mvp_visitValueLookup rows K r 1 V)
  linarith only [h,h0,h1]

/-- Summing over all row/rank slots consumes each realized adaptive value at
most once. Missing visits are zero, so no extra variance is introduced by
padding the final dyadic block beyond K. -/
theorem mvp_allRows_slotVariance_le [Fintype Row] (rows : ℕ → Row) (K : ℕ)
    (V : Fin K → State → ℝ) (p : Row → FiniteDistribution State) :
    (∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
      ∑ r : Row, (p r).variance (mvp_visitValueLookup rows K r (2*2^j+i) V)) ≤
      ∑ k : Fin K, (p (rows k.val)).variance (V k) := by
  classical
  calc
    _ = ∑ j ∈ Finset.range (Nat.log2 K), ∑ r : Row,
        ∑ i ∈ Finset.range (2*2^j),
          (p r).variance (mvp_visitValueLookup rows K r (2*2^j+i) V) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ r : Row, ∑ j ∈ Finset.range (Nat.log2 K),
        ∑ i ∈ Finset.range (2*2^j),
          (p r).variance (mvp_visitValueLookup rows K r (2*2^j+i) V) :=
      Finset.sum_comm
    _ ≤ ∑ r : Row, ∑ k : Fin K, if rows k.val = r then (p r).variance (V k) else 0 :=
      Finset.sum_le_sum (fun r _ => mvp_visitVariance_slots_le rows K r V (p r))
    _ = _ := mvp_allRows_groupVisits rows K (fun r k => (p r).variance (V k))

end StatisticalRL.OnlineRL
