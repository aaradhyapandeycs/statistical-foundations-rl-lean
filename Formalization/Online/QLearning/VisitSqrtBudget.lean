import Formalization.Online.QLearning.ReciprocalSqrt
import Mathlib.Data.Real.Sqrt

/-! Arbitrary realized visit-sequence square-root budget. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row] [DecidableEq Row]

theorem qLearning_visitCount_mass (rowAt : ℕ → Row) (K : ℕ) :
    (∑ r : Row, onlineVisitCount rowAt K r) = K := by
  classical
  induction K with
  | zero => simp [onlineVisitCount_zero]
  | succ K ih =>
    simp_rw [onlineVisitCount_succ,Finset.sum_add_distrib]
    simp [ih]

theorem qLearning_visitCount_sqrt_sum (rowAt : ℕ → Row) (K : ℕ) :
    (∑ r : Row, Real.sqrt (onlineVisitCount rowAt K r : ℝ)) ≤
      Real.sqrt (Fintype.card Row : ℝ)*Real.sqrt (K:ℝ) := by
  have hp : ∀ r : Row, (0:ℝ) ≤ 1 := fun _ => by norm_num
  have hc : ∀ r : Row, (0:ℝ) ≤ (onlineVisitCount rowAt K r : ℝ) := fun _ => by positivity
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset Row) hp hc
  have hmass : (∑ r : Row, (onlineVisitCount rowAt K r : ℝ)) = K := by
    exact_mod_cast qLearning_visitCount_mass rowAt K
  simpa [hmass] using h

theorem qLearning_visitCost_sqrt_budget (rowAt : ℕ → Row) (K : ℕ)
    (β : ℕ → ℝ) (C : ℝ) (hzero : β 0 = 0) (hC : 0 ≤ C)
    (hnonneg : ∀ n, 0 ≤ β n) (hbound : ∀ n, 0<n → β n ≤ C/Real.sqrt (n:ℝ)) :
    (∑ k ∈ Finset.range K, β (onlineVisitCount rowAt k (rowAt k))) ≤
      2*C*Real.sqrt (Fintype.card Row : ℝ)*Real.sqrt (K:ℝ) := by
  calc
    _ ≤ ∑ r : Row, ∑ n ∈ Finset.Icc 1 (onlineVisitCount rowAt K r), β n :=
      qLearning_visitCost_le_positiveRange rowAt K β hzero hnonneg
    _ ≤ ∑ r : Row, 2*C*Real.sqrt (onlineVisitCount rowAt K r : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        _ ≤ ∑ n ∈ Finset.Icc 1 (onlineVisitCount rowAt K r), C*(1/Real.sqrt (n:ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 := (Finset.mem_Icc.mp hn).1
          simpa only [mul_one_div] using hbound n (by omega)
        _ = C*(∑ n ∈ Finset.Icc 1 (onlineVisitCount rowAt K r), 1/Real.sqrt (n:ℝ)) := by rw [Finset.mul_sum]
        _ ≤ C*(2*Real.sqrt (onlineVisitCount rowAt K r : ℝ)) :=
          mul_le_mul_of_nonneg_left (qLearning_sum_reciprocalSqrt_le _) hC
        _ = _ := by ring
    _ = 2*C*(∑ r : Row, Real.sqrt (onlineVisitCount rowAt K r : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 2*C*(Real.sqrt (Fintype.card Row : ℝ)*Real.sqrt (K:ℝ)) :=
      mul_le_mul_of_nonneg_left (qLearning_visitCount_sqrt_sum rowAt K) (by positivity)
    _ = _ := by ring
end StatisticalRL.OnlineRL
